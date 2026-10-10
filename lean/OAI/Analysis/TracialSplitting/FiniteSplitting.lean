import OAI.Analysis.TracialSplitting.NuclearPacking

namespace OAI

universe uNuclear


section

noncomputable section

open Pureness

namespace CurrentMain

theorem finite_set_central_splitting
    {A D : Type} [CStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D]
    (ι : A →⋆ₐ[ℂ] D) (_hι : Function.Injective ι)
    (hA : IsNuclear.{0, uNuclear} A) (hD : RealRankZero D)
    (hT : Nonempty (TracialState D))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    (K : Finset (unitary A)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : D, IsStarProjection P ∧ ∀ x ∈ K,
      uniformTwoNorm (P * ι (x : A) - ι (x : A) * P) < ε ∧
      uniformHalvingError P (ι (x : A)) < ε := by
  classical
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := hT
  obtain ⟨η,n,hη,hη1,henergy,hbalance⟩ := exists_packing_parameters hε
  obtain ⟨Q,hQ,_⟩ := finite_packing_from_nuclearity hA.small ι hD hT hsmall hη hη1 n K ∅
  refine ⟨Q.left,Q.left_projection,?_⟩
  intro x hx
  constructor
  · apply lt_of_le_of_lt ?_ henergy
    apply ciSup_le
    intro τ
    rw [traceTwoNorm_sub_swap]
    have h := hQ.energy x hx τ
    have hs : traceTwoNorm τ (ι (x : A)*Q.left-Q.left*ι (x : A))^2 ≤ packingEnergy η n :=
      (le_add_of_nonneg_right (sq_nonneg _)).trans h
    exact (Real.le_sqrt (traceTwoNorm_nonneg τ _) (packingEnergy_nonneg hη.le n)).mpr hs
  · apply lt_of_le_of_lt ?_ hbalance
    apply ciSup_le
    intro τ
    exact (Q.halving_le τ (mapUnitary ι x)).trans
      (div_le_div_of_nonneg_right (add_le_add (hQ.remaining τ) (hQ.balance x hx τ)) (by norm_num))

end CurrentMain

end

end

end OAI
