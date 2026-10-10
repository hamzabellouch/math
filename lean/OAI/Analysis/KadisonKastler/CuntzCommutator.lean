import OAI.Analysis.KadisonKastler.CuntzMatrices
import OAI.Analysis.KadisonKastler.CompleteAmplification

namespace OAI

/-! # Scalar commutator bounds amplify along commuting Cuntz families -/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι] [DecidableEq ι]

local instance cuntzCommutatorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance cuntzCommutatorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance cuntzCommutatorSourceOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance cuntzCommutatorSourceStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem CuntzFamily.assemble_commutator (S : CuntzFamily ι H)
    (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (hcomm : ∀ i, Commute h (S.entry i))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) :
    S.assemble (CStarMatrix.mapₗ (innerDerivation h) X) =
      h * S.assemble X - S.assemble X * h := by
  have hstar (i : ι) : h * star (S.entry i) = star (S.entry i) * h := by
    have he := congrArg star (hcomm i).eq
    simpa only [star_mul, hh.star_eq] using he.symm
  have hterm (i j : ι) :
      S.entry i * (h * X i j - X i j * h) * star (S.entry j) =
        h * (S.entry i * X i j * star (S.entry j)) -
          (S.entry i * X i j * star (S.entry j)) * h := by
    calc
      _ = (S.entry i * h) * X i j * star (S.entry j) -
          S.entry i * X i j * (h * star (S.entry j)) := by noncomm_ring
      _ = (h * S.entry i) * X i j * star (S.entry j) -
          S.entry i * X i j * (star (S.entry j) * h) := by rw [← (hcomm i).eq, hstar]
      _ = _ := by noncomm_ring
  calc
    _ = ∑ i, ∑ j, (h * (S.entry i * X i j * star (S.entry j)) -
        (S.entry i * X i j * star (S.entry j)) * h) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    _ = _ := by
      simp only [CuntzFamily.assemble, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]

theorem CuntzFamily.matrix_commutator_le (S : CuntzFamily ι H)
    (M : VonNeumannAlgebra H) (hS : ∀ i, S.entry i ∈ M)
    (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (hcomm : ∀ i, Commute h (S.entry i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (X : CStarMatrix ι ι (Algebra M)) :
    ‖CStarMatrix.mapₗ ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) X‖ ≤
      δ * ‖X‖ := by
  let Y := X.map M.toStarSubalgebra.subtype
  have hY : ‖Y‖ ≤ ‖X‖ :=
    NonUnitalStarAlgHom.norm_apply_le (coefficientMatrixMap M.toStarSubalgebra.subtype) X
  have hentry : ∀ i j, Y i j ∈ M := fun i j => (X i j).property
  have hid : CStarMatrix.mapₗ ((innerDerivation h).comp
      M.toStarSubalgebra.subtype.toLinearMap) X =
      CStarMatrix.mapₗ (innerDerivation h) Y := rfl
  rw [hid, ← S.norm_assemble, S.assemble_commutator h hh hcomm]
  exact (hb _ (S.assemble_mem M hS Y hentry)).trans
    (by rw [S.norm_assemble]; exact mul_le_mul_of_nonneg_left hY hδ)

theorem completelyBounded_commutator_of_commuting_cuntz
    (M : VonNeumannAlgebra H) (h : H →L[ℂ] H) (hh : IsSelfAdjoint h)
    (hfamilies : ∀ n : ℕ, 2 ≤ n → ∃ S : CuntzFamily (Fin n) H,
      (∀ i, S.entry i ∈ M) ∧ (∀ i, Commute h (S.entry i)))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    CompletelyBoundedBy ((innerDerivation h).comp M.toStarSubalgebra.subtype.toLinearMap) δ := by
  apply completelyBoundedBy_of_large_square
  intro n hn X
  obtain ⟨S, hSM, hSh⟩ := hfamilies n hn
  exact S.matrix_commutator_le M hSM h hh hSh hδ hb X

end

end KadisonKastler

end OAI
