import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveRescaling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedGroupLaws
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialTranslationLimits

namespace OAI

/-! # Fixed group moves disappear in positively weighted word charts -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Topology

/-- The coordinate maps of every fixed right move tend to the identity in
the compact-open topology. This is the part of Cartan scaling needed by
the density sampling argument; it does not require a preconstructed graded
Lie group or any metric scaling premise. -/
theorem rescaled_fixed_translation_tendsto
    {I L G : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℝ L] [Group G]
    (X : I → L) {k c : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ) (hs : ∀ i, 0 < s i)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (t u : ℝ), Exp ((t + u) • x) = Exp (t • x) * Exp (u • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k) β)
      (fun j => bracketWordExponent s (β.val j)) (max r 0)
    Tendsto (fun r : ℝ => (⟨fun x => dynkinProduct a (basisBracket (b r)) x ((b r).equivFun v),
      continuous_dynkinProduct a _ _ _ continuous_const continuous_id continuous_const⟩ :
        C((Fin (finrank ℝ L) → ℝ), (Fin (finrank ℝ L) → ℝ))))
      atTop (𝓝 (ContinuousMap.id _)) := by
  let words := boundedBracketWords (I := I) k
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X words β)
    (fun j => bracketWordExponent s (β.val j)) (max r 0)
  obtain ⟨C, _, hC⟩ := exists_rescaledGroupData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm
  let V := Fin (finrank ℝ L) → ℝ
  let P : Set (V →L[ℝ] V →L[ℝ] V) := Prod.fst '' normalizedGroupParameters a
    (fun j => (β.val j : FreeMagma I)) (fun j => (Pi.single j (1 : ℝ) : V)) C
  have hP : IsCompact P := (isCompact_normalizedGroupParameters a
    (fun j => (β.val j : FreeMagma I))
    (fun j => (Pi.single j (1 : ℝ) : V)) C).image continuous_fst
  have hunit : ∀ B ∈ P, ∀ x, dynkinProduct a B x 0 = x := by
    rintro B ⟨p, hp, rfl⟩ x
    exact hp.2.2.2.1 x
  have hB : ∀ r : ℝ, basisBracket (b r) ∈ P := by
    intro r
    exact ⟨rescaledLieData X words β s (max r 0),
      hC s β hβ (max r 0) (le_max_right _ _), rfl⟩
  have hq : Tendsto (fun r : ℝ => (b r).equivFun v) atTop (𝓝 0) :=
    exponentialRescaleBasis_nonneg_coordinates_tendsto_zero _ _
      (fun j => bracketWordExponent_pos s hs (β.val j)) v
  exact dynkin_translation_maps_tendsto a P hP hunit (fun r => basisBracket (b r)) hB _ hq

end PolycyclicRecognition

end

end OAI
