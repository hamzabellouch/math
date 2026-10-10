import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.FiniteComparison

namespace OAI

/-! The projection onto the closed span of the initial spaces of a family
of partial isometries. All constructions remain in the original algebra. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def partialSupportVectors (S : Set (PartialIsometry M)) : Set H :=
  {y | ∃ v ∈ S, ∃ ξ, y = (v.support.val : H →L[ℂ] H) ξ}

def partialSupportSpace (S : Set (PartialIsometry M)) : Submodule ℂ H :=
  (Submodule.span ℂ (partialSupportVectors S)).topologicalClosure

instance partialSupportSpace_complete (S : Set (PartialIsometry M)) :
    CompleteSpace (partialSupportSpace S) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (partialSupportVectors S)).topologicalClosure)

theorem partialSupportSpace_le_ker (S : Set (PartialIsometry M))
    (T : H →L[ℂ] H) (hT : ∀ v ∈ S, T.comp (v.support.val : H →L[ℂ] H) = 0) :
    partialSupportSpace S ≤ T.ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro y ⟨v, hv, ξ, rfl⟩
    exact congrArg (fun A : H →L[ℂ] H => A ξ) (hT v hv)
  · exact T.isClosed_ker

theorem partialSupportProjection_mem (S : Set (PartialIsometry M)) :
    (partialSupportSpace S).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection M).mpr
  intro T hT
  rw [Submodule.range_starProjection]
  have hinv : partialSupportSpace S ≤ (partialSupportSpace S).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨v, hv, ξ, rfl⟩
      apply Submodule.le_topologicalClosure
      apply Submodule.subset_span
      refine ⟨v, hv, T ξ, ?_⟩
      have hc := VonNeumannAlgebra.mem_commutant_iff.mp hT v.support.val.val
        v.support.val.property
      exact (congrArg (fun A : H →L[ℂ] H => A ξ) hc).symm
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact fun y hy => hinv hy

def partialSupportProjection (S : Set (PartialIsometry M)) : AlgebraProjection M :=
  ⟨⟨(partialSupportSpace S).starProjection, partialSupportProjection_mem S⟩, by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := partialSupportSpace S)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := partialSupportSpace S)).isSelfAdjoint.star_eq⟩

theorem support_le_partialSupportProjection (S : Set (PartialIsometry M))
    (v : PartialIsometry M) (hv : v ∈ S) : v.support ≤ partialSupportProjection S := by
  apply Subtype.ext
  ext ξ
  apply Submodule.starProjection_eq_self_iff.mpr
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v, hv, ξ, rfl⟩)

theorem partialSupportProjection_le (S : Set (PartialIsometry M))
    (q : AlgebraProjection M) (hq : ∀ v ∈ S, v.support ≤ q) :
    partialSupportProjection S ≤ q := by
  have hk : partialSupportSpace S ≤ ((q.val : H →L[ℂ] H) - 1).ker := by
    apply partialSupportSpace_le_ker
    intro v hv
    ext ξ
    have he := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) ξ) (hq v hv)
    exact sub_eq_zero.mpr he
  apply Subtype.ext
  ext ξ
  exact sub_eq_zero.mp (hk ((partialSupportSpace S).starProjection_apply_mem ξ))

theorem support_le_centralSupport_of_target_le (e : AlgebraProjection M)
    (v : PartialIsometry M) (hv : v.target ≤ e) : v.support ≤ centralSupport e := by
  have ht := hv.trans (le_centralSupport e)
  have hc : (centralSupport e).val * v.val = v.val := by
    calc
      _ = (centralSupport e).val * (v.target.val * v.val) := by rw [v.target_mul]
      _ = v.val := by rw [← mul_assoc, ht, v.target_mul]
  change (centralSupport e).val * v.support.val = v.support.val
  rw [← v.initial, ← mul_assoc, ← centralSupport_commutes e (star v.val), mul_assoc, hc]

end

end KadisonKastler

end OAI
