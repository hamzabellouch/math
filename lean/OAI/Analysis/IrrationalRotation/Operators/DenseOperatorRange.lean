import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Algebra.Algebra.Spectrum.Basic

namespace OAI

noncomputable section

namespace Invariant233.OperatorRange

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem denseRange_of_adjoint_injective (T : H →L[ℂ] H)
    (hT : Function.Injective (star T : H →L[ℂ] H)) : DenseRange T := by
  change Dense (T.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range]
  exact LinearMap.ker_eq_bot.mpr hT

theorem denseRange_of_selfAdjoint_injective (T : H →L[ℂ] H)
    (hself : IsSelfAdjoint T) (hinj : Function.Injective T) : DenseRange T := by
  apply denseRange_of_adjoint_injective
  simpa only [hself.star_eq] using hinj

theorem unitary_injective (U : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) : Function.Injective U := by
  intro x y hxy
  have h := congrArg (fun z => star U z) hxy
  change (star U * U) x = (star U * U) y at h
  simpa only [(Unitary.mem_iff.mp hU).1, one_apply_eq_self] using h

theorem unitary_surjective (U : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) : Function.Surjective U := by
  intro x
  refine ⟨star U x, ?_⟩
  change (U * star U) x = x
  rw [(Unitary.mem_iff.mp hU).2, one_apply_eq_self]

theorem unitary_mul_selfAdjoint_range (U D : H →L[ℂ] H)
    (hU : U ∈ unitary (H →L[ℂ] H)) (hD : IsSelfAdjoint D)
    (hinj : Function.Injective D) :
    Function.Injective (U * D) ∧ DenseRange (U * D) := by
  constructor
  · exact (unitary_injective U hU).comp hinj
  · exact (unitary_surjective U hU).denseRange.comp
      (denseRange_of_selfAdjoint_injective D hD hinj) U.continuous

theorem not_surjective_of_zero_mem_spectrum (T : H →L[ℂ] H)
    (hinj : Function.Injective T) (hspec : (0 : ℂ) ∈ spectrum ℂ T) :
    ¬ Function.Surjective T := by
  intro hsurj
  exact ((spectrum.zero_mem_iff (R := ℂ)).mp hspec)
    (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩)

omit [CompleteSpace H] in

theorem not_isClosed_range_of_dense_not_surjective (T : H →L[ℂ] H)
    (hdense : DenseRange T) (hnot : ¬ Function.Surjective T) :
    ¬ IsClosed (Set.range T) := by
  intro hclosed
  apply hnot
  have hrange : Set.range T = Set.univ :=
    hclosed.closure_eq.symm.trans hdense.closure_range
  intro x
  have : x ∈ Set.range T := by rw [hrange]; trivial
  exact this

theorem eq_zero_of_eigenvector_of_spectrum_zero (T : H →L[ℂ] H)
    (hinj : Function.Injective T) (hspec : spectrum ℂ T = {0})
    (z : ℂ) (x : H) (heigen : T x = z • x) : x = 0 := by
  by_cases hz : z = 0
  · apply hinj
    simpa only [hz, zero_smul, map_zero] using heigen
  · have hunit : IsUnit (algebraMap ℂ (H →L[ℂ] H) z - T) := by
      apply spectrum.notMem_iff.mp
      rw [hspec]
      simpa only [Set.mem_singleton_iff] using hz
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    simp only [sub_apply, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self, heigen, sub_self, map_zero]

end Invariant233.OperatorRange

end

end OAI
