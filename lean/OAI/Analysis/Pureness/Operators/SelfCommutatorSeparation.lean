import OAI.Analysis.Pureness.Operators.SelfCommutatorTrace
import Mathlib.Analysis.LocallyConvex.Separation

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfCommutatorDownCone : Set (selfAdjoint A) :=
  {x | ∃ m ∈ selfCommutatorSpace (A := A), (x : A) ≤ (m : A)}

omit [StarOrderedRing A] in
lemma selfCommutatorDownCone_zero : (0 : selfAdjoint A) ∈ selfCommutatorDownCone :=
  ⟨0, Submodule.zero_mem _, le_rfl⟩

lemma selfCommutatorDownCone_smul {x : selfAdjoint A}
    (hx : x ∈ selfCommutatorDownCone) {r : ℝ} (hr : 0 ≤ r) :
    r • x ∈ selfCommutatorDownCone := by
  obtain ⟨m, hm, hxm⟩ := hx
  exact ⟨r • m, Submodule.smul_mem _ r hm, smul_le_smul_of_nonneg_left hxm hr⟩

lemma selfCommutatorDownCone_convex : Convex ℝ (selfCommutatorDownCone (A := A)) := by
  rintro x ⟨m, hm, hxm⟩ y ⟨n, hn, hyn⟩ a b ha hb _
  exact ⟨a • m + b • n, Submodule.add_mem _ (Submodule.smul_mem _ a hm)
    (Submodule.smul_mem _ b hn), add_le_add
      (smul_le_smul_of_nonneg_left hxm ha) (smul_le_smul_of_nonneg_left hyn hb)⟩

theorem tracialState_of_one_not_mem_closure
    (h : (1 : selfAdjoint A) ∉ closure (selfCommutatorDownCone (A := A))) :
    Nonempty (TracialState A) := by
  obtain ⟨f, u, hf, hu⟩ := geometric_hahn_banach_closed_point
    selfCommutatorDownCone_convex.closure isClosed_closure h
  have hu0 : 0 < u := by
    simpa using hf 0 (subset_closure selfCommutatorDownCone_zero)
  have hf1 : 0 < f 1 := hu0.trans hu
  have hnonpos (x : selfAdjoint A) (hx : x ∈ selfCommutatorDownCone) : f x ≤ 0 := by
    by_contra! hp
    have hh := hf ((u / f x + 1) • x) (subset_closure
      (selfCommutatorDownCone_smul hx (by positivity)))
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hp.ne'] at hh
    linarith
  have hzero (m : selfAdjoint A) (hm : m ∈ selfCommutatorSpace) : f m = 0 := by
    have hm₁ := hnonpos m ⟨m, hm, le_rfl⟩
    have hm₂ := hnonpos (-m) ⟨-m, Submodule.neg_mem _ hm, le_rfl⟩
    rw [map_neg] at hm₂
    linarith
  have hpos (x : selfAdjoint A) (hx : 0 ≤ (x : A)) : 0 ≤ f x := by
    have hh := hnonpos (-x) ⟨0, Submodule.zero_mem _, neg_nonpos.mpr hx⟩
    simpa only [map_neg, neg_nonpos] using hh
  refine ⟨tracialStateOfReal ((f 1)⁻¹ • f.toLinearMap) ?_ ?_ ?_⟩
  · intro x hx
    exact mul_nonneg (inv_nonneg.mpr hf1.le) (hpos x hx)
  · change (f 1)⁻¹ * f 1 = 1
    exact inv_mul_cancel₀ hf1.ne'
  · intro a
    change (f 1)⁻¹ * f (selfCommutator a) = 0
    rw [hzero _ (selfCommutator_mem a), mul_zero]

theorem exists_selfCommutatorSpace_ge_half
    (h : ¬ Nonempty (TracialState A)) :
    ∃ m ∈ selfCommutatorSpace (A := A), algebraMap ℝ A (1 / 2) ≤ (m : A) := by
  have hc : (1 : selfAdjoint A) ∈ closure (selfCommutatorDownCone (A := A)) := by
    by_contra hn
    exact h (tracialState_of_one_not_mem_closure hn)
  obtain ⟨z, ⟨m, hm, hzm⟩, hz⟩ := Metric.mem_closure_iff.mp hc (1 / 2) (by norm_num)
  have hn : ‖(1 : A) - (z : A)‖ < 1 / 2 := by
    rw [dist_eq_norm] at hz
    exact hz
  have hb : (1 : A) - (z : A) ≤ algebraMap ℝ A (1 / 2) :=
    (((IsSelfAdjoint.one A).sub z.property).le_algebraMap_norm_self).trans
      (by simpa only [Algebra.algebraMap_eq_smul_one] using
        smul_le_smul_of_nonneg_right hn.le (zero_le_one : (0 : A) ≤ 1))
  refine ⟨m, hm, le_trans ?_ hzm⟩
  have heq : (1 : A) - algebraMap ℝ A (1 / 2) = algebraMap ℝ A (1 / 2) := by
    rw [← map_one (algebraMap ℝ A), ← map_sub]
    norm_num
  rw [← heq]
  exact sub_le_comm.mp hb
end CuntzPureness

end

end OAI
