import OAI.Geometry.Kahler.BaseDensityInduction

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma halfline_bound_of_tail {f : ℝ → ℝ} (hf : Continuous f) {E : ℝ}
    (htail : ∀ y, E ≤ y → f y=0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, 0 ≤ y → |f y| ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc 0 E))
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro y hy
  by_cases he : y ≤ E
  · have hh : |f y| ≤ C := by simpa only [Real.norm_eq_abs] using hC y ⟨hy,he⟩
    exact hh.trans (le_max_left _ _)
  · rw [htail y (le_of_lt (lt_of_not_ge he)),abs_zero]
    exact le_max_right _ _

lemma deriv_tail_zero {f : ℝ → ℝ} {E : ℝ} (htail : ∀ y, E ≤ y → f y=0)
    {y : ℝ} (hy : E < y) : deriv f y=0 := by
  have he : f =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact htail z (le_of_lt hz)
  rw [he.deriv_eq,deriv_const]

lemma RadialProfiles.bounds {a : ℝ} (p : RadialProfiles a) :
    ∃ B F₁ B₁ : ℝ, 0 ≤ B ∧ 0 ≤ F₁ ∧ 0 ≤ B₁ ∧
      (∀ y, 0 ≤ y → |p.b y| ≤ B) ∧
      (∀ y, 0 ≤ y → |deriv p.f y| ≤ F₁) ∧
      (∀ y, 0 ≤ y → |deriv p.b y| ≤ B₁) := by
  obtain ⟨B,hB,hbv⟩ := halfline_bound_of_tail p.smooth_b.continuous (fun y hy => (p.tail y hy).2)
  obtain ⟨F₁,hF₁,hfv⟩ := halfline_bound_of_tail (p.smooth_f.continuous_deriv (by simp))
    (E := p.cutoff+1) (fun y hy => deriv_tail_zero (fun y hy => (p.tail y hy).1) (by linarith))
  obtain ⟨B₁,hB₁,hbd⟩ := halfline_bound_of_tail (p.smooth_b.continuous_deriv (by simp))
    (E := p.cutoff+1) (fun y hy => deriv_tail_zero (fun y hy => (p.tail y hy).2) (by linarith))
  exact ⟨B,F₁,B₁,hB,hF₁,hB₁,hbv,hfv,hbd⟩

end PinchedHartogs.BaseConstruction

end

end OAI
