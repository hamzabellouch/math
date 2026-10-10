import OAI.Geometry.SurfaceImmersion.Geometry.SardDimensionStep

namespace OAI

/-! The precise one-excess-dimension Sard instances for global double
curves: three to two, then four to three. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem three_two_critical_values_null {f : (Fin 3 → ℝ) → ℝ × ℝ}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply sard_dimension_step (H := Base) (G := ℝ) (by simp [Base]) (by simp) ?_
    (fun _ _ hV hg => scalar_surface_local_critical_values_null hV hg) hf
  simp only [Module.finrank_fin_fun,Module.finrank_prod,Module.finrank_self]
  norm_num only [Nat.cast_add,Nat.cast_one]
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0)) (Or.inl (by simp))]
  norm_num

theorem three_two_local_critical_values_null {f : (Fin 3 → ℝ) → ℝ × ℝ}
    {U : Set (Fin 3 → ℝ)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  local_critical_values_null volume (fun _ hf => three_two_critical_values_null hf) hU hf

theorem pair_chart_critical_values_null {f : (Base × Base) → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) :
    volume (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply sard_dimension_step (H := Fin 3 → ℝ) (G := ℝ × ℝ)
    (by simp [Base]) (by simp [ProjectionTarget]) ?_
    (fun _ _ hV hg => three_two_local_critical_values_null hV hg) hf
  have hE : Module.finrank ℝ (Base × Base) = 4 := by simp [Base]
  have hF : Module.finrank ℝ (ProjectionTarget 3) = 3 := by simp [ProjectionTarget]
  rw [hE,hF]
  rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0)) (Or.inl (by simp))]
  norm_num

theorem pair_chart_local_critical_values_null {f : (Base × Base) → ProjectionTarget 3}
    {U : Set (Base × Base)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  local_critical_values_null volume (fun _ hf => pair_chart_critical_values_null hf) hU hf

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
