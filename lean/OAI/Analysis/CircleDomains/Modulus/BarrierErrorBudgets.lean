import OAI.Analysis.CircleDomains.Modulus.ModelSelectedBarrier

namespace OAI

/-! Choose the finite numerical budgets in the order required by the
near-extremal model construction. No analytic conclusion is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_barrier_error_budget {η M₁ M₂ N : ℝ}
    (hη : 0 < η) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN : 0 ≤ N) :
    ∃ t : ℝ, 0 < t ∧ M₁*(t+t)+(M₂*(t+t))*N+4*M₁*t < η/3 := by
  let C := 6*M₁+2*M₂*N+1
  have hC : 0 < C := by dsimp only [C]; positivity
  let t := (η/3)/C
  have ht : 0 < t := div_pos (by positivity) hC
  have he : t*C = η/3 := div_mul_cancel₀ _ hC.ne'
  refine ⟨t,ht,?_⟩
  have he' : M₁*(t+t)+(M₂*(t+t))*N+4*M₁*t = t*C-t := by dsimp only [C]; ring
  rw [he',he]
  linarith

 theorem exists_height_error_scale (C₀ C₁ V : ℝ) {ν b : ℝ}
    (hν : 0 < ν) (hb : 0 < b) :
    ∃ t : ℝ, 0 < t ∧ t < b ∧
      2*C₀^2*(2*t+4*Real.pi*t)+4*C₁^2*(t+t)^2*V < ν^2 := by
  let E := fun t : ℝ => 2*C₀^2*(2*t+4*Real.pi*t)+4*C₁^2*(t+t)^2*V
  have hc : Continuous E := by dsimp only [E]; fun_prop
  have hzero : E 0 < ν^2 := by dsimp only [E]; nlinarith [sq_pos_of_pos hν]
  have ho : IsOpen ({t : ℝ | E t < ν^2} ∩ Iio b) :=
    (isOpen_lt hc continuous_const).inter isOpen_Iio
  have hn := ho.mem_nhds (show (0 : ℝ) ∈ {t : ℝ | E t < ν^2} ∩ Iio b from ⟨hzero,hb⟩)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  have ht : r/2 ∈ ball (0 : ℝ) r := by
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  exact ⟨r/2,half_pos hr,(hsub ht).2,(hsub ht).1⟩

end CircleDomainRigidity

end

end OAI
