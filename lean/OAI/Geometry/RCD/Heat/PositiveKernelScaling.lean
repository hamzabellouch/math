import OAI.Geometry.RCD.Heat.KernelLogMarginals
import OAI.Geometry.RCD.Heat.ContinuousKernelMarginalMass

namespace OAI

/-! # Scaling positive continuous kernels to prescribed endpoint laws

For compact endpoint spaces and probability laws, the two positive
continuous factors satisfy both marginal equations exactly. This is
the compact-support scaling step in Gigli--Tamanini, JEMS 23 (2021),
Theorem 2.2. Only its existence conclusion is needed here.
-/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem positive_kernel_scaling (K : C(X × Y, ℝ)) {m M : ℝ}
    (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y)) (hM : ∀ x y, K (x,y) ≤ M)
    (x₀ : X) (y₀ : Y) :
    ∃ (F : C(X, ℝ)) (G : C(Y, ℝ)),
      (∀ x, 0 < F x) ∧ (∀ y, 0 < G y) ∧
      (∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=1) ∧
      (∀ y, G y*(∫ x, K (x,y)*F x ∂μ)=1) := by
  obtain ⟨f,g,c,hf,hg⟩ := positive_kernel_log_marginals μ ν K hm hK hM x₀ y₀
  let F : C(X, ℝ) := ⟨fun x => Real.exp (f x),Real.continuous_exp.comp f.continuous⟩
  let G : C(Y, ℝ) := ⟨fun y => Real.exp (g y),Real.continuous_exp.comp g.continuous⟩
  have hrow : ∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=Real.exp c := by
    intro x
    change Real.exp (f x)*(∫ y, K (x,y)*Real.exp (g y) ∂ν)=Real.exp c
    rw [← Real.exp_log (continuous_kernel_exp_integral_pos ν K g hm hK x),← Real.exp_add]
    exact congrArg Real.exp (hf x)
  have hcol : ∀ y, G y*(∫ x, K (x,y)*F x ∂μ)=1 := by
    intro y
    change Real.exp (g y)*(∫ x, (transposeContinuousKernel K) (y,x)*Real.exp (f x) ∂μ)=1
    rw [← Real.exp_log (continuous_kernel_exp_integral_pos μ (transposeContinuousKernel K)
      f hm (fun y x => hK x y) y),← Real.exp_add]
    exact (congrArg Real.exp (hg y)).trans Real.exp_zero
  have hc := continuous_kernel_constant_marginal μ ν K F G hrow hcol
  exact ⟨F,G,fun x => Real.exp_pos (f x),fun y => Real.exp_pos (g y),
    fun x => (hrow x).trans hc,hcol⟩

theorem continuous_positive_kernel_scaling (K : C(X × Y, ℝ))
    (hK : ∀ x y, 0 < K (x,y)) (x₀ : X) (y₀ : Y) :
    ∃ (F : C(X, ℝ)) (G : C(Y, ℝ)),
      (∀ x, 0 < F x) ∧ (∀ y, 0 < G y) ∧
      (∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=1) ∧
      (∀ y, G y*(∫ x, K (x,y)*F x ∂μ)=1) := by
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMinOn ⟨(x₀,y₀),mem_univ _⟩ K.continuous.continuousOn
  exact positive_kernel_scaling μ ν K (hK p.1 p.2) (fun x y => hp (mem_univ (x,y)))
    (M := ‖K‖) (fun x y => (le_abs_self (K (x,y))).trans (K.norm_coe_le_norm (x,y))) x₀ y₀

end RegularPointCoordinates

end

end OAI
