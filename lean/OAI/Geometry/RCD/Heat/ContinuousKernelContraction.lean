import OAI.Geometry.RCD.Heat.ContinuousKernelLog
import OAI.Geometry.RCD.Heat.PositiveKernelOscillation
import OAI.Geometry.RCD.Sobolev.ContinuousDifferenceSpace

namespace OAI

/-! # Contraction of continuous positive kernel transforms

The norm is the supremum of pairwise differences. Consequently the
strict contraction factor has no loss from choosing a base point.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure Y) [IsProbabilityMeasure μ]

private theorem kernel_tilt_one (K : C(X × Y, ℝ)) {m : ℝ} (hm : 0 < m)
    (hK : ∀ x y, m ≤ K (x,y)) (f g : C(Y, ℝ)) (x : X) :
    positiveKernelLogTilt μ (fun y => K (x,y)) (fun y => Real.exp (g y))
      (fun y => f y-g y) 1 = continuousKernelLog μ K hm hK f x := by
  change Real.log (∫ y, Real.exp (1*(f y-g y))*(K (x,y)*Real.exp (g y)) ∂μ) =
    Real.log (∫ y, K (x,y)*Real.exp (f y) ∂μ)
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change Real.exp (1*(f y-g y))*(K (x,y)*Real.exp (g y)) = K (x,y)*Real.exp (f y)
  rw [one_mul]
  calc
    _ = K (x,y) * (Real.exp (f y-g y)*Real.exp (g y)) := by ring
    _ = _ := by rw [← Real.exp_add,sub_add_cancel]

private theorem kernel_tilt_zero (K : C(X × Y, ℝ)) {m : ℝ} (hm : 0 < m)
    (hK : ∀ x y, m ≤ K (x,y)) (f g : C(Y, ℝ)) (x : X) :
    positiveKernelLogTilt μ (fun y => K (x,y)) (fun y => Real.exp (g y))
      (fun y => f y-g y) 0 = continuousKernelLog μ K hm hK g x := by
  change Real.log (∫ y, Real.exp (0*(f y-g y))*(K (x,y)*Real.exp (g y)) ∂μ) =
    Real.log (∫ y, K (x,y)*Real.exp (g y) ∂μ)
  simp only [zero_mul,Real.exp_zero,one_mul]

theorem continuousKernelLog_oscillation (K : C(X × Y, ℝ)) {m M a b : ℝ}
    (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y))
    (hM : ∀ x y, K (x,y) ≤ M) (f g : C(Y, ℝ))
    (hab : ∀ y, a ≤ f y-g y ∧ f y-g y ≤ b) (x z : X) :
    |(continuousKernelLog μ K hm hK f x - continuousKernelLog μ K hm hK g x) -
      (continuousKernelLog μ K hm hK f z - continuousKernelLog μ K hm hK g z)| ≤
        (1-m/M)*(b-a) := by
  have h := positiveKernelLogTilt_oscillation μ
    (continuous_exp_integrable μ g)
    (Eventually.of_forall fun y => (Real.exp_pos (g y)).le)
    (continuous_exp_integral_pos μ g)
    (K.continuous.comp (continuous_const.prodMk continuous_id)).measurable
    (K.continuous.comp (continuous_const.prodMk continuous_id)).measurable
    (f.continuous.sub g.continuous).measurable hm
    (fun y => ⟨hK x y,hM x y⟩) (fun y => ⟨hK z y,hM z y⟩)
    (D := ‖f-g‖₊) (fun y => (f-g).norm_coe_le_norm y) (Eventually.of_forall hab)
  change |(positiveKernelLogTilt μ (fun y => K (x,y)) (fun y => Real.exp (g y))
      (fun y => f y-g y) 1 -
    positiveKernelLogTilt μ (fun y => K (z,y)) (fun y => Real.exp (g y))
      (fun y => f y-g y) 1) -
    (positiveKernelLogTilt μ (fun y => K (x,y)) (fun y => Real.exp (g y))
      (fun y => f y-g y) 0 -
    positiveKernelLogTilt μ (fun y => K (z,y)) (fun y => Real.exp (g y))
      (fun y => f y-g y) 0)| ≤ (1-m/M)*(b-a) at h
  rw [kernel_tilt_one μ K hm hK f g x,kernel_tilt_one μ K hm hK f g z,
    kernel_tilt_zero μ K hm hK f g x,kernel_tilt_zero μ K hm hK f g z] at h
  convert h using 1; congr 1; ring

theorem continuousKernelLog_pair_bound [Nonempty Y] (K : C(X × Y, ℝ)) {m M C : ℝ}
    (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y))
    (hM : ∀ x y, K (x,y) ≤ M) (f g : C(Y, ℝ))
    (hfg : ∀ y w, |(f y-g y)-(f w-g w)| ≤ C) (x z : X) :
    |(continuousKernelLog μ K hm hK f x - continuousKernelLog μ K hm hK g x) -
      (continuousKernelLog μ K hm hK f z - continuousKernelLog μ K hm hK g z)| ≤
        (1-m/M)*C := by
  obtain ⟨y,_,hy⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set Y).Nonempty)
    (f.continuous.sub g.continuous).continuousOn
  obtain ⟨w,_,hw⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (univ : Set Y).Nonempty)
    (f.continuous.sub g.continuous).continuousOn
  have hab : ∀ v, f y-g y ≤ f v-g v ∧ f v-g v ≤ f w-g w :=
    fun v => ⟨hy (mem_univ v),hw (mem_univ v)⟩
  have hspan : (f w-g w)-(f y-g y) ≤ C := (le_abs_self _).trans (hfg w y)
  have hmM : m ≤ M := (hK x y).trans (hM x y)
  have hM0 : 0 < M := hm.trans_le hmM
  exact (continuousKernelLog_oscillation μ K hm hK hM f g hab x z).trans
    (mul_le_mul_of_nonneg_left hspan (sub_nonneg.mpr ((div_le_one hM0).mpr hmM)))

end RegularPointCoordinates

end

end OAI
