import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.SpatialHeat

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile117
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma inner_heat_average_bound (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (u w : Lp ℝ 2 m) {t C : ℝ} (ht : 0 < t)
    (hb : ∀ s ∈ Ioc (0:ℝ) t, |⟪cheegerHeat h s u,w⟫_ℝ| ≤ C) :
    |⟪t⁻¹ • (∫ s in 0..t,cheegerHeat h s u),w⟫_ℝ| ≤ C := by
  have hi : IntervalIntegrable (fun s => cheegerHeat h s u) volume 0 t :=
    ((cheegerHeat_continuousOn hfin h u).mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  have he : ⟪(∫ s in 0..t,cheegerHeat h s u),w⟫_ℝ = ∫ s in 0..t,⟪cheegerHeat h s u,w⟫_ℝ := by
    calc
      _ = ⟪w,(∫ s in 0..t,cheegerHeat h s u)⟫_ℝ := real_inner_comm _ _
      _ = ∫ s in 0..t,⟪w,cheegerHeat h s u⟫_ℝ := ((innerSL ℝ w).intervalIntegral_comp_comm hi).symm
      _ = _ := intervalIntegral.integral_congr (fun s _ => real_inner_comm _ _)
  rw [real_inner_smul_left,he,abs_mul,abs_inv,abs_of_pos ht]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => ⟪cheegerHeat h s u,w⟫_ℝ) (C := C) (fun s hs => by
      rw [uIoc_of_le ht.le] at hs
      simpa only [Real.norm_eq_abs] using hb s hs)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos ht] at H
  calc t⁻¹ * |∫ s in 0..t,⟪cheegerHeat h s u,w⟫_ℝ| ≤ t⁻¹*(C*t) := mul_le_mul_of_nonneg_left H (by positivity)
       _ = C := by field_simp

lemma RCD.cheegerHeat_average_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf2 : MemLp f 2 m) {D : ℝ} (hfB : ∀ x,|f x| ≤ D)
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (L*⟨Real.exp (|K| *t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] (t⁻¹ • ∫ s in 0..t,cheegerHeat h s (hf2.toLp f) : Lp ℝ 2 m) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let : IsUnifLocDoublingMeasure m := hrcd.1.uniform_local_doubling hN hfull hfin
  apply exists_lipschitz_of_ball_averages
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let u (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hn (x : X) : ∀ᵐ z ∂m,0 ≤ u x z := setDensity_nonneg _ _ _
  have hmass (x : X) : ∫ z,u x z ∂m = 1 := setDensity_mass _ _ _ (hp x)
  have hb (x : X) : ∀ᵐ z ∂m,|u x z| ≤ (m (Metric.closedBall x r)).toReal⁻¹ := setDensity_bounded _ _ _
  have hs (x : X) : ∀ᵐ z ∂m,r < dist z x → u x z = 0 := setDensity_supported _ _ _ x (Subset.refl _)
  have heq (v : Lp ℝ 2 m) (x : X) : ⟪v,u x⟫_ℝ = (⨍ z in Metric.closedBall x r,v z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  have H := inner_heat_average_bound hfin h (hf2.toLp f) (u x-u y) ht
    (C := (L:ℝ)*Real.exp (|K| *t)*(2*r+dist x y)) (by
      intro s hst
      rw [inner_sub_right]
      have H := hrcd.cheegerHeat_pairing_balls hN hfull hfin h hf hf2 hfB (u x) (u y)
        (hn x) (hn y) (hmass x) (hmass y) (by positivity) (by positivity) (hb x) (hb y) x y hr.le hr.le (hs x) (hs y) hst.1.le
      apply H.trans
      rw [← two_mul r]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right (neg_le_abs K) hst.1.le).trans
        (mul_le_mul_of_nonneg_left hst.2 (abs_nonneg K)))
  rw [inner_sub_right,heq _ x,heq _ y] at H
  exact H
end WeakHessian

end
end InlinedFile117

end OAI
