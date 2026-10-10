import Mathlib
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogramCheeger
import OAI.Geometry.WeakHessian.LocalBounds.RootApproximation
import OAI.Geometry.WeakHessian.Sobolev.SquareSobolev
import OAI.Geometry.WeakHessian.Sobolev.SobolevPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile19
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [ProperSpace X] in
lemma norm_gradient_le_supported_lipschitz (hfin : FiniteOnBoundedSets m)
    {f : X → ℝ} (hfS : Sobolev m f) {L : ℝ≥0} (hf : LipschitzWith L f)
    {Q : Set X} (hQ : MeasurableSet Q) (hs : tsupport f ⊆ Q)
    (hD : MemLp (Q.indicator (fun _ : X => (L:ℝ))) 2 m) :
    ‖hfS.2.2.toLp (weakGradient m f)‖ ≤ ‖hD.toLp (Q.indicator (fun _ : X => (L:ℝ)))‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hfS.2.2.coeFn_toLp,hD.coeFn_toLp,weakGradient_zero_off_support hfS.2.1,
    weakGradient_le_lipschitz hfin hf,weakGradient_nonneg (m := m) f,
    (ae_restrict_iff' hQ).mp (indicator_ae_eq_restrict (μ := m) (f := fun _ : X => (L:ℝ)) hQ)]
      with x he hd hz hl hn hi
  rw [he,hd,Real.norm_eq_abs,abs_of_nonneg hn]
  by_cases hx : x ∈ Q
  · simpa only [hi hx,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg] using hl
  · rw [hz (fun h => hx (hs h)),indicator_of_notMem hx,norm_zero]

omit [ProperSpace X] in
lemma integral_gamma_localization (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g v : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hv : LocalSobolev m v)
    {Q : Set X} (hQ : MeasurableSet Q) (he : ∀ x ∈ Q, f x = g x)
    (hs : ∀ᵐ x ∂m, x ∉ Q → v x = 0) :
    (∫ x,gamma m f v x ∂m) = ∫ x,gamma m g v x ∂m := by
  apply integral_congr_ae
  filter_upwards [gamma_locality_left hfin hf hg hv hQ (ae_of_all _ he),
    gamma_zero_off_set hfin hpar hv hf hQ hs,gamma_zero_off_set hfin hpar hv hg hQ hs,
    gamma_comm (m := m) f v,gamma_comm (m := m) g v] with x hl hz hy hc hd
  by_cases hx : x ∈ Q
  · exact hl hx
  · rw [hc,hd,hz hx,hy hx]

lemma CurvatureDimension.potential_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) (R : ℝ≥0)
    {φs : ℕ → X → ℝ} {φ g : X → ℝ} {L : ℝ≥0}
    (hφs : ∀ n, LipschitzWith L (φs n)) (hφ : LipschitzWith L φ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hg : Sobolev m g) (hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → g x = 0) :
    Tendsto (fun n => ∫ x,gamma m (φs n) g x ∂m) atTop (𝓝 (∫ x,gamma m φ g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := Metric.closedBall o ((R:ℝ)+2)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  obtain ⟨k,hk⟩ := exists_nat_ge (B+(L:ℝ)*(R:ℝ))
  have hk0 : (0:ℝ) ≤ k := (add_nonneg hB (mul_nonneg L.coe_nonneg R.coe_nonneg)).trans hk
  let χ := rootCutoff o R
  let loc (v : X → ℝ) (x : X) := realClip k (v x)*χ x
  let T : ℝ≥0 := L*‖(1:ℝ)‖₊+‖(k:ℝ)‖₊*1
  have hχB (x : X) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (rootCutoff_nonneg o R x)]
    exact rootCutoff_le_one o R x
  have hlip (v : X → ℝ) (hv : LipschitzWith L v) : LipschitzWith T (loc v) := by
    have hcl : LipschitzWith L (fun x => realClip k (v x)) := by
      simpa only [one_mul,Function.comp_def] using (realClip_lipschitz k).comp hv
    exact lipschitz_mul_bounded hcl (rootCutoff_lipschitz o R) (fun x => realClip_abs_le k (v x)) hχB
  have hs (v : X → ℝ) : tsupport (loc v) ⊆ Q :=
    tsupport_mul_subset_right.trans (rootCutoff_support o R)
  have hc (v : X → ℝ) : HasCompactSupport (loc v) :=
    isCompact_closedBall o ((R:ℝ)+2) |>.of_isClosed_subset (isClosed_tsupport _) (hs v)
  have hS (v : X → ℝ) (hv : LipschitzWith L v) : Sobolev m (loc v) :=
    sobolev_of_lipschitz_compactSupport hfin (hlip v hv) (hc v)
  have he (v : X → ℝ) (hv : LipschitzWith L v) (hbv : |v o| ≤ B)
      (x : X) (hx : x ∈ Metric.closedBall o R) : loc v x = v x := by
    have hdist : dist x o ≤ R := hx
    have H : |v x| ≤ (k:ℝ) := by
      have ha : |v x| ≤ |v o|+|v x-v o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (v o) (v x)
      have hbnd := hv.dist_le_mul x o
      rw [Real.dist_eq] at hbnd
      exact (ha.trans (add_le_add hbv (hbnd.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)))).trans hk
    simp only [loc,χ,rootCutoff_one hx,mul_one,realClip,
      min_eq_left (abs_le.mp H).2,max_eq_right (abs_le.mp H).1]
  let d := Q.indicator (fun _ : X => (k:ℝ))
  have hd : MemLp d 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hdom (v : X → ℝ) : ∀ᵐ x ∂m, ‖loc v x‖ ≤ ‖d x‖ := by
    apply ae_of_all
    intro x
    by_cases hx : x ∈ Q
    · simp only [loc,d,indicator_of_mem hx,norm_mul,Real.norm_eq_abs,abs_of_nonneg hk0]
      exact (mul_le_mul (realClip_abs_le k (v x)) (hχB x) (abs_nonneg _) hk0).trans_eq (mul_one _)
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs v h)),norm_zero]
      exact norm_nonneg _
  have hLT : Tendsto (fun n => (hS (φs n) (hφs n)).1.toLp (loc (φs n))) atTop
      (𝓝 ((hS φ hφ).1.toLp (loc φ))) := by
    apply toLp_tendsto_of_domination (fun n => (hS (φs n) (hφs n)).1) (hS φ hφ).1 hd
      (fun n => hdom (φs n))
    exact ae_of_all _ fun x => ((realClip_lipschitz k).continuous.tendsto (φ x) |>.comp (hT x)).mul_const (χ x)
  let D := Q.indicator (fun _ : X => (T:ℝ))
  have hD : MemLp D 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hbD (n : ℕ) : ‖(hS (φs n) (hφs n)).2.2.toLp (weakGradient m (loc (φs n)))‖ ≤ ‖hD.toLp D‖ :=
    norm_gradient_le_supported_lipschitz hfin (hS (φs n) (hφs n)) (hlip _ (hφs n))
      measurableSet_closedBall (hs _) hD
  have H := hcd.integral_gamma_tendsto hfin hq o (fun n => hS _ (hφs n)) (hS φ hφ) hg hLT (norm_nonneg _) hbD
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hp (v : X → ℝ) (hv : LipschitzWith L v) (hbv : |v o| ≤ B) :
      (∫ x,gamma m (loc v) g x ∂m) = ∫ x,gamma m v g x ∂m :=
    integral_gamma_localization hfin hpar (hS v hv).2.1 (localSobolev_of_lipschitz hfin hv) hg.2.1
      measurableSet_closedBall (he v hv hbv) hgs
  simpa only [hp φ hφ hbφ,hp _ (hφs _) (hb _)] using H
end WeakHessian

end
end InlinedFile19

end OAI
