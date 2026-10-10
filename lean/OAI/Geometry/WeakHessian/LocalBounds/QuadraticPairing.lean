import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.PotentialPairing
import OAI.Geometry.WeakHessian.Sobolev.QuadraticGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile31
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma CurvatureDimension.quadratic_potential_pairing_tendsto {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (hq : QuadraticCheegerEnergy m) (o : X) (R : ℝ≥0)
    {T : ℝ≥0} (hTpos : 0 < T)
    {φs : ℕ → X → ℝ} {φ g : X → ℝ}
    (hφs : ∀ n, QuadraticLipschitzBound o T (φs n)) (hφ : QuadraticLipschitzBound o T φ)
    {B : ℝ} (_ : 0 ≤ B) (hb : ∀ n, |φs n o| ≤ B) (hbφ : |φ o| ≤ B)
    (hT : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hg : Sobolev m g) (hgs : ∀ᵐ x ∂m, x ∉ Metric.closedBall o R → g x = 0) :
    Tendsto (fun n => ∫ x,gamma m (φs n) g x ∂m) atTop (𝓝 (∫ x,gamma m φ g x ∂m)) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin (Metric.ball x 1) Metric.isBounded_ball⟩⟩
  let Q := Metric.closedBall o ((R:ℝ)+2)
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  let L : ℝ≥0 := T+(R+2)
  obtain ⟨k,hk⟩ := exists_nat_ge (B+(L:ℝ)*(R:ℝ))
  let χ := rootCutoff o R
  let loc (v : X → ℝ) (x : X) := realClip k (v x)*χ x
  let C : ℝ≥0 := L*‖(1:ℝ)‖₊+‖(k:ℝ)‖₊*1
  have hχB (x : X) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (rootCutoff_nonneg o R x)]
    exact rootCutoff_le_one o R x
  have hlocal (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) : LipschitzOnWith L v Q := by
    have H := hv.lipschitzOn_ball T.coe_nonneg o (R+2)
    have hL : NNReal.mk (dist o o+(T:ℝ)+((R+2:ℝ≥0):ℝ)) (by positivity) = L := by
      apply NNReal.eq
      simp [L]
    rw [hL] at H
    simpa only [Q,NNReal.coe_add,NNReal.coe_ofNat] using H
  have hlip (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) : LipschitzWith C (loc v) := by
    obtain ⟨v',hv',hev'⟩ := (hlocal v hv).extend_real
    have hcl : LipschitzWith L (fun x => realClip k (v' x)) := by
      simpa only [one_mul,Function.comp_def] using (realClip_lipschitz k).comp hv'
    have H := lipschitz_mul_bounded hcl (rootCutoff_lipschitz o R) (fun x => realClip_abs_le k (v' x)) hχB
    have heq : loc v = (fun x => realClip k (v' x)*rootCutoff o R x) := by
      funext x
      by_cases hx : x ∈ Q
      · simp only [loc,χ,hev' hx]
      · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (rootCutoff_support o R hh))
        change realClip k (v x)*χ x = realClip k (v' x)*χ x
        rw [hz,mul_zero,mul_zero]
    rw [heq]
    exact H
  have hs (v : X → ℝ) : tsupport (loc v) ⊆ Q :=
    tsupport_mul_subset_right.trans (rootCutoff_support o R)
  have hc (v : X → ℝ) : HasCompactSupport (loc v) :=
    isCompact_closedBall o ((R:ℝ)+2) |>.of_isClosed_subset (isClosed_tsupport _) (hs v)
  have hS (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) : Sobolev m (loc v) :=
    sobolev_of_lipschitz_compactSupport hfin (hlip v hv) (hc v)
  have he (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) (hbv : |v o| ≤ B)
      (x : X) (hx : x ∈ Metric.closedBall o R) : loc v x = v x := by
    have hdist : dist x o ≤ R := hx
    have H : |v x| ≤ (k:ℝ) := by
      have ha : |v x| ≤ |v o|+|v x-v o| := by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using norm_le_norm_add_norm_sub (v o) (v x)
      have hbnd := (hlocal v hv).dist_le_mul x (show x ∈ Q from le_trans hdist (by linarith)) o (by change dist o o ≤ (R:ℝ)+2; rw [dist_self]; positivity)
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
    · simp only [loc,d,indicator_of_mem hx,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      exact (mul_le_mul (realClip_abs_le k (v x)) (hχB x) (abs_nonneg _) (Nat.cast_nonneg k)).trans_eq (mul_one _)
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs v h)),norm_zero]
      exact norm_nonneg _
  have hLT : Tendsto (fun n => (hS (φs n) (hφs n)).1.toLp (loc (φs n))) atTop
      (𝓝 ((hS φ hφ).1.toLp (loc φ))) := by
    apply toLp_tendsto_of_domination (fun n => (hS (φs n) (hφs n)).1) (hS φ hφ).1 hd
      (fun n => hdom (φs n))
    exact ae_of_all _ fun x => ((realClip_lipschitz k).continuous.tendsto (φ x) |>.comp (hT x)).mul_const (χ x)
  let D := Q.indicator (fun _ : X => (C:ℝ))
  have hD : MemLp D 2 m := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (memLp_const _)
  have hbD (n : ℕ) : ‖(hS (φs n) (hφs n)).2.2.toLp (weakGradient m (loc (φs n)))‖ ≤ ‖hD.toLp D‖ :=
    norm_gradient_le_supported_lipschitz hfin (hS (φs n) (hφs n)) (hlip _ (hφs n))
      measurableSet_closedBall (hs _) hD
  have H := hcd.integral_gamma_tendsto hfin hq o (fun n => hS _ (hφs n)) (hS φ hφ) hg hLT (norm_nonneg _) hbD
  have hpar := hcd.global_localGradientParallelogram hfin o hq
  have hp (v : X → ℝ) (hv : QuadraticLipschitzBound o T v) (hbv : |v o| ≤ B) :
      (∫ x,gamma m (loc v) g x ∂m) = ∫ x,gamma m v g x ∂m :=
    integral_gamma_localization hfin hpar (hS v hv).2.1 (hv.localSobolev hfin hTpos) hg.2.1
      measurableSet_closedBall (he v hv hbv) hgs
  simpa only [hp φ hφ hbφ,hp _ (hφs _) (hb _)] using H
end WeakHessian

end
end InlinedFile31

end OAI
