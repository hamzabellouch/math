import Mathlib
import OAI.Geometry.WeakHessian.Entropy.SobolevFisher
import OAI.Geometry.WeakHessian.LocalBounds.StrongRoots
import OAI.Geometry.WeakHessian.Entropy.EntropyPairingLimits
import OAI.Geometry.WeakHessian.Calculus.DualLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile22
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m]

theorem RCD.compact_sobolev_entropy_subdifferential {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      IsTestPlan m (π:Measure (Curve X)) ∧ BoundedTracks (π:Measure (Curve X)) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      LipschitzWith (2*(R+2)) φ ∧ LipschitzWith (2*(R+2)) ψ ∧
      (∀ x y,φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  have hsw : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R := by rw [← hμ]; exact ae_iff.mpr hsμ
  obtain ⟨vs,hLip,hvb,hvsupp,hvs,hvp,Ds,hDs,hUG,hV,hD⟩ :=
    hrcd.1.normalized_compact_root_approximation hfin hw hwm hB hwn hwB o R (squareDensity_zero_outside hwm hsw)
  let Q : ℝ≥0 := R+2
  let D : ℝ≥0∞ := C+ENNReal.ofReal ((2*B)^2)+1
  have hDt : D ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hCt,ENNReal.ofReal_ne_top⟩,ENNReal.one_ne_top⟩
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hCD : C ≤ D := le_trans le_self_add le_self_add
  have hBD : ENNReal.ofReal ((2*B)^2) ≤ D := le_trans le_add_self le_self_add
  have hBsmall : ENNReal.ofReal (B^2) ≤ D :=
    (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg B])).trans hBD
  have hdμ : (μ:Measure X) ≤ D • m := by
    rw [hμ]; exact dominated_mono_constant (squareDensity_le_of_bound hB hwn hwB) hBsmall
  have hdνD := dominated_mono_constant hdν hCD
  have hsμQ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o Q :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp [Q] : (R:ℝ) ≤ (Q:ℝ))) hx
  have hsνQ : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o Q :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp [Q] : (R:ℝ) ≤ (Q:ℝ))) hx
  let μs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (vs n) (hvp n)
  have hms (n : ℕ) : (μs n:Measure X) = squareDensityMeasure m (vs n) := rfl
  have hds (n : ℕ) : (μs n:Measure X) ≤ D • m := by
    exact dominated_mono_constant (squareDensity_le_of_bound (by positivity : 0 ≤ 2*B)
      (ae_of_all _ fun x => (hvb n x).1) (ae_of_all _ fun x => (hvb n x).2)) hBD
  have hss (n : ℕ) : ∀ᵐ x ∂(μs n:Measure X), x ∈ Metric.closedBall o Q := by
    apply squareDensity_ae_support (vs n).continuous.measurable
    apply ae_of_all
    intro x hx
    have H : x ∉ tsupport (vs n) := fun h => hx (by simpa only [Q,NNReal.coe_add,NNReal.coe_ofNat] using hvsupp n h)
    exact image_eq_zero_of_notMem_tsupport H
  obtain ⟨π,hπ,hb,hgeo,hopt,hE,hchord,hcomp⟩ :=
    hrcd.1.exists_entropy_testPlan hN hfin μ ν o Q (ae_iff.mp hsμQ) (ae_iff.mp hsνQ) hD0 hDt hdμ hdνD
  have hex (n : ℕ) := hrcd.bounded_entropy_subdifferential hN hfin (vs n) (hLip n).choose_spec
    (fun x => (hvb n x).1) (μs n) ν (hms n) o Q (ae_iff.mp (hss n)) (ae_iff.mp hsνQ) hD0 hDt (hds n) hdνD
  choose ps φ ψ hps hbps hgps hops hφ hψ hdual hcontact hent using hex
  let fs (n : ℕ) (x : X) := φ n x-φ n o
  let gs (n : ℕ) (x : X) := ψ n x+φ n o
  have hf (n : ℕ) : LipschitzWith (2*Q) (fs n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [fs,Real.dist_eq,sub_sub_sub_cancel_right] using (hφ n).dist_le_mul x y
  have hg (n : ℕ) : LipschitzWith (2*Q) (gs n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [gs,Real.dist_eq,add_sub_add_right_eq_sub] using (hψ n).dist_le_mul x y
  have hfd (n : ℕ) (x y : X) : fs n x+gs n y ≤ dist x y^2/2 := by
    dsimp [fs,gs]; linarith [hdual n x y]
  have hfc (n : ℕ) : ∀ᵐ γ ∂(ps n:Measure (Curve X)), fs n (γ timeZero)+gs n (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := (hcontact n).mono fun γ hc => by dsimp [fs,gs]; linarith
  have hgb (n : ℕ) : |gs n o| ≤ 2*(2*Q:ℝ≥0)*Q := by
    apply centered_dual_bound (hf n) (hg n) o Q (sub_self _) (hfd n) (hfc n)
    have H0 : ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeZero ∈ Metric.closedBall o Q := by
      apply (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable measurableSet_closedBall).mp
      change ∀ᵐ x ∂interpolation (ps n:Measure (Curve X)) timeZero, x ∈ Metric.closedBall o Q
      rw [(hops n).1.interpolation_endpoints.1]
      exact hss n
    have H1 : ∀ᵐ γ ∂(ps n:Measure (Curve X)), γ timeOne ∈ Metric.closedBall o Q := by
      apply (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable measurableSet_closedBall).mp
      change ∀ᵐ x ∂interpolation (ps n:Measure (Curve X)) timeOne, x ∈ Metric.closedBall o Q
      rw [(hops n).1.interpolation_endpoints.2]
      exact hsνQ
    exact H0.and H1
  obtain ⟨f,g,s,hs,hfL,hgL,hfo,hgo,hfT,hgT,hfg⟩ := exists_dual_subsequence o fs gs hf hg
    (by positivity : 0 ≤ 2*(2*Q:ℝ≥0)*Q) (fun n => by dsimp [fs]; simp only [sub_self,abs_zero]; positivity)
    hgb hfd
  have hcost : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (planEnergy (π:Measure (Curve X)))) := by
    apply optimal_energy_squareDensity_tendsto (fun n => (vs n).continuous.measurable) hwm hvs hw.1 hvp hV o Q hss
      (by rw [← hμ]; exact hsμQ) hsνQ ps π hbps hb (fun n => hops n)
    simpa only [← hμ] using hopt
  have hsμs : Tendsto μs atTop (𝓝 μ) := by
    have H := squareDensity_tendsto_probability (fun n => (vs n).continuous.measurable) hwm hvs hw.1 hvp inferInstance hV
    have he : squareDensityProbability m w inferInstance = μ := by apply Subtype.ext; exact hμ.symm
    rwa [he] at H
  have hIf : Tendsto (fun n => ∫ x,fs (s n) x ∂(μs (s n):Measure X)) atTop (𝓝 (∫ x,f x ∂(μ:Measure X))) := by
    rw [hμ]
    exact squareDensity_varying_pairing_tendsto (fun n => (vs (s n)).continuous.measurable) hwm
      (fun n => hvs (s n)) hw.1 (fun n => hvp (s n)) (hV.comp hs.tendsto_atTop) o Q
      (fun n => hss (s n)) (by rw [← hμ]; exact hsμQ) (fun n => hf (s n))
      (B := 0) (fun n => by simp [fs]) hfT
  have hIg := lipschitz_integral_tendsto_supported o Q hsνQ (fun n => hg (s n))
    (fun n => hgb (s n)) hgT
  have hc : ∀ᵐ γ ∂(π:Measure (Curve X)), f (γ timeZero)+g (γ timeOne) =
      dist (γ timeZero) (γ timeOne)^2/2 := by
    apply contact_of_integral_eq hb hb.integrable_length_sq hfL hgL hfg
    rw [hopt.1.interpolation_endpoints.1,hopt.1.interpolation_endpoints.2]
    apply tendsto_nhds_unique (hIf.add hIg)
    have he (n : ℕ) : (∫ x,fs (s n) x ∂(μs (s n):Measure X))+
        (∫ x,gs (s n) x ∂(ν:Measure X)) = planEnergy (ps (s n):Measure (Curve X))/2 := by
      have H := contact_integral_eq (hbps (s n)) (hf (s n)) (hg (s n)) (hfc (s n))
      rwa [(hops (s n)).1.interpolation_endpoints.1,(hops (s n)).1.interpolation_endpoints.2] at H
    simp_rw [he]
    exact hcost.comp hs.tendsto_atTop |>.div_const 2
  have hS (n : ℕ) : Sobolev m (vs n) := Sobolev.of_upperGradient hfin (hvs n) (hUG n) (hDs n)
  obtain ⟨hsub,hsubT⟩ := hrcd.1.strong_root_approximation hfin hrcd.2 o hw
    (fun n => (vs n:X → ℝ)) Ds hvs hDs hUG hV hD
  obtain ⟨M,hM,hMb⟩ := (Metric.isBounded_range_of_tendsto (fun n => ‖(hDs n).toLp (Ds n)‖) hD.norm).exists_pos_norm_le
  have hgrad (n : ℕ) : ‖(hS n).2.2.toLp (weakGradient m (vs n))‖ ≤ M := by
    have H := sqrt_gradient_energy_le_upper (hS n) (hUG n) (hDs n)
    rw [← norm_toLp_sq_eq_integral (hS n).2.2,Real.sqrt_sq (norm_nonneg _)] at H
    exact H.trans (by simpa only [Real.norm_eq_abs,abs_norm] using hMb _ (mem_range_self n))
  have hpair : Tendsto (fun n => ∫ x,2*vs (s n) x*gamma m (fs (s n)) (vs (s n)) x ∂m) atTop
      (𝓝 (∫ x,2*w x*gamma m f w x ∂m)) := by
    apply hrcd.1.entropy_pairing_tendsto hfin hrcd.2 o R (fun n => hS (s n)) hw
      (hwn.and hwB |>.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2)
      (squareDensity_zero_outside hwm hsw) (hV.comp hs.tendsto_atTop)
      (hsubT.comp hs.tendsto_atTop) (fun n => hgrad (s n)) (fun n => hf (s n)) hfL
      (by positivity : 0 ≤ 2*(2*Q:ℝ≥0)*Q) (fun n => by simp only [fs,sub_self,abs_zero]; exact NNReal.coe_nonneg _) hfo hfT
  have hent' (n : ℕ) : entropyReal m (μs (s n):Measure X) ≤ entropyReal m (ν:Measure X)+
      (∫ x,2*vs (s n) x*gamma m (fs (s n)) (vs (s n)) x ∂m)-K/2*planEnergy (ps (s n):Measure (Curve X)) := by
    have he : (∫ x,2*vs (s n) x*gamma m (fs (s n)) (vs (s n)) x ∂m) =
        ∫ x,2*vs (s n) x*gamma m (φ (s n)) (vs (s n)) x ∂m := by
      apply integral_congr_ae
      have H := gamma_add_const_left hfin (localSobolev_of_lipschitz hfin (hφ (s n))) (hS (s n)).2.1 (-φ (s n) o)
      filter_upwards [H] with x hx
      simp only [fs,sub_eq_add_neg,hx]
    rw [he]
    linarith [hent (s n)]
  have hlim := (tendsto_const_nhds (x := entropyReal m (ν:Measure X))).add hpair |>.sub
    ((hcost.comp hs.tendsto_atTop).const_mul (K/2))
  have H := entropyReal_le_of_tendsto_supported hfin (fun n => μs (s n)) μ
    (hsμs.comp hs.tendsto_atTop) o Q (fun n => hss (s n)) hsμQ hDt (fun n => hds (s n)) hdμ hlim hent'
  exact ⟨π,f,g,hπ,hb,hgeo,hopt,hfL,hgL,hfg,hc,by linarith⟩
end WeakHessian

end
end InlinedFile22

end OAI
