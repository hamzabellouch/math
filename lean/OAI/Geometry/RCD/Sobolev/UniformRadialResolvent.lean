import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # A radial resolvent with only a lower rescaled curvature bound

The resolvent and heat-gradient estimates hold at the chosen time. The volume bound is supplied by CD, including the improved
nonnegative-curvature case. No two-sided bound on curvature is needed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.radial_resolvent_of_volume
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) {R t D : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hD : 0 < D) (hKt : 1/2 ≤ 1+K*t) (hsize : t * D ≤ R^2/1024)
    (hvolume : ∀ x, dist p x ≤ 4*R →
      (hausdorff n X).real (closedBall p (2*R)) ≤
        D * (hausdorff n X).real (closedBall x (R/96))) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    let L : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
    ∃ (u : SobolevSpace μ hX.quadratic) (d : Lp ℝ 2 μ) (v : X → ℝ),
      IsWeakLaplacian μ hX.quadratic u d ∧ (∀ᵐ x ∂μ, |d x| ≤ 2/t) ∧
      LipschitzWith (2*L) v ∧ SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ 1) ∧
      ∀ x, dist p x ≤ 4*R → |v x-radialCutoff p R x| < 1/8 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let hQ := hX.quadratic
  let L : ℝ≥0 := ⟨R⁻¹,inv_nonneg.mpr hR.le⟩
  let f := SobolevSpace.toLp μ hQ (radialSobolevCutoff μ hQ p hR)
  let u := SobolevSpace.resolventAt μ hQ t ht f
  let F := resolventLp μ hQ t ht f
  have hf : radialCutoff p R =ᵐ[μ] f := (radialSobolevCutoff_coe μ hQ p hR).symm
  have hφ := radialCutoff_lipschitz p hR
  have hM (x : X) : |radialCutoff p R x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_bounds p R x).1]
    exact (radialCutoff_bounds p R x).2
  have hMf : ∀ᵐ x ∂μ, |f x| ≤ (1:ℝ≥0) := hf.mono fun x hx => hx ▸ hM x
  have hKt0 : 0 < 1+K*t := by linarith
  obtain ⟨v,hv,he⟩ := hX.resolvent_lipschitz K n hn f hφ hf 1 hM ht hKt0
  have hv' : LipschitzWith (2*L) v := hv.weaken (by
    apply NNReal.coe_le_coe.mp
    change R⁻¹/(1+K*t) ≤ 2*R⁻¹
    apply (div_le_iff₀ hKt0).mpr
    nlinarith [inv_nonneg.mpr hR.le])
  let d := t⁻¹ • (F-f)
  have hFM : ∀ᵐ x ∂μ, |F x| ≤ (1:ℝ≥0) := resolventLp_abs_bound μ hQ t ht f 1 hMf
  refine ⟨u,d,v,SobolevSpace.resolventAt_weak_laplacian μ hQ t ht f,?_,hv',he,hFM,?_⟩
  · filter_upwards [hFM,hMf,Lp.coeFn_smul t⁻¹ (F-f),Lp.coeFn_sub F f] with x hx hfx hd hsub
    rw [hd,Pi.smul_apply,smul_eq_mul,hsub,Pi.sub_apply,abs_mul,abs_of_pos (inv_pos.mpr ht)]
    change t⁻¹*|F x-f x| ≤ 2/t
    have hb : |F x-f x| ≤ 2 := (abs_sub _ _).trans (by norm_num at hx hfx ⊢; linarith)
    calc _ ≤ t⁻¹*2 := mul_le_mul_of_nonneg_left hb (inv_pos.mpr ht).le
      _ = _ := by ring
  · intro x hx
    have hr : 0 < R/96 := by positivity
    have h0 : μ (closedBall x (R/96)) ≠ 0 := ne_of_gt
      ((hX.fullSupport x (R/96) hr).trans_le (measure_mono ball_subset_closedBall))
    have htop : μ (closedBall x (R/96)) ≠ ∞ := (isCompact_closedBall x (R/96)).measure_lt_top.ne
    have hm : 0 < μ.real (closedBall x (R/96)) := ENNReal.toReal_pos h0 htop
    have hvol := hvolume x hx
    have herr := resolventLp_error_energy μ hQ t ht (radialSobolevCutoff μ hQ p hR)
    have hen := radialSobolevCutoff_energy_le μ hQ p hR
    have herror : ‖F-f‖^2 ≤ μ.real (closedBall x (R/96))/1024 := by
      have hR2 : 0 < R^2 := sq_pos_of_pos hR
      have htt : t/R^2 ≤ 1/(1024*D) := by
        apply (div_le_iff₀ hR2).mpr
        rw [show 1 / (1024*D) * R^2 = R^2 / (1024*D) by ring]
        apply (le_div_iff₀ (by positivity : 0 < 1024*D)).mpr
        nlinarith only [hsize]
      have he2 := mul_le_mul_of_nonneg_left hen (show 0 ≤ 2*t by positivity)
      have heq : 2*t*(μ.real (closedBall p (2*R))/(2*R^2)) =
          (t/R^2)*μ.real (closedBall p (2*R)) := by ring
      rw [heq] at he2
      have hprod := mul_le_mul_of_nonneg_right htt (show 0 ≤ μ.real (closedBall p (2*R)) from ENNReal.toReal_nonneg)
      change ‖F-f‖^2 ≤ _ at herr
      have hden : 0 < 1024*D := by positivity
      have hvol' : μ.real (closedBall p (2*R)) / (1024*D) ≤
          μ.real (closedBall x (R/96))/1024 := by
        apply (div_le_iff₀ hden).mpr
        nlinarith only [hvol]
      have hprod' : (t/R^2)*μ.real (closedBall p (2*R)) ≤
          μ.real (closedBall p (2*R))/(1024*D) := by
        simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hprod
      exact herr.trans (he2.trans (hprod'.trans hvol'))
    obtain ⟨a,ha,ha2,hab⟩ := lipschitz_lp_pointwise_error μ hv' hφ he hf.symm x hr.le h0
    have ha2' : a^2 ≤ (1:ℝ)/1024 := by
      apply ha2.trans
      apply (div_le_iff₀ hm).mpr
      nlinarith only [herror]
    have hal : a ≤ (1:ℝ)/32 := by nlinarith
    change |v x-radialCutoff p R x| ≤ (2*R⁻¹+R⁻¹)*(R/96)+a at hab
    have hrad : (2*R⁻¹+R⁻¹)*(R/96) = (1:ℝ)/32 := by field_simp; ring
    rw [hrad] at hab
    linarith


/-- A fixed lower rescaled curvature bound gives a uniform resolvent time
and therefore a uniform bounded-Laplacian approximation of the radial cutoff. -/
theorem NoncollapsedRCD.uniform_radial_resolvent_bounded {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (a : ℝ) (ha : 0 ≤ a) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (p : X) (R : ℝ) (_hR : 0 < R), -a ≤ K*R^2 →
      letI : ProperSpace X := hX.proper K n hn
      letI : SeparableSpace X := hX.separable
      letI : IsLocallyFiniteMeasure (hausdorff n X) :=
        locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
      let μ := hausdorff n X
      let L : ℝ≥0 := ⟨R⁻¹, inv_nonneg.mpr _hR.le⟩
      ∃ (u : SobolevSpace μ hX.quadratic) (d : Lp ℝ 2 μ) (v : X → ℝ),
        IsWeakLaplacian μ hX.quadratic u d ∧
        (∀ᵐ x ∂μ, |d x| ≤ (2048*D)/R^2) ∧
        LipschitzWith (2*L) v ∧ SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v ∧
        (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ 1) ∧
        ∀ x, dist p x ≤ 4*R → |v x-radialCutoff p R x| < 1/8 := by
  obtain ⟨D₀, hD₀, hvolume⟩ := hX.rescaled_ball_volume_factor hn
    (a := 49 * a) (δ := 1/672) (by positivity) (by norm_num) (by norm_num)
  let D := max D₀ (a + 1)
  have hD : 1 ≤ D := hD₀.trans (le_max_left _ _)
  have haD : a + 1 ≤ D := le_max_right _ _
  refine ⟨D, hD, ?_⟩
  intro p R hR hcurv
  dsimp only
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let t := R^2/(1024*D)
  have ht : 0 < t := div_pos (sq_pos_of_pos hR) (by positivity)
  have htime : t*D = R^2/1024 := by dsimp only [t]; field_simp
  have hKt : 1/2 ≤ 1+K*t := by
    have hh : -a/(1024*D) ≤ K*t := by
      dsimp only [t]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hcurv (by positivity)
    have hd : -1/2 ≤ -a/(1024*D) := by
      apply (le_div_iff₀ (by positivity : 0 < 1024*D)).mpr
      nlinarith only [haD, ha]
    linarith only [hh, hd]
  have hv : ∀ x, dist p x ≤ 4*R →
      (hausdorff n X).real (closedBall p (2*R)) ≤
        D * (hausdorff n X).real (closedBall x (R/96)) := by
    intro x hx
    have hc : -(49 * a) ≤ K*(7*R)^2 := by nlinarith only [hcurv]
    have hdx : dist x p ≤ 7*R := by rw [dist_comm]; linarith only [hx, hR]
    have hh := hvolume p (7*R) (by positivity) hc x hdx
    have hs : closedBall p (2*R) ⊆ ball p (7*R) :=
      closedBall_subset_ball (by linarith only [hR])
    have hsmall : (1/672:ℝ)*(7*R) = R/96 := by ring
    rw [hsmall] at hh
    have hh' : (hausdorff n X).real (ball p (7 * R)) ≤
        D * (hausdorff n X).real (ball x (R / 96)) :=
      hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
    exact (measureReal_mono hs (hX.finiteOnBounded _ isBounded_ball).ne).trans
      (hh'.trans (mul_le_mul_of_nonneg_left
        (measureReal_mono ball_subset_closedBall
          (hX.finiteOnBounded _ isBounded_closedBall).ne) hD0.le))
  obtain ⟨u, d, v, hud, hd, rest⟩ := hX.radial_resolvent_of_volume K n hn p hR ht hD0
    hKt htime.le hv
  refine ⟨u, d, v, hud, ?_, rest⟩
  have hbound : 2/t = (2048*D)/R^2 := by dsimp only [t]; field_simp; norm_num
  simpa only [hbound] using hd


/-- A fixed lower rescaled curvature bound gives a uniform resolvent time
and therefore a uniform bounded-Laplacian approximation of the radial cutoff. -/
theorem NoncollapsedRCD.uniform_radial_resolvent {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (p : X) (R : ℝ) (_hR : 0 < R), -1 ≤ K*R^2 →
      letI : ProperSpace X := hX.proper K n hn
      letI : SeparableSpace X := hX.separable
      letI : IsLocallyFiniteMeasure (hausdorff n X) :=
        locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
      let μ := hausdorff n X
      let L : ℝ≥0 := ⟨R⁻¹, inv_nonneg.mpr _hR.le⟩
      ∃ (u : SobolevSpace μ hX.quadratic) (d : Lp ℝ 2 μ) (v : X → ℝ),
        IsWeakLaplacian μ hX.quadratic u d ∧
        (∀ᵐ x ∂μ, |d x| ≤ (2048*D)/R^2) ∧
        LipschitzWith (2*L) v ∧ SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v ∧
        (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic u x| ≤ 1) ∧
        ∀ x, dist p x ≤ 4*R → |v x-radialCutoff p R x| < 1/8 := by
  exact hX.uniform_radial_resolvent_bounded hn 1 (by norm_num)

end RegularPointCoordinates

end

end OAI
