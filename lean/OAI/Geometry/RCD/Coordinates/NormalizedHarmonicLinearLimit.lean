import OAI.Geometry.RCD.Harmonic.ScaledHarmonicValueConvergence
import OAI.Geometry.RCD.Sobolev.HarmonicLinearEnergyL1
import OAI.Geometry.RCD.Harmonic.MeanGramControl

namespace OAI

/-! # Exact energy normalization fixes the norm of a harmonic linear limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.normalized_harmonic_linear_limit_ne_zero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hcurv5 : ∀ k, -1 ≤ K*(5*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k) ≤ M)
    (hmean : ∀ k, ((hausdorff n X).real (ball (p k) (r k)))⁻¹*
      ∫ x in ball (p k) (r k), r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x
        ∂hausdorff n X = 1)
    (L : Euclidean n →L[ℝ] ℝ)
    (hconv : ∀ W : ℝ, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-L (V k x)| ≤ δ) : L ≠ 0 := by
  intro hzero
  let μ := hausdorff n X
  have hnorm' (k : ℕ) : harmonicTargetNorm hX (p k) (5*r k) ((2 : ℝ) • w k) ≤ 2*M := by
    rw [harmonicTargetNorm_smul]
    simpa only [abs_of_pos (by norm_num : (0:ℝ)<2)] using
      mul_le_mul_of_nonneg_left (hnorm k) (by norm_num : (0:ℝ)≤2)
  have hsharp := hX.harmonic_linear_sharp hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
    (fun k => (2 : ℝ) • w k) (fun k => (hw k).smul μ hX.quadratic 2)
    (mul_pos (by norm_num) hM) hnorm' ((2 : ℝ) • L) (by simp [hzero])
    (sobolev_linear_value_convergence_smul μ hX.quadratic p r V w L (by norm_num) hconv)
    1 (by norm_num)
  obtain ⟨k,hk⟩ := hsharp.exists
  have hs : ball (p k) (r k) ⊆ ball (p k) (3*r k) :=
    ball_subset_ball (by linarith [hr k])
  have hb : ∀ᵐ x ∂μ.restrict (ball (p k) (r k)),
      r k^2*localGamma μ hX.quadratic (w k) (w k) x ≤ 1/2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hk,
      ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic 2 (w k) ((2 : ℝ) • w k)),
      ae_restrict_of_ae (localGamma_smul_right μ hX.quadratic 2 (w k) (w k))] with x hx hl hr'
    change r k^2*localGamma μ hX.quadratic ((2 : ℝ) • w k) ((2 : ℝ) • w k) x ≤ 1+1 at hx
    rw [hl,hr'] at hx
    nlinarith
  have hfin : μ (ball (p k) (r k)) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hm : 0 < μ.real (ball (p k) (r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (hr k)).ne' hfin
  have hi := integral_mono_ae
    ((localGamma_memL1 μ hX.quadratic (w k) (w k)).const_mul (r k^2)).integrableOn
    (integrableOn_const hfin) hb
  rw [setIntegral_const] at hi
  simp only [smul_eq_mul] at hi
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hm.le)
  rw [hmean k] at hh
  have he : (μ.real (ball (p k) (r k)))⁻¹*(μ.real (ball (p k) (r k))*(1/2)) = 1/2 := by
    field_simp
  rw [he] at hh
  norm_num at hh

theorem NoncollapsedRCD.normalized_harmonic_linear_limit_norm {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hcurv5 : ∀ k, -1 ≤ K*(5*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ k, harmonicTargetNorm hX (p k) (5*r k) (w k) ≤ M)
    (hmean : ∀ k, ((hausdorff n X).real (ball (p k) (r k)))⁻¹*
      ∫ x in ball (p k) (r k), r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x
        ∂hausdorff n X = 1)
    (L : Euclidean n →L[ℝ] ℝ)
    (hconv : ∀ W : ℝ, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-L (V k x)| ≤ δ) : ‖L‖ = 1 := by
  let μ := hausdorff n X
  have hL : 0 < ‖L‖ := norm_pos_iff.mpr
    (hX.normalized_harmonic_linear_limit_ne_zero hn p r ε V hr hcurv hcurv5 hε hε1 hεlim
      hV w hw hM hnorm hmean L hconv)
  let c : ℝ := ‖L‖⁻¹
  have hc : 0 < c := inv_pos.mpr hL
  let u := fun k => c • w k
  have hu (k : ℕ) : harmonicTargetNorm hX (p k) (5*r k) (u k) ≤ c*M := by
    rw [harmonicTargetNorm_smul,abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hnorm k) hc.le
  have hunit : ‖c • L‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg hc.le]
    exact inv_mul_cancel₀ hL.ne'
  have he := hX.harmonic_linear_energy_l1 hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
    u (fun k => (hw k).smul μ hX.quadratic c) (mul_pos hc hM) hu (c • L) hunit
    (sobolev_linear_value_convergence_smul μ hX.quadratic p r V w L hc hconv)
  let e := fun k x => |r k^2*localGamma μ hX.quadratic (u k) (u k) x-1|
  have hfin (k : ℕ) : μ (ball (p k) (5*r k)) ≠ ⊤ :=
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hm (k : ℕ) : 0 < μ.real (ball (p k) (5*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne' (hfin k)
  have hmass₁ := measured_ball_mass_tendsto (by norm_num : (0:ℝ)<5) (by norm_num : (0:ℝ)<1)
    (by norm_num) hr hV hfin hm hεlim
  have hmass₂ := measured_ball_mass_tendsto (by norm_num : (0:ℝ)<5) (by norm_num : (0:ℝ)<2)
    (by norm_num) hr hV hfin hm hεlim
  have hv (R : ℝ) (hR : 0 < R) : 0 < volume.real (ball (0 : Euclidean n) R) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' measure_ball_lt_top.ne
  have hmass := hmass₁.div hmass₂ (ne_of_gt (mul_pos (inv_pos.mpr (hv 5 (by norm_num)))
    (hv 2 (by norm_num))))
  have hmass' : Tendsto (fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
      μ.real (ball (p k) (r k))) atTop
      (𝓝 (volume.real (ball (0 : Euclidean n) 1)/volume.real (ball (0 : Euclidean n) 2))) := by
    convert hmass using 1
    · funext k
      dsimp only [Pi.div_apply,μ]
      simp only [one_mul]
      have hm' : (hausdorff n X).real (ball (p k) (r k*5)) ≠ 0 := by
        simpa only [μ,mul_comm] using (hm k).ne'
      field_simp [hm']
    · congr 1
      field_simp [(hv 5 (by norm_num)).ne']
  have hei (k : ℕ) : IntegrableOn (e k) (ball (p k) (2*r k)) μ :=
    (((localGamma_memL1 μ hX.quadratic (u k) (u k)).const_mul (r k^2)).integrableOn.sub
      (integrableOn_const (hX.finiteOnBounded _ isBounded_ball).ne)).abs
  have hinner := normalized_weighted_core_convergence μ
    (fun k => ball (p k) (r k)) (fun k => ball (p k) (2*r k))
    (fun k => (μ.real (ball (p k) (2*r k)))⁻¹)
    (fun k => inv_pos.mpr (ENNReal.toReal_pos
      (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne))
    (fun _ _ => 1) e (fun k => by simpa only [one_mul] using hei k)
    (fun _ => Eventually.of_forall (fun _ => abs_nonneg _))
    (fun _ => Eventually.of_forall (fun _ => zero_le_one))
    (fun k => ball_subset_ball (by linarith [hr k]))
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => rfl)))
    (div_ne_zero (hv 1 (by norm_num)).ne' (hv 2 (by norm_num)).ne') hmass'
    (by simpa only [one_mul] using he)
  have hbound (k : ℕ) : |c^2-1| ≤ (μ.real (ball (p k) (r k)))⁻¹*
      ∫ x in ball (p k) (r k), e k x ∂μ := by
    have hg : ∀ᵐ x ∂μ.restrict (ball (p k) (r k)),
        r k^2*localGamma μ hX.quadratic (u k) (u k) x =
          c^2*(r k^2*localGamma μ hX.quadratic (w k) (w k) x) := by
      filter_upwards [ae_restrict_of_ae (localGamma_smul_left μ hX.quadratic c (w k) (c • w k)),
        ae_restrict_of_ae (localGamma_smul_right μ hX.quadratic c (w k) (w k))] with x hl hr'
      change r k^2*localGamma μ hX.quadratic (c • w k) (c • w k) x = _
      rw [hl,hr']
      ring
    have hmean' : (μ.real (ball (p k) (r k)))⁻¹*
        (∫ x in ball (p k) (r k), r k^2*localGamma μ hX.quadratic (u k) (u k) x ∂μ) = c^2 := by
      rw [integral_congr_ae hg,integral_const_mul]
      calc _ = c^2*((μ.real (ball (p k) (r k)))⁻¹*
          ∫ x in ball (p k) (r k), r k^2*localGamma μ hX.quadratic (w k) (w k) x ∂μ) := by ring
           _ = c^2 := by rw [hmean k,mul_one]
    have hb := abs_average_sub_const_le μ (ball (p k) (r k))
      (hX.fullSupport _ _ (hr k)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
      ((localGamma_memL1 μ hX.quadratic (u k) (u k)).const_mul (r k^2)).integrableOn 1
    rwa [hmean'] at hb
  have hcz : |c^2-1| ≤ 0 := ge_of_tendsto hinner (Eventually.of_forall hbound)
  have hcunit : c = 1 := by nlinarith [abs_nonneg (c^2-1),le_abs_self (c^2-1),neg_le_abs (c^2-1)]
  change ‖L‖⁻¹ = 1 at hcunit
  exact inv_injective (by simpa using hcunit)

end RegularPointCoordinates

end

end OAI
