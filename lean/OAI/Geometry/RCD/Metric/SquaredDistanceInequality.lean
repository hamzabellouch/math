import OAI.Geometry.RCD.Harmonic.RadialContractionMoments
import OAI.Geometry.RCD.Harmonic.RadialFirstVariation
import OAI.Geometry.RCD.Sobolev.LocalizedGradientPair

namespace OAI

/-! # The squared-distance Laplacian inequality from actual CD contraction

Contract normalized volume in a ball toward its center. The explicit density
bound controls nonnegative test integrals; the uniform radial first variation
identifies their infinitesimal change with the energy pairing.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.squaredDistance_laplacian_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (p : X) {R : ℝ} (hR : 0 < R)
    (g : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) {L : ℝ≥0}
    (hv : LipschitzWith L v) (hs : HasCompactSupport v) (hsupp : tsupport v ⊆ ball p R)
    (hrep : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] v)
    (hv0 : ∀ x, 0 ≤ v x) :
    0 ≤ energyForm (hausdorff n X) hX.quadratic
      (inwardQuadratic (hausdorff n X) hX.quadratic p hR.le) g +
        ((n : ℝ) + κ * R ^ 2) * ∫ x, v x ∂hausdorff n X := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let q := inwardQuadratic μ hX.quadratic p hR.le
  let B := ball p R
  have hB0 : μ B ≠ 0 := (hX.fullSupport p R hR).ne'
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded B isBounded_ball).ne
  let ν : ProbabilityMeasure X := ⟨uniformOn μ B, uniformOn_probability μ B hB0 hBt⟩
  let C₀ := (μ B)⁻¹
  have hC₀ : C₀ ≠ ∞ := ENNReal.inv_ne_top.mpr hB0
  have hb : (ν : Measure X) ≤ C₀ • μ := by
    intro S
    exact mul_le_mul_right (Measure.restrict_le_self (μ := μ) (s := B) S) _
  have hsν : ∀ᵐ x ∂(ν : Measure X), x ∈ ball p R := uniformOn_ae_mem μ B measurableSet_ball
  let D := 3 * R / 2
  have hRD : R < D := by dsimp only [D]; linarith
  let a (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1)) / 2
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have ha1 (k : ℕ) : a k ≤ 1 / 2 := by
    have hh : 1 / ((k : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]
    dsimp only [a]
    linarith
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa only [a, zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  let T (k : ℕ) : Time := ⟨a k, (ha k).le, (ha1 k).trans (by norm_num)⟩
  have hplans (k : ℕ) := hX.exists_compressed_radial_time hn hκ hK ν hC₀ hb p hR hRD
    (hsν.mono fun _ hx => (mem_ball.mp hx).le) (T k) (ha k) (ha1 k)
  choose π hp hi hg hD hc he hr using hplans
  let (k : ℕ) : IsProbabilityMeasure (π k) := hp k
  have hM := radialPathBudget_ne_top K n κ D hC₀
  have hlen (k : ℕ) : ∀ᵐ γ ∂π k, dist (γ 0) (γ 1) ≤ a k * R := by
    have hstart : ∀ᵐ γ ∂π k, γ 0 ∈ ball p R := by
      apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
      rw [hi k]
      exact hsν
    filter_upwards [hr k, hstart] with γ hγ hx
    exact hγ.1.trans_le (mul_le_mul_of_nonneg_left (mem_ball.mp hx).le (ha k).le)
  have heik := (ae_restrict_iff' measurableSet_ball).mp (hX.inwardSobolev_eikonal hn p hR)
  have hmom (k : ℕ) := radial_contraction_moments μ hX.quadratic p hR.le (ha k).le
    ((ha1 k).trans (by norm_num)) heik (ν : Measure X) (uniformOn_absolutelyContinuous μ B)
    hsν (π k) (hi k) (hc k) ((hr k).mono fun _ hγ => ⟨hγ.1, hγ.2.1⟩)
  have hlow {c : ℝ} (hcc : c < -weightedGradientPair μ hX.quadratic (ν : Measure X) q g) :=
    radial_first_variation_eventually_gt μ hX.quadratic π hg hM hc hD (ν : Measure X) hi
      a ha ha0 hR.le hlen q g (fun k => (hmom k).1) (fun k => (hmom k).2) hcc
  let I := ∫ x, v x ∂μ
  have hI : 0 ≤ I := integral_nonneg hv0
  have hvi : Integrable v μ := hv.continuous.integrable_of_hasCompactSupport hs
  have hbound (k : ℕ) :
      (∫ γ, SobolevSpace.toLp μ hX.quadratic g (γ 1) -
        SobolevSpace.toLp μ hX.quadratic g (γ 0) ∂π k) / a k ≤
      C₀.toReal * ((radialContractionDensity n κ D (a k) - 1) / a k) * I := by
    have hrp (s : Time) : ∀ᵐ γ ∂π k, SobolevSpace.toLp μ hX.quadratic g (γ s) = v (γ s) := by
      apply ae_of_ae_map (measurable_path_eval s).aemeasurable (p := fun x =>
        SobolevSpace.toLp μ hX.quadratic g x = v x)
      exact (Measure.absolutelyContinuous_of_le_smul (hc k s)).ae_le hrep
    have hgi (s : Time) : Integrable (fun γ : C(Time, X) => SobolevSpace.toLp μ hX.quadratic g (γ s)) (π k) :=
      (compressionPullback_memLp μ (π k) _ (measurable_path_eval s) hM (hc k s)
        (SobolevSpace.toLp μ hX.quadratic g)).integrable (by norm_num)
    have heval (s : Time) : (∫ γ, SobolevSpace.toLp μ hX.quadratic g (γ s) ∂π k) =
        ∫ x, v x ∂(π k).map (fun γ => γ s) := by
      rw [integral_map (measurable_path_eval s).aemeasurable hv.continuous.measurable.aestronglyMeasurable]
      exact integral_congr_ae (hrp s)
    have hνv : (∫ x, v x ∂(ν : Measure X)) = C₀.toReal * I := by
      change (∫ x, v x ∂uniformOn μ B) = _
      rw [integral_uniformOn_of_support μ hsupp]
      simp only [C₀, ENNReal.toReal_inv, I, B]
    rw [integral_sub (hgi 1) (hgi 0), heval 1, heval 0, hi k, hνv]
    have hcoeff : C₀.toReal = (μ B).toReal⁻¹ := ENNReal.toReal_inv (μ B)
    have hmeasure := integral_mono_measure (he k) (ae_of_all _ hv0)
      (hvi.smul_measure (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top))
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (radialContractionDensity_pos n κ D (by linarith [ha1 k])).le] at hmeasure
    apply (div_le_iff₀ (ha k)).mpr
    rw [hcoeff] at hmeasure ⊢
    have heq : (μ B).toReal⁻¹ * ((radialContractionDensity n κ D (a k) - 1) / a k) * I * a k =
        (μ B).toReal⁻¹ * (radialContractionDensity n κ D (a k) - 1) * I := by
      field_simp [(ha k).ne']
    rw [heq]
    change _ ≤ _ at hmeasure
    dsimp only [I]
    nlinarith
  let J := C₀.toReal * ((n : ℝ) + κ * D ^ 2 / 3) * I
  have hBlim : Tendsto (fun k => C₀.toReal * ((radialContractionDensity n κ D (a k) - 1) / a k) * I)
      atTop (𝓝 J) := by
    have htime : Tendsto a atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
      ⟨ha0, Eventually.of_forall ha⟩
    exact ((radialContractionDensity_secant_tendsto n κ D).comp htime).const_mul C₀.toReal |>.mul_const I
  have hpair : -weightedGradientPair μ hX.quadratic (ν : Measure X) q g ≤ J := by
    by_contra hnot
    obtain ⟨c, hcJ, hcp⟩ := exists_between (lt_of_not_ge hnot)
    obtain ⟨k, hk, hb⟩ := ((hlow hcp).and (hBlim.eventually (Iio_mem_nhds hcJ))).exists
    exact (not_lt_of_ge (hbound k)) (hb.trans hk)
  change -weightedGradientPair μ hX.quadratic (uniformOn μ B) q g ≤ J at hpair
  rw [weightedGradientPair_uniformOn μ hX.quadratic hB0 q g v hsupp hrep] at hpair
  have hcpos : 0 < (μ B).toReal⁻¹ := inv_pos.mpr (ENNReal.toReal_pos hB0 hBt)
  change -((μ B).toReal⁻¹ * energyForm μ hX.quadratic q g) ≤
    C₀.toReal * ((n : ℝ) + κ * D ^ 2 / 3) * I at hpair
  rw [show C₀.toReal = (μ B).toReal⁻¹ from ENNReal.toReal_inv (μ B)] at hpair
  have hcD : κ * D ^ 2 / 3 ≤ κ * R ^ 2 := by
    dsimp only [D]
    nlinarith [mul_nonneg hκ (sq_nonneg R)]
  have hscaled := mul_le_mul_of_nonneg_right hcD hI
  change 0 ≤ energyForm μ hX.quadratic q g + ((n : ℝ) + κ * R ^ 2) * I
  have hdiv := (mul_le_mul_iff_of_pos_left hcpos).mp
    (show (μ B).toReal⁻¹ * (-energyForm μ hX.quadratic q g) ≤
      (μ B).toReal⁻¹ * (((n : ℝ) + κ * D ^ 2 / 3) * I) by nlinarith [hpair])
  linarith

end RegularPointCoordinates

end

end OAI
