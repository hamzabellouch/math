import OAI.Geometry.RCD.Sobolev.PoissonEnergyError
import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure

namespace OAI

/-!
# Full shifted Bochner mass of a Poisson replacement

The cutoff calculation keeps both the positive source measure and the full
shifted Bochner measure. Its only error is the energy-density error already
controlled by the linear positive-source bound.
-/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- Testing the shifted Bochner measure and the squared-distance Laplacian
with the same cutoff bounds the full mass where the cutoff is one. -/
theorem poisson_bochner_mass_le (f : SobolevSpace μ hQ)
    (β σ : Measure X) [IsFiniteMeasure β] [IsFiniteMeasure σ]
    (χ : X →ᵇ ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (s S : Set X) (hs : MeasurableSet s)
    (hχone : ∀ x ∈ s, χ x = 1)
    (Q dχ : X → ℝ) (hQi : IntegrableOn Q S μ)
    (hdχ : AEStronglyMeasurable dχ (μ.restrict S))
    {D E κ a n : ℝ} (hD : 0 ≤ D) (hκ : 0 ≤ κ) (hna : n ≤ a)
    (hdχbound : ∀ᵐ x ∂μ.restrict S, |dχ x| ≤ D)
    (herror : (∫ x in S, |(1 / 2 : ℝ) * localGamma μ hQ f f x - Q x| ∂μ) ≤ E)
    (hsource : (∫ x, χ x ∂β) =
      (1 / 2 : ℝ) * (∫ x in S, localGamma μ hQ f f x * dχ x ∂μ) +
      κ * (∫ x in S, χ x * localGamma μ hQ f f x ∂μ) -
      (2 * a - n) * ∫ x in S, χ x ∂μ)
    (hQsource : (∫ x in S, Q x * dχ x ∂μ) =
      a * (∫ x in S, χ x ∂μ) - ∫ x, χ x ∂σ) :
    β.real s ≤ D * E + κ * ∫ x in S, localGamma μ hQ f f x ∂μ := by
  let g := localGamma μ hQ f f
  let e := fun x => (1 / 2 : ℝ) * g x - Q x
  have hgi : IntegrableOn g S μ := (localGamma_memL1 μ hQ f f).integrableOn
  have hei : IntegrableOn e S μ := (hgi.const_mul (1 / 2 : ℝ)).sub hQi
  have hdχnorm : ∀ᵐ x ∂μ.restrict S, ‖dχ x‖ ≤ D := by
    simpa only [Real.norm_eq_abs] using hdχbound
  have hgd : IntegrableOn (fun x => g x * dχ x) S μ := by
    exact (hgi.bdd_mul hdχ hdχnorm).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hQd : IntegrableOn (fun x => Q x * dχ x) S μ := by
    exact (hQi.bdd_mul hdχ hdχnorm).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hsplit : (∫ x in S, e x * dχ x ∂μ) =
      (1 / 2 : ℝ) * (∫ x in S, g x * dχ x ∂μ) - ∫ x in S, Q x * dχ x ∂μ := by
    dsimp only [e]
    simp only [sub_mul, mul_assoc]
    rw [integral_sub (hgd.const_mul (1 / 2 : ℝ)) hQd, integral_const_mul]
  have herrorweighted : |∫ x in S, e x * dχ x ∂μ| ≤ D * E := by
    have hb := norm_integral_le_of_norm_le (hei.abs.const_mul D) (show
        ∀ᵐ x ∂μ.restrict S, ‖e x * dχ x‖ ≤ D * |e x| from by
      filter_upwards [hdχbound] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg (e x)])
    rw [integral_const_mul, Real.norm_eq_abs] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left herror hD)
  have hχi (ν : Measure X) [IsFiniteMeasure ν] : Integrable χ ν :=
    Integrable.of_bound χ.continuous.aestronglyMeasurable ‖χ‖
      (Filter.Eventually.of_forall χ.norm_coe_le_norm)
  have hmass : β.real s ≤ ∫ x, χ x ∂β := by
    have hb : s.indicator (fun _ => (1 : ℝ)) ≤ᵐ[β] χ := by
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx, hχone x hx]
      · simpa only [indicator_of_notMem hx] using (hχ x).1
    have hi := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hs) (hχi β) hb
    simpa only [integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one] using hi
  have hσpos : 0 ≤ ∫ x, χ x ∂σ := integral_nonneg fun x => (hχ x).1
  have hχpos : 0 ≤ ∫ x in S, χ x ∂μ := integral_nonneg fun x => (hχ x).1
  have hχg : (∫ x in S, χ x * g x ∂μ) ≤ ∫ x in S, g x ∂μ := by
    apply integral_mono_ae (hgi.bdd_mul χ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall χ.norm_coe_le_norm)) hgi
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ f)] with x hx
    dsimp only [g]
    rw [hx]
    exact mul_le_of_le_one_left (sq_nonneg _) (hχ x).2
  have hident : (∫ x, χ x ∂β) = (∫ x in S, e x * dχ x ∂μ) +
      κ * (∫ x in S, χ x * g x ∂μ) +
      (n - a) * (∫ x in S, χ x ∂μ) - ∫ x, χ x ∂σ := by
    rw [hsplit, hQsource, hsource]
    dsimp only [g]
    ring
  have hcurv := mul_le_mul_of_nonneg_left hχg hκ
  have hnegative : (n - a) * (∫ x in S, χ x ∂μ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hna) hχpos
  have heupper := (le_abs_self (∫ x in S, e x * dχ x ∂μ)).trans herrorweighted
  rw [hident] at hmass
  dsimp only [g] at hcurv
  linarith

end RegularPointCoordinates

end

end OAI
