import OAI.Geometry.Kahler.BaseDensityMoments

namespace OAI

universe uKahler13116_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

def densityMeasure (W : Base → ℝ) : Measure Sphere := sigma.withDensity (fun ξ : Sphere => ENNReal.ofReal (W ξ))

lemma densityMeasure_integral {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    {E : Type uKahler13116_1} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Sphere → E) :
    (∫ ξ, g ξ ∂densityMeasure W) = ∫ ξ, W ξ • g ξ ∂sigma := by
  change (∫ ξ, g ξ ∂sigma.withDensity (fun ξ : Sphere => ENNReal.ofReal (W ξ))) = _
  have hm : Measurable (fun ξ : Sphere => ENNReal.ofReal (W ξ)) := (hW.comp continuous_subtype_val).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g]
  simp_rw [ENNReal.toReal_ofReal (hpos _)]

lemma densityMeasure_probability {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    (hmass : (∫ ξ : Sphere, W ξ ∂sigma)=1) : IsProbabilityMeasure (densityMeasure W) := by
  constructor
  have hi : Integrable (fun ξ : Sphere => W ξ) sigma := continuous_integrable (hW.comp continuous_subtype_val)
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hpos),hmass]
  norm_num

lemma densityMeasure_represents {W : Base → ℝ} (hW : Continuous W) (hpos : ∀ ξ : Sphere, 0 ≤ W ξ)
    (hmoment : ∀ p : MvPolynomial (Fin 2) ℂ,
      (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p*(W ξ:ℂ) ∂sigma)=MvPolynomial.eval (fun _ => 0) p) :
    Represents (densityMeasure W) := by
  intro p
  rw [densityMeasure_integral hW hpos]
  simpa only [Complex.real_smul,mul_comm] using hmoment p

lemma density_orbit_mean {Q : ℕ} (hQ : 2 ≤ Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    OrbitMeanOne (density Q R f b P j) := by
  classical
  have hq : 0 < Q := by omega
  induction j with
  | zero => exact orbitMean_one
  | succ j ih =>
    intro ξ
    have hw := density_smooth hq hER hf hb htail P j
    have hi : Integrable (fun z : Circle => density Q R f b P j ((z:ℂ) • (ξ:Base))) circleMeasure := by
      apply compact_continuous_integrable
      exact hw.continuous.comp ((continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).smul continuous_const)
    have hic : ∀ p ∈ P (Q^(j+1)), Integrable (fun z : Circle => densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p ((z:ℂ) • (ξ:Base))) circleMeasure := by
      intro p hp
      apply compact_continuous_integrable
      exact (densityCorrection_smooth (pow_pos hq _) hER hf hb hw htail p).continuous.comp ((continuous_subtype_val : Continuous (fun z : Circle => (z:ℂ))).smul continuous_const)
    simp only [density]
    rw [integral_add hi (integrable_finsetSum _ hic),integral_finsetSum _ hic,ih ξ]
    have hz : (∑ p ∈ P (Q^(j+1)), ∫ z : Circle, densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p ((z:ℂ) • (ξ:Base)) ∂circleMeasure)=0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact densityCorrection_orbit_zero (hw.differentiable (by simp)) (density_bandwidth hq hER hf hb htail P j) (densityBandwidth_lt hQ j) R f b p ξ
    rw [hz,add_zero]

end PinchedHartogs.BaseConstruction

end

end OAI
