import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.Barycenter

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma integral_density_nonnegative {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] (μ : Measure X) {ρ : X → ℝ}
    (hm : AEStronglyMeasurable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) (f : X → ℝ) :
    (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (ρ x))) = ∫ x, ρ x*f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul]

lemma density_real_univ {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) {ρ : X → ℝ}
    (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) :
    (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).real univ = ∫ x, ρ x ∂μ := by
  rw [measureReal_def,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi hρ,ENNReal.toReal_ofReal (integral_nonneg_of_ae hρ)]

lemma density_finite {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) {ρ : X → ℝ}
    (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi hρ]
  exact ENNReal.ofReal_lt_top

lemma weighted_double_distance_lower (hX : IsCAT0 X) (μ : Measure X) {ρ : X → ℝ}
    (hi : Integrable ρ μ) (hρ : 0 ≤ᵐ[μ] ρ) {W : ℝ}
    (hall : ∀ y, W^2 ≤ (∫ x, ρ x ∂μ)*(∫ x, dist y x^2*ρ x ∂μ)) :
    2*W^2 ≤ ∫ y, (∫ x, dist y x^2*ρ x ∂μ)*ρ y ∂μ := by
  let η := μ.withDensity (fun x => ENNReal.ofReal (ρ x))
  let : IsFiniteMeasure η := density_finite μ hi hρ
  have hpot (y : X) : squaredPotential η y = ∫ x, dist y x^2*ρ x ∂μ := by
    rw [squaredPotential,integral_density_nonnegative μ hi.aestronglyMeasurable hρ]
    simp_rw [mul_comm (ρ _) (dist _ _^2)]
  have h := double_distance_lower_bound hX η (W := W) (fun y => by
    rw [show η.real univ = ∫ x, ρ x ∂μ from density_real_univ μ hi hρ,hpot]
    exact hall y)
  rw [integral_density_nonnegative μ hi.aestronglyMeasurable hρ] at h
  simpa only [hpot,mul_comm] using h
end CAT0Fillings
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (μ : Measure X) {U : X → ℝ}
lemma chord_weight_identity {β : ℝ} (hb : 0 < β) {u v r : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v^(2+4*β)*(u^β*r*v^β)^2 = u^(2*β)*(r^2*v^(2+6*β)) := by
  rw [mul_pow,mul_pow,←Real.rpow_mul_natCast hu,←Real.rpow_mul_natCast hv,Nat.cast_ofNat]
  rw [show (2+6*β:ℝ) = (2+4*β)+β*2 by ring,
    Real.rpow_add' hv (by linarith : 2+4*β+β*2 ≠ 0),show β*2=2*β by ring]
  ring

lemma chord_moment_identity {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (μ : Measure X) {U : X → ℝ}
    (hU : AEStronglyMeasurable U μ) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hW : 0 < total μ (fun x => U x^(2+4*β))) (y : X) :
    (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β))) =
    U y^(2*β)*(∫ x, dist y x^2*U x^(2+6*β) ∂μ)/total μ (fun x => U x^(2+4*β)) := by
  rw [integral_probability μ _ (hU.aemeasurable.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW]
  simp_rw [chord_weight_identity hb (hU0 y) (hU0 _)]
  rw [integral_const_mul]

lemma chord_double_identity (hU : AEStronglyMeasurable U μ) (hU0 : ∀ x, 0 ≤ U x)
    {β : ℝ} (hb : 0 < β) (hW : 0 < total μ (fun x => U x^(2+4*β))) :
    (∫ y, (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β)))
      ∂probability μ (fun x => U x^(2+4*β))) =
    (∫ y, (∫ x, dist y x^2*U x^(2+6*β) ∂μ)*U y^(2+6*β) ∂μ)/
      (total μ (fun x => U x^(2+4*β)))^2 := by
  simp_rw [chord_moment_identity μ hU hU0 hb hW]
  rw [integral_probability μ _ (hU.aemeasurable.pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW]
  have he (y : X) : U y^(2+4*β)*(U y^(2*β)*(∫ x, dist y x^2*U x^(2+6*β) ∂μ)/
      total μ (fun x => U x^(2+4*β))) =
      ((∫ x, dist y x^2*U x^(2+6*β) ∂μ)*U y^(2+6*β))/total μ (fun x => U x^(2+4*β)) := by
    rw [show (2+6*β:ℝ) = (2+4*β)+2*β by ring,
      Real.rpow_add' (hU0 y) (by linarith : 2+4*β+2*β ≠ 0)]
    ring
  simp_rw [he]
  rw [integral_div]
  ring

lemma opposite_average (hX : IsCAT0 X) (hU : AEStronglyMeasurable U μ)
    (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 < β)
    (hi : Integrable (fun x => U x^(2+6*β)) μ)
    (hW : 0 < total μ (fun x => U x^(2+4*β)))
    (hall : ∀ y, (total μ (fun x => U x^(2+4*β)))^2 ≤
      (∫ x, U x^(2+6*β) ∂μ)*(∫ x, dist y x^2*U x^(2+6*β) ∂μ)) :
    2 ≤ ∫ y, (∫ x, (U y^β*dist y x*U x^β)^2 ∂probability μ (fun x => U x^(2+4*β)))
      ∂probability μ (fun x => U x^(2+4*β)) := by
  rw [chord_double_identity μ hU hU0 hb hW]
  apply (le_div_iff₀ (sq_pos_of_pos hW)).mpr
  exact weighted_double_distance_lower hX μ hi
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hall
end CAT0Fillings.ChordMeasure
end

end OAI
