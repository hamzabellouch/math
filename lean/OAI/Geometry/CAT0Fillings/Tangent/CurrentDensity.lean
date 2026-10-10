import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Chord.NonnegativeMeasure
import OAI.Geometry.CAT0Fillings.Chord.Fubini
import OAI.Geometry.CAT0Fillings.Tangent.Transfer

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
lemma kernel_rescaled (n : ℕ) {u ε β κ r : ℝ} (hu : 0 ≤ u) :
    u^(2*(n:ℝ)*β)/(1+κ^2*(r/ε)^2*u^(2*β))^n =
    u^(2*(n:ℝ)*β)*ChordTransform.kernel n ((κ*r*u^β)^2) ((ε^2)⁻¹) := by
  have hp : (u^β)^2 = u^(2*β) := by
    rw [←Real.rpow_mul_natCast hu]; congr 1; ring
  have he : 1+κ^2*(r/ε)^2*u^(2*β) = 1+(ε^2)⁻¹*(κ*r*u^β)^2 := by
    simp only [mul_pow,hp,div_eq_mul_inv]
    ring
  rw [he]
  simp [ChordTransform.kernel,Real.rpow_neg_natCast,_root_.zpow_neg,zpow_natCast,div_eq_mul_inv]

lemma rescaled_transform_identity (μ : Measure X) (U : X → ℝ) (hU : Measurable U)
    (hU0 : ∀ x, 0 ≤ U x) (n : ℕ) (β κ ε : ℝ) (o : X)
    (hi : Integrable (fun x => U x^(2*(n:ℝ)*β)) μ)
    (hW : 0 < ChordMeasure.total μ (fun x => U x^(2*(n:ℝ)*β))) :
    let ρ := fun x => U x^(2*(n:ℝ)*β)
    let ν := ChordMeasure.probability μ ρ
    (∫⁻ x, ENNReal.ofReal (U x^(2*(n:ℝ)*β)/
      (1+κ^2*(dist x o/ε)^2*U x^(2*β))^n) ∂μ) =
    ENNReal.ofReal (ChordMeasure.total μ ρ *
      ChordTransform.transform ν n (fun x => (κ*dist o x*U x^β)^2) ((ε^2)⁻¹)) := by
  let ρ := fun x => U x^(2*(n:ℝ)*β)
  let ν := ChordMeasure.probability μ ρ
  let b := fun x => (κ*dist o x*U x^β)^2
  have hb : Measurable b := ((measurable_const.mul ((continuous_const.dist continuous_id).measurable)).mul (hU.pow_const β)).pow_const 2
  let : IsProbabilityMeasure ν := ChordMeasure.isProbability μ ρ hi
    (Eventually.of_forall fun x => Real.rpow_nonneg (hU0 x) _) hW
  have hki := ChordTransform.kernel_integrable ν hb.aestronglyMeasurable
    (Eventually.of_forall fun x => sq_nonneg _) (Nat.cast_nonneg n)
    (inv_nonneg.mpr (sq_nonneg ε))
  change _ = ENNReal.ofReal (ChordMeasure.total μ ρ * ChordTransform.transform ν n b ((ε^2)⁻¹))
  rw [ENNReal.ofReal_mul hW.le,ChordTransform.transform,
    ofReal_integral_eq_lintegral_ofReal hki (Eventually.of_forall fun x =>
      (ChordTransform.kernel_pos (sq_nonneg _) (inv_nonneg.mpr (sq_nonneg ε))).le),
    ChordMeasure.lintegral_probability μ ρ (hU.pow_const _).aemeasurable hW _
      ((ChordTransform.kernel_aestronglyMeasurable μ hb.aestronglyMeasurable _ _).aemeasurable.ennreal_ofReal)]
  apply lintegral_congr
  intro x
  rw [kernel_rescaled n (hU0 x),dist_comm x o,ENNReal.ofReal_mul (Real.rpow_nonneg (hU0 x) _)]
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v : X → ℝ}
lemma exists_nonnegative_borel (hv : AEStronglyMeasurable v μ) (hpos : 0 ≤ᵐ[μ] v) :
    ∃ U : X → ℝ, Measurable U ∧ (∀ x, 0 ≤ U x) ∧ U =ᵐ[μ] v := by
  refine ⟨fun x => max (hv.mk v x) 0,hv.measurable_mk.max measurable_const,fun x => le_max_right _ _,?_⟩
  filter_upwards [hv.ae_eq_mk,hpos] with x hx hp
  change 0 ≤ v x at hp
  rw [←hx,max_eq_left hp]
lemma ae_positive_probability {U : X → ℝ} (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    {p : ℝ} (hp : 0 < p) :
    ∀ᵐ y ∂probability μ (fun x => U x^p), 0 < U y := by
  rw [probability]
  apply (ae_withDensity_iff' ((hU.pow_const _).div_const _).ennreal_ofReal.aemeasurable).mpr
  filter_upwards [] with y hy
  by_contra hh
  have hu := le_antisymm (le_of_not_gt hh) (hU0 y)
  apply hy
  simp [hu,Real.zero_rpow hp.ne']
end CAT0Fillings.ChordMeasure
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
def HasTangentBound (μ : Measure X) (U : X → ℝ) (n : ℕ) (β : ℝ) (y : X) : Prop :=
  ∀ (ε : ℕ → ℝ), (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
    ∀ (B : ℕ → ℝ≥0∞) (L : ℝ≥0∞),
    (∀ j, ENNReal.ofReal ((ε j^n)⁻¹) *
      ∫⁻ x, ENNReal.ofReal (U x^(2*(n:ℝ)*β)/
        (1+(U y^β)^2*(dist x y/ε j)^2*U x^(2*β))^n) ∂μ ≤ B j) →
    Tendsto B atTop (𝓝 L) → ENNReal.ofReal (sphereArea n/(2:ℝ)^n) ≤ L
end CAT0Fillings.TangentDensity
namespace CAT0Fillings.ChartGeometry
open TangentDensity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
include q in
lemma ae_current_tangent_density_imp (hn : 2 < n) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 ≤ β) :
    ∀ᵐ y ∂MassMeasure.currentMassMeasure hT, 0 < U y →
      TangentDensity.HasTangentBound (MassMeasure.currentMassMeasure hT) U n β y := by
  exact q.ae_current_of_ae_coordinates (P := fun y => 0 < U y →
    TangentDensity.HasTangentBound (MassMeasure.currentMassMeasure hT) U n β y)
    (fun i => q.ae_chart_tangent_density hn i U hU hU0 hb)

include q in
lemma ae_current_tangent_density (hn : 2 < n) (U : X → ℝ)
    (hU : Measurable U) (hU0 : ∀ x, 0 ≤ U x) {β : ℝ} (hb : 0 < β) :
    ∀ᵐ y ∂ChordMeasure.probability (MassMeasure.currentMassMeasure hT)
        (fun x => U x^(2*(n:ℝ)*β)),
      TangentDensity.HasTangentBound (MassMeasure.currentMassMeasure hT) U n β y := by
  have hp : 0 < 2*(n:ℝ)*β := mul_pos (mul_pos (by norm_num) (by exact_mod_cast (show 0<n by omega))) hb
  have hd := q.ae_current_tangent_density_imp hn U hU hU0 hb.le
  have hd' := (withDensity_absolutelyContinuous (MassMeasure.currentMassMeasure hT)
    (fun x => ENNReal.ofReal (U x^(2*(n:ℝ)*β)/ChordMeasure.total (MassMeasure.currentMassMeasure hT)
      (fun x => U x^(2*(n:ℝ)*β))))).ae_le hd
  filter_upwards [ChordMeasure.ae_positive_probability hU hU0 hp,hd'] with y hy hd
  exact hd hy
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
lemma rescaled_power_eq (n : ℕ) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    (ε^n)⁻¹*(1+C*(ε^2)⁻¹)^(-(n:ℝ)/2) = (ε^2+C)^(-(n:ℝ)/2) := by
  have hs : 0 < ε^2 := sq_pos_of_pos hε
  have he : 1+C*(ε^2)⁻¹ = (ε^2+C)/(ε^2) := by field_simp
  have hp : (ε^2)^(-(n:ℝ)/2) = (ε^n)⁻¹ := by
    rw [←Real.rpow_natCast ε 2,←Real.rpow_mul hε.le]
    rw [Nat.cast_ofNat,show (2:ℝ)*(-(n:ℝ)/2) = -(n:ℝ) by ring,Real.rpow_neg_natCast,
      _root_.zpow_neg,zpow_natCast]
  rw [he,Real.div_rpow (by positivity) hs.le,hp]
  have hn : (ε^n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n hε.ne')
  exact mul_div_cancel₀ _ hn

lemma rescaled_spherical_limit (n : ℕ) {ε : ℕ → ℝ}
    (hε : ∀ j, 0 < ε j) (h0 : Tendsto ε atTop (𝓝 0)) (W : ℝ) :
    Tendsto (fun j => ENNReal.ofReal ((ε j^n)⁻¹*W*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2)))
      atTop (𝓝 (ENNReal.ofReal (W/(2:ℝ)^n))) := by
  have he (j) : (ε j^n)⁻¹*W*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2) =
      W*((ε j)^2+4)^(-(n:ℝ)/2) := by
    calc
      _ = W*((ε j^n)⁻¹*(1+4*(ε j^2)⁻¹)^(-(n:ℝ)/2)) := by ring
      _ = _ := by rw [rescaled_power_eq n (hε j) (by norm_num : (0:ℝ)≤4)]
  simp_rw [he]
  have hfour : (4:ℝ)^(-(n:ℝ)/2) = ((2:ℝ)^n)⁻¹ := by
    rw [show (4:ℝ) = 2^2 by norm_num,←Real.rpow_natCast (2:ℝ) 2,
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [Nat.cast_ofNat,show (2:ℝ)*(-(n:ℝ)/2) = -(n:ℝ) by ring,Real.rpow_neg_natCast,
      _root_.zpow_neg,zpow_natCast]
  apply ENNReal.tendsto_ofReal
  have h := (tendsto_const_nhds (x := W)).mul
    (((h0.pow 2).add_const 4).rpow_const (p := -(n:ℝ)/2) (Or.inl (by norm_num)))
  simp only [zero_pow (by norm_num : 2≠0),zero_add] at h
  change Tendsto (fun j => W*(ε j^2+4)^(-(n:ℝ)/2)) atTop
    (𝓝 (W*(4:ℝ)^(-(n:ℝ)/2))) at h
  rw [hfour] at h
  simpa only [div_eq_mul_inv] using h
end CAT0Fillings.TangentDensity
end

end OAI
