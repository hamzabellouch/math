import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCapIntegral

namespace OAI

/-! A first absolute energy moment suffices to remove the upper cap
from bounded replica tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavity_exp_cap_discard_first {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (H : X → ℝ) (hH : Measurable H)
    {T : ℝ} (hT : 0 < T) (hi : Integrable (fun x => |H x|) μ) :
    1 - (∫ x, Real.exp (-max (H x - T) 0) ∂μ) ≤ (∫ x, |H x| ∂μ) / T := by
  let w := fun x => Real.exp (-max (H x - T) 0)
  have hw : Measurable w := ((hH.sub_const T).max measurable_const).neg.exp
  have hw1 x : w x ≤ 1 := (Real.exp_le_exp.mpr (by linarith [le_max_right (H x - T) 0])).trans_eq Real.exp_zero
  have hiw : Integrable w μ := integrable_of_measurable_abs_le hw
    (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact hw1 x)
  have hb x : 1 - w x ≤ |H x| / T := by
    by_cases hx : H x ≤ T
    · have he : w x = 1 := by simp [w, max_eq_right (sub_nonpos.mpr hx)]
      rw [he, sub_self]
      exact div_nonneg (abs_nonneg _) hT.le
    · have hpos : 0 < H x := hT.trans (lt_of_not_ge hx)
      have hratio : 1 ≤ |H x| / T := by
        rw [abs_of_pos hpos]
        exact (one_le_div hT).mpr (le_of_not_ge hx)
      exact (sub_le_self 1 (Real.exp_pos _).le).trans hratio
  have h := integral_mono ((integrable_const 1).sub hiw) (hi.div_const T) hb
  simpa only [Pi.sub_apply, integral_sub (integrable_const 1) hiw, integral_const,
    probReal_univ, one_smul, integral_div, w] using h

lemma cavity_replica_cap_error_first {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) {T : ℝ} (hT : 0 < T)
    (hi : Integrable (fun x => |H x|) (ν.tilted H)) {r : ℕ}
    (F : (Fin r → X) → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |(∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν.tilted (fun x => min (H x) T))) -
      ∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν.tilted H)| ≤
        2 * B * r * (∫ x, |H x| ∂ν.tilted H) / T := by
  let := isProbabilityMeasure_tilted he
  let g := fun x => -max (H x - T) 0
  have hg : Measurable g := ((hH.sub_const T).max measurable_const).neg
  have hgb x : Real.exp (g x) ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, (Real.exp_le_exp.mpr (neg_nonpos.mpr (le_max_right _ _))).trans_eq Real.exp_zero⟩
  have hgi : Integrable (fun x => Real.exp (g x)) (ν.tilted H) :=
    integrable_of_measurable_abs_le hg.exp
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hgb x).2)
  have hsum : H + g = fun x => min (H x) T := by
    funext x
    change H x + -max (H x - T) 0 = min (H x) T
    by_cases hx : H x ≤ T
    · rw [max_eq_right (sub_nonpos.mpr hx), min_eq_left hx]
      ring
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hx)), min_eq_right (le_of_not_ge hx)]
      ring
  have htilt : (ν.tilted H).tilted g = ν.tilted (fun x => min (H x) T) := by
    rw [tilted_tilted he, hsum]
  have hb := cavity_soft_cutoff_replica_error (ν.tilted H) (fun x => Real.exp (g x))
    hg.exp hgb F hF hB hFb
  rw [cavityWeightedReplicaMean_exp _ g hgi F, htilt] at hb
  have hd := cavity_exp_cap_discard_first (ν.tilted H) H hH hT hi
  exact hb.trans ((mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq (by ring))

theorem cavity_replica_cap_mean_error_first {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => |H (ω,x)|) ((ν ω).tilted (fun x => H (ω,x))))
    (hmi : Integrable (fun ω => ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {B K T : ℝ} (hB : 0 ≤ B) (hT : 0 < T) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B)
    (hK : (∫ ω, ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ K) :
    |∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (min (H (ω,x)) T))
      (fun σ => F (ω,σ)) -
      cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤ 2 * B * r * K / T := by
  let w := fun p : Ω × X => Real.exp (H p)
  let v := fun p : Ω × X => Real.exp (min (H p) T)
  have hw : Measurable w := hH.exp
  have hv : Measurable v := (hH.min measurable_const).exp
  let D := fun ω => cavityWeightedReplicaMean (ν ω) (fun x => v (ω,x)) (fun σ => F (ω,σ)) -
    cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x)) (fun σ => F (ω,σ))
  have hD : Measurable D :=
    ((measurable_cavityWeightNumerator ν hν v hv F hF).div
      ((measurable_cavityWeightNormalizer ν hν v hv).pow_const r)).sub
    ((measurable_cavityWeightNumerator ν hν w hw F hF).div
      ((measurable_cavityWeightNormalizer ν hν w hw).pow_const r))
  have hb : ∀ᵐ ω ∂P, |D ω| ≤
      2 * B * r * (∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) / T := by
    filter_upwards [he, hi] with ω hωe hωi
    have hvI : Integrable (fun x => Real.exp (min (H (ω,x)) T)) (ν ω) :=
      integrable_of_measurable_abs_le (hv.comp measurable_prodMk_left)
        (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
    have hh := cavity_replica_cap_error_first (ν ω) (fun x => H (ω,x))
      (hH.comp measurable_prodMk_left) hωe hT hωi (fun σ => F (ω,σ))
      (hF.comp measurable_prodMk_left) hB (hFb ω)
    rw [← cavityWeightedReplicaMean_exp (ν ω) _ hvI,
      ← cavityWeightedReplicaMean_exp (ν ω) _ hωe] at hh
    exact hh
  have hE := (hmi.const_mul (2 * B * r)).div_const T
  have hiD : Integrable D P := hE.mono' hD.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hb)
  calc
    _ ≤ ∫ ω, |D ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2 * B * r * (∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) / T ∂P :=
      integral_mono_ae hiD.abs hE hb
    _ = 2 * B * r * (∫ ω, ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) / T := by
      rw [integral_div, integral_const_mul]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) hT.le

lemma cavity_replica_cap_expectation_error_first {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => |H (ω,x)|) ((ν ω).tilted (fun x => H (ω,x))))
    (hmi : Integrable (fun ω => ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {B K T : ℝ} (hB : 0 ≤ B) (hT : 0 < T) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B)
    (hK : (∫ ω, ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ K) :
    |(∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (min (H (ω,x)) T))
        (fun σ => F (ω,σ)) ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤ 2 * B * r * K / T := by
  have hc : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (min (H (ω,x)) T)) (ν ω) := by
    apply ae_of_all
    intro ω
    exact integrable_of_measurable_abs_le
      (((hH.comp measurable_prodMk_left).min measurable_const).exp)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hiC := cavity_exp_replicaMean_integrable P ν hν (fun p => min (H p) T)
    (hH.min measurable_const) F hF hc hFb
  have hiF := cavity_exp_replicaMean_integrable P ν hν H hH F hF he hFb
  rw [← integral_sub hiC hiF]
  exact cavity_replica_cap_mean_error_first P ν hν H hH F hF he hi hmi hB hT hFb hK


end InvariantIsing

end

end OAI
