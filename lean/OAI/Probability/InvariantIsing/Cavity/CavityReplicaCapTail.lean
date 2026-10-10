import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCapIntegral

namespace OAI

/-! Cap removal from tightness of the full Gibbs law. Only the Gibbs
mass of the set on which the energy cap acts enters the bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma cavity_exp_cap_discard_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (H : X → ℝ) (hH : Measurable H)
    (T : ℝ) (s : Set X) (hs : MeasurableSet s) (hgood : ∀ x ∉ s, H x ≤ T) :
    1 - (∫ x, Real.exp (-max (H x - T) 0) ∂μ) ≤ μ.real s := by
  let w := fun x => Real.exp (-max (H x - T) 0)
  have hw : Measurable w := ((hH.sub_const T).max measurable_const).neg.exp
  have hw1 x : w x ≤ 1 := (Real.exp_le_exp.mpr
    (neg_nonpos.mpr (le_max_right _ _))).trans_eq Real.exp_zero
  have hi : Integrable w μ := integrable_of_measurable_abs_le hw
    (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact hw1 x)
  have hb x : 1 - w x ≤ s.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ s
    · rw [indicator_of_mem hx]
      exact sub_le_self 1 (Real.exp_pos _).le
    · rw [indicator_of_notMem hx]
      have he : w x = 1 := by simp [w, max_eq_right (sub_nonpos.mpr (hgood x hx))]
      rw [he, sub_self]
  have he := integral_mono ((integrable_const 1).sub hi) ((integrable_const 1).indicator hs) hb
  simpa only [Pi.sub_apply, integral_sub (integrable_const 1) hi, integral_const,
    probReal_univ, one_smul, integral_indicator_const _ hs, smul_eq_mul, mul_one, w] using he

lemma cavity_replica_cap_tail_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) (T : ℝ)
    (s : Set X) (hs : MeasurableSet s) (hgood : ∀ x ∉ s, H x ≤ T) {r : ℕ}
    (F : (Fin r → X) → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightedReplicaMean ν (fun x => Real.exp (min (H x) T)) F -
      cavityWeightedReplicaMean ν (fun x => Real.exp (H x)) F| ≤
        2 * B * r * (ν.tilted H).real s := by
  let := isProbabilityMeasure_tilted he
  let g := fun x => -max (H x - T) 0
  have hg : Measurable g := ((hH.sub_const T).max measurable_const).neg
  have hgb x : Real.exp (g x) ∈ Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, (Real.exp_le_exp.mpr
      (neg_nonpos.mpr (le_max_right _ _))).trans_eq Real.exp_zero⟩
  have hgi : Integrable (fun x => Real.exp (g x)) (ν.tilted H) :=
    integrable_of_measurable_abs_le hg.exp
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact (hgb x).2)
  have hcap : Integrable (fun x => Real.exp (min (H x) T)) ν :=
    integrable_of_measurable_abs_le ((hH.min measurable_const).exp)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
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
  rw [cavityWeightedReplicaMean_exp ν _ hcap, cavityWeightedReplicaMean_exp ν _ he]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (cavity_exp_cap_discard_tail (ν.tilted H) H hH T s hs hgood) (by positivity))

end InvariantIsing

end

end OAI
