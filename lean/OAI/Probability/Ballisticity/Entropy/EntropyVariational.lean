import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience.Entropy

variable {X : Type*} [MeasurableSpace X]

theorem entropy_test_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ∞)
    (F : X → ℝ) (hFμ : Integrable F μ)
    (he : Integrable (fun x => Real.exp (F x)) ν) :
    (∫ x, F x ∂μ) - Real.log (∫ x, Real.exp (F x) ∂ν) ≤
      (klDiv μ ν).toReal := by
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hkl
  have hac' : μ ≪ ν.tilted F := hac.trans (absolutelyContinuous_tilted he)
  have hh := integrable_llr_tilted_right hac hFμ hllr he
  have hnon := integral_llr_add_sub_measure_univ_nonneg hac' hh
  have : IsProbabilityMeasure (ν.tilted F) := isProbabilityMeasure_tilted he
  rw [probReal_univ,probReal_univ,add_sub_cancel_right] at hnon
  rw [integral_llr_tilted_right hac hFμ he hllr] at hnon
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  linarith

theorem entropy_exp_test_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ∞)
    (F : X → ℝ) (hFμ : Integrable F μ)
    (he : Integrable (fun x => Real.exp (F x)) ν) :
    (∫ x, F x ∂μ) - (∫ x, Real.exp (F x) ∂ν) + 1 ≤
      (klDiv μ ν).toReal := by
  have h := entropy_test_le μ ν hkl F hFμ he
  have hp : 0 < ∫ x, Real.exp (F x) ∂ν := integral_exp_pos he
  have hl := Real.log_le_sub_one_of_pos hp
  linarith

lemma entropy_young_exact {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    u*v - Real.exp v + 1 ≤ klFun u := by
  by_cases h0 : u = 0
  · simp [h0,klFun,Real.exp_nonneg]
  have hp : 0 < u := lt_of_le_of_ne hu (Ne.symm h0)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v-Real.log u)) hu
  have heq : u*Real.exp (v-Real.log u) = Real.exp v := by
    rw [Real.exp_sub,Real.exp_log hp]
    field_simp
  rw [heq] at he
  unfold klFun
  nlinarith

def ExpBudget (μ ν : Measure X) (C : ℝ) : Prop :=
  ∀ F : X → ℝ, Measurable F → (∃ B : ℝ, ∀ x, |F x| ≤ B) →
    (∫ x, F x ∂μ) - (∫ x, Real.exp (F x) ∂ν) + 1 ≤ C

lemma integrable_of_bounded {μ : Measure X} [IsFiniteMeasure μ] {F : X → ℝ}
    (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) : Integrable F μ := by
  obtain ⟨B,hB⟩ := hB
  exact (integrable_const B).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)

lemma exp_integrable_of_bounded {μ : Measure X} [IsFiniteMeasure μ] {F : X → ℝ}
    (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    Integrable (fun x => Real.exp (F x)) μ := by
  obtain ⟨B,hB⟩ := hB
  exact (integrable_const (Real.exp B)).mono' hF.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x)))

lemma expBudget_of_kl_le (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (hC : 0 ≤ C) (hkl : klDiv μ ν ≤ ENNReal.ofReal C) :
    ExpBudget μ ν C := by
  intro F hF hB
  have hf : klDiv μ ν ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  exact (entropy_exp_test_le μ ν hf F (integrable_of_bounded hF hB)
    (exp_integrable_of_bounded hF hB)).trans (ENNReal.toReal_le_of_le_ofReal hC hkl)

lemma ExpBudget.nonneg (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : 0 ≤ C := by
  have hh := h (fun _ => 0) measurable_const ⟨0,fun _ => by simp⟩
  simpa using hh

lemma ExpBudget.absolutelyContinuous (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  by_contra hμs
  have hp : 0 < μ.real s := ENNReal.toReal_pos hμs (measure_ne_top _ _)
  let t : ℝ := (C+1) / μ.real s
  have ht : 0 < t := div_pos (by linarith [h.nonneg μ ν]) hp
  let F : X → ℝ := s.indicator (fun _ => t)
  have hF : Measurable F := measurable_const.indicator hs
  have hh := h F hF ⟨t,fun x => by
    by_cases hx : x ∈ s
    · simp [F,hx,abs_of_pos ht]
    · simp [F,hx,ht.le]⟩
  have he : (∫ x, Real.exp (F x) ∂ν) = 1 := by
    have heq : (fun x => Real.exp (F x)) =ᵐ[ν] fun _ => (1:ℝ) := by
      filter_upwards [show ∀ᵐ x ∂ν, x ∉ s from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hνs] with x hx
      simp [F,hx]
    simpa using integral_congr_ae heq
  rw [he,show (∫ x, F x ∂μ) = μ.real s * t by
    exact integral_indicator_const t hs] at hh
  dsimp [t] at hh
  rw [mul_div_cancel₀ _ hp.ne'] at hh
  linarith

lemma integrable_of_bounded_truncated_integrals (μ : Measure X) [IsFiniteMeasure μ]
    (F : X → ℝ) (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (C : ℝ) (hbound : ∀ n : ℕ, (∫ x, min (n:ℝ) (F x) ∂μ) ≤ C) :
    Integrable F μ := by
  have hi (n : ℕ) : Integrable (fun x => min (n:ℝ) (F x)) μ := by
    apply integrable_of_bounded (measurable_const.min hF)
    exact ⟨n,fun x => by
      rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
      exact min_le_left _ _⟩
  have heq (x : X) : ENNReal.ofReal (F x) =
      ⨆ n : ℕ, ENNReal.ofReal (min (n:ℝ) (F x)) := by
    apply le_antisymm
    · obtain ⟨n,hn⟩ := exists_nat_ge (F x)
      exact (by rw [min_eq_right hn] : ENNReal.ofReal (F x) ≤
        ENNReal.ofReal (min (n:ℝ) (F x))).trans (le_iSup (fun n : ℕ => ENNReal.ofReal (min (n:ℝ) (F x))) n)
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_right _ _)
  have hl : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal C := by
    simp_rw [heq]
    rw [lintegral_iSup (fun n => (measurable_const.min hF).ennreal_ofReal)
      (fun n m hnm x => ENNReal.ofReal_le_ofReal
        (min_le_min_right _ (Nat.cast_le.mpr hnm)))]
    apply iSup_le
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (hi n)
      (ae_of_all _ fun x => le_min (Nat.cast_nonneg _) (hF0 x))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
    (ae_of_all _ hF0)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)

lemma ExpBudget.finite_kl (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : klDiv μ ν ≠ ∞ := by
  have hac := h.absolutelyContinuous μ ν
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν) = 1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  let F : X → ℝ := fun x => Real.log (max 1 (g x))
  have hF : Measurable F := (measurable_const.max hg).log
  have hF0 (x : X) : 0 ≤ F x := Real.log_nonneg (le_max_left _ _)
  have hFi : Integrable F μ := by
    apply integrable_of_bounded_truncated_integrals μ F hF hF0 (C+1)
    intro n
    have hFn : Measurable (fun x => min (n:ℝ) (F x)) := measurable_const.min hF
    have hBn : ∃ B : ℝ, ∀ x, |min (n:ℝ) (F x)| ≤ B :=
      ⟨n,fun x => by
        rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
        exact min_le_left _ _⟩
    have he := h _ hFn hBn
    have he₂ : (∫ x, Real.exp (min (n:ℝ) (F x)) ∂ν) ≤ 2 := by
      have hp := integral_mono (exp_integrable_of_bounded hFn hBn)
        ((integrable_const 1).add hgi) (fun x => by
          calc Real.exp (min (n:ℝ) (F x)) ≤ Real.exp (F x) :=
              Real.exp_le_exp.mpr (min_le_right _ _)
            _ = max 1 (g x) := Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
            _ ≤ 1+g x := max_le (by linarith [hg0 x]) (by linarith))
      simpa only [Pi.add_apply,integral_add (integrable_const 1) hgi,integral_const,
        probReal_univ,one_smul,hg1,one_add_one_eq_two] using hp
    linarith
  have hpos : Integrable (fun x => g x * F x) ν :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hFi
  have hlog : Integrable (fun x => g x * Real.log (g x)) ν := by
    apply (hpos.add (integrable_const 1)).mono' (hg.mul hg.log).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |g x * Real.log (g x)| ≤ g x * F x + 1
      apply abs_le.mpr
      constructor
      · have hlow : -1 ≤ g x * Real.log (g x) := by
          by_cases hx : g x = 0
          · simp [hx]
          have hl := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log (hg0 x)) (hg0 x)
          rw [mul_neg,mul_inv_cancel₀ hx] at hl
          exact hl
        have hn : 0 ≤ g x * F x := mul_nonneg (hg0 x) (hF0 x)
        linarith
      · by_cases hx : g x = 0
        · simp [hx]
        have hl := mul_le_mul_of_nonneg_left
          (Real.log_le_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) (le_max_right 1 (g x))) (hg0 x)
        change g x * Real.log (g x) ≤ g x * F x at hl
        linarith
  exact klDiv_ne_top hac ((integrable_rnDeriv_mul_log_iff hac).mp hlog)

noncomputable def logClip (n : ℕ) (x : ℝ) : ℝ := max (-(n:ℝ)) (min (n:ℝ) x)

lemma abs_logClip_le (n : ℕ) (x : ℝ) : |logClip n x| ≤ (n:ℝ) := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩

lemma abs_logClip_le_abs (n : ℕ) (x : ℝ) : |logClip n x| ≤ |x| := by
  unfold logClip
  rcases le_total x (n:ℝ) with hx|hx
  · rw [min_eq_right hx]
    rcases le_total (-(n:ℝ)) x with hn|hn
    · rw [max_eq_right hn]
    · rw [max_eq_left hn,abs_neg,abs_of_nonneg (Nat.cast_nonneg n)]
      exact (by linarith : (n:ℝ) ≤ -x).trans (neg_le_abs _)
  · rw [min_eq_left hx,max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n]),abs_of_nonneg (Nat.cast_nonneg n)]
    exact hx.trans (le_abs_self _)

lemma logClip_eventually (x : ℝ) : ∀ᶠ n : ℕ in atTop, logClip n x = x := by
  obtain ⟨N,hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have h : |x| ≤ (n:ℝ) := hN.trans (Nat.cast_le.mpr hn)
  rw [logClip,min_eq_right ((le_abs_self _).trans h),max_eq_right]
  linarith [neg_le_abs x]

lemma exp_logClip_log_le {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (logClip n (Real.log u)) ≤ 1+u := by
  by_cases h : 0 ≤ Real.log u
  · calc Real.exp (logClip n (Real.log u)) ≤ Real.exp (Real.log u) := by
            apply Real.exp_le_exp.mpr
            exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)
         _ = u := Real.exp_log hu
         _ ≤ _ := by linarith
  · calc Real.exp (logClip n (Real.log u)) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr
            exact max_le (neg_nonpos.mpr (Nat.cast_nonneg n))
              ((min_le_right _ _).trans (le_of_not_ge h))
         _ = 1 := Real.exp_zero
         _ ≤ _ := by linarith

theorem kl_le_of_expBudget (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) :
    klDiv μ ν ≤ ENNReal.ofReal C := by
  have hfinite := h.finite_kl μ ν
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hfinite
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hgp : ∀ᵐ x ∂μ, 0 < g x := by
    filter_upwards [Measure.rnDeriv_pos hac,hac.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx ht
    exact ENNReal.toReal_pos hx.ne' ht.ne
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν) = 1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  let F : ℕ → X → ℝ := fun n x =>
    if g x = 0 then -(n:ℝ) else logClip n (Real.log (g x))
  have hFm (n : ℕ) : Measurable (F n) := by
    exact measurable_const.ite (measurableSet_eq_fun hg measurable_const)
      (measurable_const.max (measurable_const.min hg.log))
  have hFb (n : ℕ) (x : X) : |F n x| ≤ (n:ℝ) := by
    dsimp only [F]
    split_ifs
    · rw [abs_neg,abs_of_nonneg (Nat.cast_nonneg n)]
    · exact abs_logClip_le n _
  have hFdom (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖llr μ ν x‖ := by
    filter_upwards [hgp] with x hx
    simp only [F,ite_eq_right hx.ne',llr,Real.norm_eq_abs]
    exact abs_logClip_le_abs n _
  have hFpt : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (llr μ ν x)) := by
    filter_upwards [hgp] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [logClip_eventually (Real.log (g x))] with n hn
    simpa only [F,ite_eq_right hx.ne',llr] using hn.symm
  have hFlim : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, llr μ ν x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖llr μ ν x‖)
      (fun n => (hFm n).aestronglyMeasurable) hllr.norm hFdom hFpt
  have heDom (n : ℕ) (x : X) : ‖Real.exp (F n x)‖ ≤ 1+g x := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    dsimp only [F]
    split_ifs with hx
    · have he : Real.exp (-(n:ℝ)) ≤ 1 := by
        rw [←Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
      linarith [hg0 x]
    · exact exp_logClip_log_le (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) n
  have hePt (x : X) : Tendsto (fun n => Real.exp (F n x)) atTop (𝓝 (g x)) := by
    by_cases hx : g x = 0
    · simp only [F,hx,ite_eq_left]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    · apply tendsto_const_nhds.congr'
      filter_upwards [logClip_eventually (Real.log (g x))] with n hn
      simp only [F,ite_eq_right hx,hn,Real.exp_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx))]
  have heLim : Tendsto (fun n => ∫ x, Real.exp (F n x) ∂ν) atTop (𝓝 1) := by
    rw [←hg1]
    exact tendsto_integral_of_dominated_convergence (fun x => 1+g x)
      (fun n => (hFm n).exp.aestronglyMeasurable) ((integrable_const 1).add hgi)
      (fun n => ae_of_all _ (heDom n)) (ae_of_all _ hePt)
  have hbound (n : ℕ) := h (F n) (hFm n) ⟨n,hFb n⟩
  have hlimit := (hFlim.sub heLim).add (tendsto_const_nhds (x := (1:ℝ)))
  have hh := le_of_tendsto hlimit (Eventually.of_forall hbound)
  have hh' : (klDiv μ ν).toReal ≤ C := by
    rw [toReal_klDiv_of_measure_eq hac (by simp)]
    linarith
  rw [←ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hh'

end DirectionalTransience.Entropy

end

end OAI
