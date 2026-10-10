import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianSquareTails

namespace OAI

noncomputable section
open scoped Topology
open Filter MeasureTheory Real Set
namespace SKRatio.Bins
open SKRatioClock.Regression

lemma tanh_exp_negative (x : ℝ) : tanh x=(1-exp (-2*x))/(1+exp (-2*x)) := by
  rw [tanh_eq]
  have he : exp (-2*x)=exp (-x)/exp x := by
    rw [←exp_sub]; congr 1; ring
  rw [he]
  field_simp

lemma tendsto_tanh_atTop : Tendsto tanh atTop (𝓝 1) := by
  have hn : Tendsto (fun x : ℝ => -2*x) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2)) using 1
    funext x
    simp
  have he := tendsto_exp_atBot.comp hn
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).div ((tendsto_const_nhds (x := (1 : ℝ))).add he)
    (by norm_num : (1:ℝ)+0≠0)
  change Tendsto (fun x : ℝ => (1-exp (-2*x))/(1+exp (-2*x))) atTop (𝓝 ((1-0)/(1+0))) at hh
  simpa only [sub_zero,add_zero,div_one,←tanh_exp_negative] using hh

lemma tanh_tail_uniform {δ : ℝ} (hδ : 0<δ) : ∃ R : ℝ, 0<R ∧
    ∀ S : ℝ, R≤S → ∀ x : ℝ, S≤|x| →
      |tanh x-tanh (if 0≤x then S else -S)|<δ := by
  have he := tendsto_tanh_atTop.eventually (Metric.ball_mem_nhds (1:ℝ) (half_pos hδ))
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  refine ⟨max R 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro S hS x hx
  have hSR : R≤S := (le_max_left _ _).trans hS
  have hpos : 0≤S := (le_of_lt (by norm_num : (0:ℝ)<1)).trans ((le_max_right _ _).trans hS)
  by_cases hx0 : 0≤x
  · rw [ite_eq_left hx0]
    rw [abs_of_nonneg hx0] at hx
    have h1 : |tanh x-1|<δ/2 := hR x (hSR.trans hx)
    have h2 : |tanh S-1|<δ/2 := hR S hSR
    have hh := abs_sub_le (tanh x) 1 (tanh S)
    rw [abs_sub_comm 1 (tanh S)] at hh
    linarith
  · rw [ite_eq_right hx0,tanh_neg]
    have hx' : S≤-x := by simpa only [abs_of_neg (lt_of_not_ge hx0)] using hx
    have h1 : |tanh (-x)-1|<δ/2 := hR (-x) (hSR.trans hx')
    have h2 : |tanh S-1|<δ/2 := hR S hSR
    have hh := abs_sub_le (tanh (-x)) 1 (tanh S)
    rw [abs_sub_comm 1 (tanh S)] at hh
    rw [tanh_neg] at hh h1
    have hid : |tanh x- -tanh S|=|-tanh x-tanh S| := by
      rw [←abs_neg (tanh x- -tanh S)]; congr 1; ring
    rw [hid]
    linarith

lemma squareTail_antitone {R S : ℝ} (hRS : R≤S) (x : ℝ) :
    squareTail S x ≤ squareTail R x := by
  unfold squareTail
  split_ifs with hS hR hR
  · rfl
  · exact (hR (hRS.trans_lt hS)).elim
  · exact sq_nonneg _
  · rfl

lemma integrable_squareTail {μ : Measure ℝ} (hi : Integrable (fun x : ℝ => x^2) μ) (R : ℝ) :
    Integrable (squareTail R) μ := by
  apply hi.mono' (measurable_squareTail R).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]
    exact squareTail_le R x)

lemma tendsto_integral_squareTail {μ : Measure ℝ} (hi : Integrable (fun x : ℝ => x^2) μ) :
    Tendsto (fun R : ℕ => ∫ x, squareTail R x ∂μ) atTop (𝓝 0) := by
  have hh : Tendsto (fun R : ℕ => ∫ x, squareTail R x ∂μ) atTop (𝓝 (∫ _x, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x^2)
    · intro R
      exact (measurable_squareTail R).aestronglyMeasurable
    · exact hi
    · intro R
      exact ae_of_all _ (fun x => by
        rw [norm_eq_abs,abs_of_nonneg (squareTail_nonneg _ _)]
        exact squareTail_le R x)
    · apply ae_of_all
      intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with R hR
      have hx : |x|≤(R:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hR)
      simp [squareTail,not_lt.mpr hx]
  simpa only [integral_zero] using hh

end SKRatio.Bins

end

end OAI
