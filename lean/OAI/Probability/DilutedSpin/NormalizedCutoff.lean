import OAI.Probability.DilutedSpin.NormalizationSymmetry
import OAI.Probability.DilutedSpin.RealEncoding

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

noncomputable def centerSample {p : ℕ} (z : InteractionSample p) : InteractionSample p :=
  (centeredInteraction z,z.2)
lemma measurable_centerSample (p : ℕ) : Measurable (centerSample (p := p)) :=
  (measurable_centeredInteraction p).prodMk measurable_snd

noncomputable def centeredModel {p : ℕ} (M : Model p) : Model p :=
  mapModel M centerSample id (measurable_centerSample p) measurable_id

noncomputable def clippedModel {p : ℕ} (M : Model p) (K : ℝ) : Model p :=
  mapModel M (clipSample K) (clipReal K) (measurable_clipSample K) (measurable_clipReal K)

lemma clipReal_abs_le {K : ℝ} (hK : 0≤K) (x : ℝ) : |clipReal K x|≤|x| := by
  refine abs_le.mpr ⟨?_,?_⟩
  · apply le_max_of_le_right
    exact le_min (by linarith [abs_nonneg x]) (neg_abs_le x)
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right K x).trans (le_abs_self x))

lemma clipSample_norm_le {p : ℕ} {K : ℝ} (hK : 0≤K) (z : InteractionSample p) :
    ‖(clipSample K z).1‖≤‖z.1‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro s
  exact (clipReal_abs_le hK (z.1 s)).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 s)

lemma clipSample_difference_bound {p : ℕ} {K : ℝ} (hK : 0≤K) (z : InteractionSample p) :
    ‖z.1-(clipSample K z).1‖≤2*‖z.1‖ := by
  have h1 := norm_sub_le z.1 (clipSample K z).1
  have h2 := clipSample_norm_le hK z
  linarith

lemma clipSample_eventually_eq {p : ℕ} (z : InteractionSample p) :
    ∀ᶠ K : ℕ in atTop,clipSample (K:ℝ) z=z := by
  obtain ⟨k,hk⟩ := exists_nat_ge ‖z.1‖
  filter_upwards [eventually_ge_atTop k] with K hK
  apply clipSample_eq
  intro s
  exact (show |z.1 s|≤‖z.1‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 s).trans
    (hk.trans (by exact_mod_cast hK))

lemma clipReal_eventually_eq (x : ℝ) : ∀ᶠ K : ℕ in atTop,clipReal (K:ℝ) x=x := by
  obtain ⟨k,hk⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop k] with K hK
  exact clipReal_eq (hk.trans (by exact_mod_cast hK))

lemma clipping_interaction_error_tendsto {p : ℕ} (M : Model p)
    (hi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Tendsto (fun K : ℕ => ∫ z : InteractionSample p,‖z.1-(clipSample (K:ℝ) z).1‖ ∂M.disorder.toMeasure)
      atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (F := fun K (z : InteractionSample p) => ‖z.1-(clipSample (K:ℝ) z).1‖) (f := fun _ => 0) (fun z : InteractionSample p => 2*‖z.1‖)
    (fun K : ℕ => (measurable_fst.sub (measurable_fst.comp (measurable_clipSample (K:ℝ)))).norm.aestronglyMeasurable)
    (hi.const_mul 2)
    (fun K => ae_of_all _ (fun z => by simpa only [norm_norm] using clipSample_difference_bound (by positivity : 0≤(K:ℝ)) z))
    (ae_of_all _ (fun z => tendsto_const_nhds.congr' ((clipSample_eventually_eq z).mono (fun K hK => by dsimp only; rw [hK,sub_self,norm_zero]))))
  simpa only [integral_zero] using hh

lemma clipping_field_error_tendsto {p : ℕ} (M : Model p)
    (hi : Integrable (fun x : ℝ => |x|) M.field.toMeasure) :
    Tendsto (fun K : ℕ => ∫ x : ℝ,|x-clipReal (K:ℝ) x| ∂M.field.toMeasure) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (F := fun K (x : ℝ) => |x-clipReal (K:ℝ) x|) (f := fun _ => 0) (fun x : ℝ => 2*|x|)
    (fun K : ℕ => (measurable_id.sub (measurable_clipReal (K:ℝ))).abs.aestronglyMeasurable)
    (hi.const_mul 2)
    (fun K => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have h1 := abs_sub x (clipReal (K:ℝ) x)
      have h2 := clipReal_abs_le (by positivity : 0≤(K:ℝ)) x
      linarith))
    (ae_of_all _ (fun x => tendsto_const_nhds.congr' ((clipReal_eventually_eq x).mono (fun K hK => by dsimp only; rw [hK,sub_self,abs_zero]))))
  simpa only [integral_zero] using hh

lemma centeredModel_symmetric {p : ℕ} (M : Model p) (hM : Admissible M) (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l)))
      (centeredModel M).disorder.toMeasure (centeredModel M).disorder.toMeasure := by
  have hh := centeredInteraction_permutation M hM e
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map centerSample M.disorder.toMeasure)=Measure.map _ (Measure.map centerSample M.disorder.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_centerSample p),
      Measure.map_map (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop) (measurable_centerSample p)]
    exact hh.map_eq

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped BigOperators

lemma convex_pow_tangent {p : ℕ} (hp : Even p) (x y : ℝ) :
    (p:ℝ)*y^(p-1)*(x-y) ≤ x^p-y^p := by
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => t^p) := hp.convexOn_pow
  have hd : HasDerivAt (fun t : ℝ => t^p) ((p:ℝ)*y^(p-1)) y := hasDerivAt_pow p y
  rcases lt_trichotomy y x with h | h | h
  · have hh := hc.le_slope_of_hasDerivAt (mem_univ y) (mem_univ x) h hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
  · subst x
    simp
  · have hh := hc.slope_le_of_hasDerivAt (mem_univ x) (mem_univ y) h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp (show (y^p-x^p)/(y-x)≤(p:ℝ)*y^(p-1) from hh)
    nlinarith

 
lemma even_cavity_remainder_nonneg {p : ℕ} (hp : Even p) (hp1 : 1≤p) (P B : ℝ) :
    0 ≤ P^p-(p:ℝ)*P*B^(p-1)+((p-1:ℕ):ℝ)*B^p := by
  have ht := convex_pow_tangent hp P B
  have he : B^(p-1)*B=B^p := by rw [← pow_succ,Nat.sub_add_cancel hp1]
  rw [Nat.cast_sub hp1,Nat.cast_one]
  nlinarith

/-- Coefficients of all three regularized insertions share this sign. -/
lemma admissible_upper_coefficient_nonpos {p : ℕ} (M : Model p) (hM : Admissible M)
    (n : ℕ) (hn : 1≤n) (t P B : ℝ) (ht : 0≤t) :
    -(t^n/(n:ℝ))*(∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      (P^p-(p:ℝ)*P*B^(p-1)+((p-1:ℕ):ℝ)*B^p) ≤ 0 := by
  have hr := even_cavity_remainder_nonneg hM.even (by have := hM.arity; omega) P B
  have hb := hM.positivity n hn
  apply mul_nonpos_of_nonpos_of_nonneg _ hr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hb

lemma regularized_ratio_pos {d t : ℝ} (hd : |d|<1) (ht0 : 0≤t) (ht1 : t≤1) :
    0 < 1+t*d := by
  have hlo := (abs_lt.mp hd).1
  by_cases h : 0 ≤ d
  · have := mul_nonneg ht0 h
    linarith
  · have := mul_le_mul_of_nonpos_right ht1 (le_of_not_ge h)
    nlinarith

lemma regularized_ratio_bounds {d d₀ t lo hi : ℝ}
    (hd₀ : |d₀|<1) (ht0 : 0≤t) (ht1 : t≤1)
    (hlo1 : lo≤1) (hhi1 : 1≤hi)
    (hlo : lo≤(1+d)/(1+d₀)) (hhi : (1+d)/(1+d₀)≤hi) :
    lo≤(1+t*d)/(1+t*d₀) ∧ (1+t*d)/(1+t*d₀)≤hi := by
  have hp : 0<1+d₀ := by have := (abs_lt.mp hd₀).1; linarith
  have hpl := regularized_ratio_pos hd₀ ht0 ht1
  have hl := (le_div_iff₀ hp).mp hlo
  have hh := (div_le_iff₀ hp).mp hhi
  constructor
  · rw [le_div_iff₀ hpl]
    have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hlo1)
    have h2 := mul_nonneg ht0 (sub_nonneg.mpr hl)
    nlinarith
  · rw [div_le_iff₀ hpl]
    have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hhi1)
    have h2 := mul_nonneg ht0 (sub_nonneg.mpr hh)
    nlinarith

/-- Normalized regularization never requires integrability of log a. -/
lemma regularized_normalized_log_bound {d d₀ t C : ℝ} (hC : 0≤C)
    (hd : |d|<1) (hd₀ : |d₀|<1) (ht0 : 0≤t) (ht1 : t≤1)
    (hlo : Real.exp (-C)≤(1+d)/(1+d₀)) (hhi : (1+d)/(1+d₀)≤Real.exp C) :
    |Real.log (1+t*d)-Real.log (1+t*d₀)|≤C := by
  have hp := regularized_ratio_pos hd ht0 ht1
  have hp₀ := regularized_ratio_pos hd₀ ht0 ht1
  rw [← Real.log_div hp.ne' hp₀.ne']
  have hb := regularized_ratio_bounds hd₀ ht0 ht1
    (Real.exp_le_one_iff.mpr (by linarith)) (Real.one_le_exp_iff.mpr hC) hlo hhi
  have hq := div_pos hp hp₀
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hq).mpr hb.1,
    (Real.log_le_iff_le_exp hq).mpr hb.2⟩

end DilutedSpinGlass

end

end OAI
