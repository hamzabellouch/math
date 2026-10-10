import Mathlib
import OAI.Probability.SLELocalization.LoewnerExit
import OAI.Probability.SLELocalization.PhysicalPast

namespace OAI


/-! Conformal localization and Is Loewner Trace Using estimates. -/

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge
namespace IsLoewnerTraceUsing
variable {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma hasDerivAt_real (h : IsLoewnerTraceUsing U γ g f)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    HasDerivAt (fun s => (g s z).re)
      (2 * ((g t z).re-U t) / Complex.normSq (g t z-(U t:ℂ))) t := by
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (h.hasDerivAt_eval ht hz)
  simpa [Complex.div_re,Function.comp_def] using hh

lemma initial_real_le (h : IsLoewnerTraceUsing U γ g f)
    {T M : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hU : ∀ t ∈ Icc 0 T, U t ≤ M) (hend : (g T z).re ≤ M) : z.re ≤ M := by
  let R : ℝ → ℝ := fun s => (g (T-s) z).re
  have hc : ContinuousOn R (Icc 0 T) :=
    (Complex.continuous_re.comp_continuousOn (h.continuous_eval hT hz)).comp
      (continuous_const.sub continuous_id).continuousOn (fun s hs => by constructor <;> linarith [hs.1,hs.2])
  have hd (s : ℝ) (hs : s ∈ Ico 0 T) : HasDerivAt R
      (-2*((g (T-s) z).re-U (T-s))/Complex.normSq (g (T-s) z-(U (T-s):ℂ))) s := by
    have he := (h.hasDerivAt_real (sub_pos.2 hs.2)
      (survivingDomain_mono (by linarith [hs.1]) hz)).comp s
      ((hasDerivAt_id s).const_sub T)
    simpa [R,neg_div,Function.comp_def] using he
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb := image_le_of_deriv_right_lt_deriv_boundary hc
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (B:=fun _ => M+ε) (B':=fun _ => 0)
    (by dsimp [R]; simpa using hend.trans (by linarith : M ≤ M+ε))
    (fun _ => hasDerivAt_const _ _) (fun s hs he => ?_) (x:=T) ⟨hT,le_rfl⟩
  · simpa [R,h.initial z hz.1.1] using hb
  · have hden := Complex.normSq_pos.2
      (h.centered_ne_zero (t:=T-s) (z:=z) (by linarith [hs.2]) (survivingDomain_mono (by linarith [hs.1]) hz))
    have hh := hU (T-s) (by constructor <;> linarith [hs.1,hs.2])
    dsimp [R] at he
    exact div_neg_of_neg_of_pos (by nlinarith) hden

lemma initial_real_ge (h : IsLoewnerTraceUsing U γ g f)
    {T m : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hU : ∀ t ∈ Icc 0 T, m ≤ U t) (hend : m ≤ (g T z).re) : m ≤ z.re := by
  let R : ℝ → ℝ := fun s => -(g (T-s) z).re
  have hc : ContinuousOn R (Icc 0 T) :=
    (Complex.continuous_re.comp_continuousOn (h.continuous_eval hT hz)).neg.comp
      (continuous_const.sub continuous_id).continuousOn (fun s hs => by constructor <;> linarith [hs.1,hs.2])
  have hd (s : ℝ) (hs : s ∈ Ico 0 T) : HasDerivAt R
      (2*((g (T-s) z).re-U (T-s))/Complex.normSq (g (T-s) z-(U (T-s):ℂ))) s := by
    have he := ((h.hasDerivAt_real (sub_pos.2 hs.2)
      (survivingDomain_mono (by linarith [hs.1]) hz)).comp s
      ((hasDerivAt_id s).const_sub T)).neg
    convert he using 1
    all_goals first | rfl | norm_num
  have hn : -z.re ≤ -m := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hb := image_le_of_deriv_right_lt_deriv_boundary hc
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (B:=fun _ => -m+ε) (B':=fun _ => 0)
      (by dsimp [R]; simpa using (show -(g T z).re ≤ -m+ε by linarith))
      (fun _ => hasDerivAt_const _ _) (fun s hs he => ?_) (x:=T) ⟨hT,le_rfl⟩
    · simpa [R,h.initial z hz.1.1] using hb
    · have hden := Complex.normSq_pos.2
        (h.centered_ne_zero (t:=T-s) (z:=z) (by linarith [hs.2]) (survivingDomain_mono (by linarith [hs.1]) hz))
      have hh := hU (T-s) (by constructor <;> linarith [hs.1,hs.2])
      dsimp [R] at he
      exact div_neg_of_neg_of_pos (by nlinarith) hden
  linarith

lemma initial_height_sq_le (h : IsLoewnerTraceUsing U γ g f)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    z.im^2 ≤ (g T z).im^2+4*T := by
  have hm : MonotoneOn (fun s => (g s z).im^2+4*s) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
      (((Complex.continuous_im.comp_continuousOn (h.continuous_eval hT hz)).pow 2).add
        (continuous_const.mul continuous_id).continuousOn)
      (f':=fun t => -4*(g t z).im^2/Complex.normSq (g t z-(U t:ℂ))+4)
    · intro t ht
      rw [interior_Icc] at ht
      convert (((h.hasDerivAt_height ht.1 (survivingDomain_mono ht.2.le hz)).pow 2).add
        ((hasDerivAt_id t).const_mul 4)).hasDerivWithinAt using 1
      all_goals first | rfl | (norm_num; ring)
    · intro t ht
      rw [interior_Icc] at ht
      have hd := Complex.normSq_pos.2 (h.centered_ne_zero ht.1.le (survivingDomain_mono ht.2.le hz))
      have he : (g t z).im^2 ≤ Complex.normSq (g t z-(U t:ℂ)) := by
        simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
        nlinarith [sq_nonneg ((g t z).re-U t)]
      have hb : -4*(g t z).im^2/Complex.normSq (g t z-(U t:ℂ)) ≥ -4 := by
        exact (le_div_iff₀ hd).2 (by nlinarith)
      linarith
  simpa [h.initial z hz.1.1] using hm ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT

end IsLoewnerTraceUsing

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge

theorem trace_driver_rectangle
    {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing U γ g f) {T m M : ℝ} (_hT : 0 ≤ T)
    (_hU : ContinuousOn U (Icc 0 T))
    (hb : ∀ t ∈ Icc 0 T, m ≤ U t ∧ U t ≤ M) :
    ∀ t ∈ Icc 0 T, m ≤ (γ t).re ∧ (γ t).re ≤ M ∧ (γ t).im ^ 2 ≤ 4*t := by
  intro t ht
  let w : ℝ → ℂ := fun y => (U t:ℂ)+(y:ℂ)*Complex.I
  let z : ℝ → ℂ := fun y => f t (w y)
  have hw (y : ℝ) (hy : 0 < y) : w y ∈ halfPlane := by simpa [w,halfPlane] using hy
  have hz (y : ℝ) (hy : 0 < y) : z y ∈ localizationDomain γ t :=
    h.2.2.2.2.2.2.2.2.1 t ht.1 (hw y hy)
  have he (y : ℝ) (hy : 0 < y) : g t (z y) = w y :=
    h.2.2.2.2.2.2.2.2.2.2.1 t ht.1 _ (hw y hy)
  have hlim : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 (γ t)) :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2 t ht.1
  have hleft (y : ℝ) (hy : 0 < y) : m ≤ (z y).re :=
    h.initial_real_ge ht.1 (hz y hy)
      (fun s hs => (hb s ⟨hs.1,hs.2.trans ht.2⟩).1)
      (by simpa [he y hy,w] using (hb t ht).1)
  have hright (y : ℝ) (hy : 0 < y) : (z y).re ≤ M :=
    h.initial_real_le ht.1 (hz y hy)
      (fun s hs => (hb s ⟨hs.1,hs.2.trans ht.2⟩).2)
      (by simpa [he y hy,w] using (hb t ht).2)
  have hheight (y : ℝ) (hy : 0 < y) : (z y).im^2 ≤ y^2+4*t := by
    simpa [he y hy,w] using h.initial_height_sq_le ht.1 (hz y hy)
  refine ⟨ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim) ?_,
    le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim) ?_,?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using hleft y hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using hright y hy
  · have hr : Tendsto (fun y : ℝ => y^2+4*t) (𝓝[>] (0:ℝ)) (𝓝 (4*t)) := by
      simpa using (show ContinuousAt (fun y : ℝ => y^2+4*t) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto ((Complex.continuous_im.continuousAt.tendsto.comp hlim).pow 2) hr
    filter_upwards [self_mem_nhdsWithin] with y hy using hheight y hy

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter
open scoped Topology
namespace SLEExactGauge
namespace IsLoewnerTraceUsing
variable {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma earlier_real_le (h : IsLoewnerTraceUsing U γ g f)
    {S T M : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hU : ∀ t ∈ Icc S T, U t ≤ M) (hend : (g T z).re ≤ M) : (g S z).re ≤ M := by
  have hT : 0 ≤ T := hS.trans hST
  let R : ℝ → ℝ := fun s => (g (T-s) z).re
  have hc : ContinuousOn R (Icc 0 (T-S)) :=
    (Complex.continuous_re.comp_continuousOn (h.continuous_eval hT hz)).comp
      (continuous_const.sub continuous_id).continuousOn (fun s hs => by constructor <;> linarith [hs.1,hs.2])
  have hd (s : ℝ) (hs : s ∈ Ico 0 (T-S)) : HasDerivAt R
      (-2*((g (T-s) z).re-U (T-s))/Complex.normSq (g (T-s) z-(U (T-s):ℂ))) s := by
    have he := (h.hasDerivAt_real (by linarith [hs.2] : 0 < T-s)
      (survivingDomain_mono (by linarith [hs.1]) hz)).comp s
      ((hasDerivAt_id s).const_sub T)
    simpa [R,neg_div,Function.comp_def] using he
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb := image_le_of_deriv_right_lt_deriv_boundary hc
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (B:=fun _ => M+ε) (B':=fun _ => 0)
    (by dsimp [R]; simpa using hend.trans (by linarith : M ≤ M+ε))
    (fun _ => hasDerivAt_const _ _) (fun s hs he => ?_) (x:=T-S) ⟨sub_nonneg.2 hST,le_rfl⟩
  · simpa [R,sub_sub_cancel] using hb
  · have hden := Complex.normSq_pos.2
      (h.centered_ne_zero (t:=T-s) (z:=z) (by linarith [hs.2]) (survivingDomain_mono (by linarith [hs.1]) hz))
    have hh := hU (T-s) (by constructor <;> linarith [hs.1,hs.2])
    dsimp [R] at he
    exact div_neg_of_neg_of_pos (by nlinarith) hden

lemma earlier_real_ge (h : IsLoewnerTraceUsing U γ g f)
    {S T m : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hU : ∀ t ∈ Icc S T, m ≤ U t) (hend : m ≤ (g T z).re) : m ≤ (g S z).re := by
  have hT : 0 ≤ T := hS.trans hST
  let R : ℝ → ℝ := fun s => -(g (T-s) z).re
  have hc : ContinuousOn R (Icc 0 (T-S)) :=
    (Complex.continuous_re.comp_continuousOn (h.continuous_eval hT hz)).neg.comp
      (continuous_const.sub continuous_id).continuousOn (fun s hs => by constructor <;> linarith [hs.1,hs.2])
  have hd (s : ℝ) (hs : s ∈ Ico 0 (T-S)) : HasDerivAt R
      (2*((g (T-s) z).re-U (T-s))/Complex.normSq (g (T-s) z-(U (T-s):ℂ))) s := by
    have he := ((h.hasDerivAt_real (by linarith [hs.2] : 0 < T-s)
      (survivingDomain_mono (by linarith [hs.1]) hz)).comp s
      ((hasDerivAt_id s).const_sub T)).neg
    convert he using 1
    all_goals first | rfl | norm_num
  have hn : -(g S z).re ≤ -m := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hb := image_le_of_deriv_right_lt_deriv_boundary hc
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (B:=fun _ => -m+ε) (B':=fun _ => 0)
      (by dsimp [R]; simpa using (show -(g T z).re ≤ -m+ε by linarith))
      (fun _ => hasDerivAt_const _ _) (fun s hs he => ?_) (x:=T-S) ⟨sub_nonneg.2 hST,le_rfl⟩
    · simpa [R,sub_sub_cancel] using hb
    · have hden := Complex.normSq_pos.2
        (h.centered_ne_zero (t:=T-s) (z:=z) (by linarith [hs.2]) (survivingDomain_mono (by linarith [hs.1]) hz))
      have hh := hU (T-s) (by constructor <;> linarith [hs.1,hs.2])
      dsimp [R] at he
      exact div_neg_of_neg_of_pos (by nlinarith) hden
  linarith

lemma earlier_height_sq_le (h : IsLoewnerTraceUsing U γ g f)
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    (g S z).im^2 ≤ (g T z).im^2+4*(T-S) := by
  have hT : 0 ≤ T := hS.trans hST
  have hcont := (h.continuous_eval hT hz).mono (Icc_subset_Icc hS le_rfl)
  have hm : MonotoneOn (fun s => (g s z).im^2+4*s) (Icc S T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc S T)
      (((Complex.continuous_im.comp_continuousOn hcont).pow 2).add
        (continuous_const.mul continuous_id).continuousOn)
      (f':=fun t => -4*(g t z).im^2/Complex.normSq (g t z-(U t:ℂ))+4)
    · intro t ht
      rw [interior_Icc] at ht
      convert (((h.hasDerivAt_height (hS.trans_lt ht.1) (survivingDomain_mono ht.2.le hz)).pow 2).add
        ((hasDerivAt_id t).const_mul 4)).hasDerivWithinAt using 1
      all_goals first | rfl | (norm_num; ring)
    · intro t ht
      rw [interior_Icc] at ht
      have hd := Complex.normSq_pos.2 (h.centered_ne_zero (hS.trans ht.1.le) (survivingDomain_mono ht.2.le hz))
      have he : (g t z).im^2 ≤ Complex.normSq (g t z-(U t:ℂ)) := by
        simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
        nlinarith [sq_nonneg ((g t z).re-U t)]
      have hb : -4*(g t z).im^2/Complex.normSq (g t z-(U t:ℂ)) ≥ -4 := by
        exact (le_div_iff₀ hd).2 (by nlinarith)
      linarith
  have hh := hm ⟨le_rfl,hST⟩ ⟨hST,le_rfl⟩ hST
  linarith

lemma later_real_le (h : IsLoewnerTraceUsing U γ g f)
    {S T M ε : ℝ} (hS : 0 < S) (hST : S ≤ T) (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hU : ∀ t ∈ Icc S T, U t ≤ M) (hstart : (g S z).re ≤ M) :
    (g T z).re ≤ M+ε+(2/ε)*(T-S) := by
  have hc := Complex.continuous_re.comp_continuousOn
    ((h.continuous_eval (hS.le.trans hST) hz).mono (Icc_subset_Icc hS.le le_rfl))
  have hd (t : ℝ) (ht : t ∈ Ico S T) :=
    h.hasDerivAt_real (hS.trans_le ht.1) (survivingDomain_mono ht.2.le hz)
  apply image_le_of_deriv_right_lt_deriv_boundary hc
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (B:=fun t => M+ε+(2/ε)*(t-S)) (B':=fun _ => 2/ε)
    (by simpa using hstart.trans (show M ≤ M+ε by linarith))
    (fun t => by simpa using (((hasDerivAt_id t).sub_const S).const_mul (2/ε)).const_add (M+ε))
    (fun t ht he => ?_) ⟨hST,le_rfl⟩
  have hden := Complex.normSq_pos.2 (h.centered_ne_zero (hS.le.trans ht.1) (survivingDomain_mono ht.2.le hz))
  have hu := hU t ⟨ht.1,ht.2.le⟩
  have hx : ε ≤ (g t z).re-U t := by
    have hh : 0 ≤ (2/ε)*(t-S) := mul_nonneg (by positivity) (sub_nonneg.2 ht.1)
    dsimp only [Function.comp_apply] at he
    linarith
  have hy := h.im_pos (hS.le.trans ht.1) (survivingDomain_mono ht.2.le hz)
  rw [div_lt_div_iff₀ hden hε]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  nlinarith [sq_pos_of_pos hy, mul_nonneg (sub_nonneg.2 hx) (show 0 ≤ (g t z).re-U t by linarith)]

lemma later_real_ge (h : IsLoewnerTraceUsing U γ g f)
    {S T m ε : ℝ} (hS : 0 < S) (hST : S ≤ T) (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ localizationDomain γ T)
    (hU : ∀ t ∈ Icc S T, m ≤ U t) (hstart : m ≤ (g S z).re) :
    m-ε-(2/ε)*(T-S) ≤ (g T z).re := by
  have hc := (Complex.continuous_re.comp_continuousOn
    ((h.continuous_eval (hS.le.trans hST) hz).mono (Icc_subset_Icc hS.le le_rfl))).neg
  have hd (t : ℝ) (ht : t ∈ Ico S T) :=
    (h.hasDerivAt_real (hS.trans_le ht.1) (survivingDomain_mono ht.2.le hz)).neg
  have hh := image_le_of_deriv_right_lt_deriv_boundary hc
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (B:=fun t => -m+ε+(2/ε)*(t-S)) (B':=fun _ => 2/ε)
    (by simpa using (show -(g S z).re ≤ -m+ε by linarith))
    (fun t => by simpa using (((hasDerivAt_id t).sub_const S).const_mul (2/ε)).const_add (-m+ε))
    (fun t ht he => ?_) (x:=T) ⟨hST,le_rfl⟩
  · dsimp only [Function.comp_apply, Pi.neg_apply] at hh
    linarith
  · have hden := Complex.normSq_pos.2 (h.centered_ne_zero (hS.le.trans ht.1) (survivingDomain_mono ht.2.le hz))
    have hu := hU t ⟨ht.1,ht.2.le⟩
    have hx : ε ≤ U t-(g t z).re := by
      have hh : 0 ≤ (2/ε)*(t-S) := mul_nonneg (by positivity) (sub_nonneg.2 ht.1)
      dsimp only [Function.comp_apply, Pi.neg_apply] at he
      linarith
    have hy := h.im_pos (hS.le.trans ht.1) (survivingDomain_mono ht.2.le hz)
    rw [← neg_div,div_lt_div_iff₀ hden hε]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
    nlinarith [sq_pos_of_pos hy, mul_nonneg (sub_nonneg.2 hx) (show 0 ≤ U t-(g t z).re by linarith)]

theorem earlier_tip_rectangle (h : IsLoewnerTraceUsing U γ g f)
    {S T m M : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hlive : γ T ∈ localizationDomain γ S)
    (hb : ∀ t ∈ Icc S T, m ≤ U t ∧ U t ≤ M) :
    m ≤ (g S (γ T)).re ∧ (g S (γ T)).re ≤ M ∧ (g S (γ T)).im ^ 2 ≤ 4*(T-S) := by
  have hT : 0 ≤ T := hS.trans hST
  let w : ℝ → ℂ := fun y => (U T:ℂ)+(y:ℂ)*Complex.I
  let z : ℝ → ℂ := fun y => f T (w y)
  have hw (y : ℝ) (hy : 0 < y) : w y ∈ halfPlane := by simpa [w,halfPlane] using hy
  have hz (y : ℝ) (hy : 0 < y) : z y ∈ localizationDomain γ T :=
    h.2.2.2.2.2.2.2.2.1 T hT (hw y hy)
  have he (y : ℝ) (hy : 0 < y) : g T (z y) = w y :=
    h.2.2.2.2.2.2.2.2.2.2.1 T hT _ (hw y hy)
  have hlim : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 (γ T)) :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2 T hT
  have hlim' : Tendsto (fun y => g S (z y)) (𝓝[>] (0:ℝ)) (𝓝 (g S (γ T))) :=
    (h.analytic_eval hS hlive).continuousAt.tendsto.comp hlim
  have hleft (y : ℝ) (hy : 0 < y) : m ≤ (g S (z y)).re :=
    h.earlier_real_ge hS hST (hz y hy) (fun s hs => (hb s hs).1)
      (by simpa [he y hy,w] using (hb T ⟨hST,le_rfl⟩).1)
  have hright (y : ℝ) (hy : 0 < y) : (g S (z y)).re ≤ M :=
    h.earlier_real_le hS hST (hz y hy) (fun s hs => (hb s hs).2)
      (by simpa [he y hy,w] using (hb T ⟨hST,le_rfl⟩).2)
  have hheight (y : ℝ) (hy : 0 < y) : (g S (z y)).im^2 ≤ y^2+4*(T-S) := by
    simpa [he y hy,w] using h.earlier_height_sq_le hS hST (hz y hy)
  refine ⟨ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim') ?_,
    le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hlim') ?_,?_⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using hleft y hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using hright y hy
  · have hr : Tendsto (fun y : ℝ => y^2+4*(T-S)) (𝓝[>] (0:ℝ)) (𝓝 (4*(T-S))) := by
      simpa using (show ContinuousAt (fun y : ℝ => y^2+4*(T-S)) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto ((Complex.continuous_im.continuousAt.tendsto.comp hlim').pow 2) hr
    filter_upwards [self_mem_nhdsWithin] with y hy using hheight y hy

end IsLoewnerTraceUsing

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge

lemma ball_subset_localizationDomain {γ : ℝ → ℂ} {t : ℝ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : z ∈ localizationDomain γ t)
    (hfree : ball z r ⊆ halfPlane \ localizationSegment γ 0 t) :
    ball z r ⊆ localizationDomain γ t := by
  have hc := (convex_ball z r).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hr) hfree
  intro w hw
  refine ⟨hfree hw,?_⟩
  rw [← connectedComponentIn_eq (hc hw)]
  exact hz.2

lemma first_disk_hit_free {γ : ℝ → ℂ} {T r : ℝ} {z : ℂ}
    (hr : 0 < r) (hball : closedBall z r ⊆ halfPlane)
    (hlive : z ∈ localizationDomain γ T) (hhit : dist (γ T) z = r)
    (hpre : ∀ t ∈ Ico 0 T, r < dist (γ t) z) :
    ball z r ⊆ localizationDomain γ T ∧ ∀ s ∈ Ico 0 T,
      closedBall z r ⊆ localizationDomain γ s := by
  constructor
  · apply ball_subset_localizationDomain hr hlive
    intro w hw
    refine ⟨hball (ball_subset_closedBall hw),?_⟩
    rintro ⟨t,ht,he⟩
    subst w
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (not_le_of_gt (hpre t ⟨ht.1,hlt⟩)) (mem_ball.1 hw).le
    · exact (ne_of_lt (mem_ball.1 hw)) hhit
  · intro s hs
    apply closedBall_subset_survivingDomain hr.le (survivingDomain_mono hs.2.le hlive)
    intro w hw
    refine ⟨hball hw,?_⟩
    rintro ⟨t,ht,he⟩
    subst w
    exact (not_le_of_gt (hpre t ⟨ht.1,ht.2.trans_lt hs.2⟩)) (mem_closedBall.1 hw)

lemma first_disk_hit_live_before {γ : ℝ → ℂ} {T r : ℝ} {z : ℂ}
    (hr : 0 < r) (hball : closedBall z r ⊆ halfPlane)
    (hlive : z ∈ localizationDomain γ T) (hhit : dist (γ T) z = r)
    (hpre : ∀ t ∈ Ico 0 T, r < dist (γ t) z) :
    ∀ s ∈ Ico 0 T, γ T ∈ localizationDomain γ s := by
  intro s hs
  exact (first_disk_hit_free hr hball hlive hhit hpre).2 s hs (mem_closedBall.2 hhit.le)

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge
namespace IsLoewnerTraceUsing
variable {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

theorem fresh_tip_access (h : IsLoewnerTraceUsing U γ g f) {T : ℝ}
    (hT : 0 < T) (hU : ContinuousOn U (Icc 0 T))
    (hlive : ∀ s ∈ Ico 0 T, γ T ∈ localizationDomain γ s) :
    Tendsto (g T) (𝓝[localizationDomain γ T] (γ T)) (𝓝 (U T : ℂ)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let e := ε/10
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨η,hη,hηU⟩ := Metric.continuousWithinAt_iff.1
    (hU.continuousWithinAt ⟨hT.le,le_rfl⟩) e he
  let δ := min η (e^2/8)
  have hδ : 0 < δ := lt_min hη (by positivity)
  obtain ⟨S,hSlo,hST⟩ := exists_between (max_lt hT (sub_lt_self T hδ))
  have hS : 0 < S := (le_max_left _ _).trans_lt hSlo
  have hSδ : T-δ < S := (le_max_right _ _).trans_lt hSlo
  have htimeη : T-S < η := (by linarith : T-S < δ).trans_le (min_le_left _ _)
  have htimee : T-S < e^2/8 := (by linarith : T-S < δ).trans_le (min_le_right _ _)
  have hUb (s : ℝ) (hs : s ∈ Icc S T) : U T-e ≤ U s ∧ U s ≤ U T+e := by
    have hh := hηU ⟨hS.le.trans hs.1,hs.2⟩ (show dist s T < η by
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.2 hs.2)]
      linarith [hs.1])
    rw [Real.dist_eq] at hh
    have ha := abs_lt.1 hh
    constructor <;> linarith [ha.1,ha.2]
  have htip := h.earlier_tip_rectangle hS.le hST.le (hlive S ⟨hS.le,hST⟩) hUb
  have htipim : (g S (γ T)).im < e := by
    have hy := h.im_pos hS.le (hlive S ⟨hS.le,hST⟩)
    nlinarith [htip.2.2]
  have hevent : ∀ᶠ w in 𝓝[localizationDomain γ T] (γ T),
      dist (g S w) (g S (γ T)) < e :=
    (Metric.tendsto_nhds.1 (h.analytic_eval hS.le (hlive S ⟨hS.le,hST⟩)).continuousAt.tendsto e he).filter_mono nhdsWithin_le_nhds
  filter_upwards [hevent,self_mem_nhdsWithin] with w hnear hw
  rw [dist_eq_norm] at hnear
  have hrnear : |(g S w).re-(g S (γ T)).re| < e := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (g S w-g S (γ T))).trans_lt hnear
  have hinear : |(g S w).im-(g S (γ T)).im| < e := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (g S w-g S (γ T))).trans_lt hnear
  have hstartlo : U T-2*e ≤ (g S w).re := by nlinarith [(abs_lt.1 hrnear).1,htip.1]
  have hstarthi : (g S w).re ≤ U T+2*e := by nlinarith [(abs_lt.1 hrnear).2,htip.2.1]
  have hlo := h.later_real_ge hS hST.le he hw
    (fun s hs => (show U T-2*e ≤ U T-e by linarith).trans (hUb s hs).1) hstartlo
  have hhi := h.later_real_le hS hST.le he hw
    (fun s hs => (hUb s hs).2.trans (show U T+e ≤ U T+2*e by linarith)) hstarthi
  have hdt : (2/e)*(T-S) < e := by
    calc
      _ = 2*(T-S)/e := by ring
      _ < e := (div_lt_iff₀ he).2 (by nlinarith)
  have hre : |(g T w).re-U T| < 4*e := by
    rw [abs_lt]
    constructor <;> linarith
  have him : (g T w).im < 2*e := by
    have hm := h.height_antitone hT.le hw ⟨hS.le,hST.le⟩ ⟨hT.le,le_rfl⟩ hST.le
    linarith [(abs_lt.1 hinear).2]
  have himabs : |(g T w).im| < 2*e := by rw [abs_of_pos (h.im_pos hT.le hw)]; exact him
  rw [dist_eq_norm]
  calc
    _ ≤ |(g T w).re-U T|+|(g T w).im| := by
      simpa only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] using
        Complex.norm_le_abs_re_add_abs_im (g T w-(U T:ℂ))
    _ < 6*e := by linarith
    _ < ε := by dsimp [e]; linarith

end IsLoewnerTraceUsing

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge

theorem first_disk_hit_access {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing U γ g f) {T r : ℝ} {z : ℂ}
    (hT : 0 < T) (hr : 0 < r) (hU : ContinuousOn U (Icc 0 T))
    (hball : Metric.closedBall z r ⊆ halfPlane)
    (hlive : z ∈ localizationDomain γ T)
    (hhit : dist (γ T) z = r)
    (hpre : ∀ t ∈ Ico 0 T, r < dist (γ t) z) :
    Tendsto (g T) (𝓝[localizationDomain γ T] (γ T)) (𝓝 (U T : ℂ)) :=
  h.fresh_tip_access hT hU (first_disk_hit_live_before hr hball hlive hhit hpre)

theorem first_disk_hit_access_path {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing U γ g f) {T r : ℝ} {z : ℂ}
    (hT : 0 < T) (hr : 0 < r) (hU : ContinuousOn U (Icc 0 T))
    (hball : closedBall z r ⊆ halfPlane) (hlive : z ∈ localizationDomain γ T)
    (hhit : dist (γ T) z = r) (hpre : ∀ t ∈ Ico 0 T, r < dist (γ t) z) :
    ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 1) ∧ η 0 = 0 ∧ ‖η 1‖ = 1 ∧
      (∀ u ∈ Ioc 0 1, 0 < (η u).im ∧
        f T ((U T:ℂ)+(‖g T z-(U T:ℂ)‖:ℂ)*η u) =
          z+((1-u:ℝ):ℂ)*(γ T-z)) := by
  classical
  let R : ℝ → ℂ := fun u => z+((1-u:ℝ):ℂ)*(γ T-z)
  let N := ‖g T z-(U T:ℂ)‖
  let H : ℝ → ℂ := fun u => ((N⁻¹:ℝ):ℂ)*(g T (R u)-(U T:ℂ))
  let η := Function.update H 0 0
  have hN : 0 < N := norm_pos_iff.2 (h.centered_ne_zero hT.le hlive)
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hR0 : R 0 = γ T := by simp [R]
  have hR1 : R 1 = z := by simp [R]
  have hRc : Continuous R := by dsimp [R]; fun_prop
  have hRball (u : ℝ) (hu : u ∈ Ioc 0 1) : R u ∈ ball z r := by
    have hdist : dist (R u) z = (1-u)*r := by
      rw [dist_eq_norm]
      dsimp [R]
      rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 hu.2)]
      rw [← dist_eq_norm,hhit]
    rw [mem_ball,hdist]
    nlinarith [mul_pos hu.1 hr]
  have hRl (u : ℝ) (hu : u ∈ Ioc 0 1) : R u ∈ localizationDomain γ T :=
    (first_disk_hit_free hr hball hlive hhit hpre).1 (hRball u hu)
  have hlimR : Tendsto R (𝓝[Icc (0:ℝ) 1 \ {0}] 0) (𝓝[localizationDomain γ T] (γ T)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_,?_⟩
    · have hh : Tendsto R (𝓝[Icc (0:ℝ) 1 \ {0}] 0) (𝓝 (R 0)) := hRc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rw [hR0] at hh
      exact hh
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact hRl u ⟨lt_of_le_of_ne hu.1.1 (Ne.symm hu.2),hu.1.2⟩
  have hlimG := (first_disk_hit_access h hT hr hU hball hlive hhit hpre).comp hlimR
  have hηcont : ContinuousOn η (Icc 0 1) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      rw [show η = Function.update H 0 0 from rfl,continuousWithinAt_update_same]
      simpa only [H,Function.comp_def,sub_self,mul_zero] using (hlimG.sub (tendsto_const_nhds (x := (U T:ℂ)))).const_mul ((N⁻¹:ℝ):ℂ)
    · have hcH : ContinuousAt H u := by
        exact continuousAt_const.mul (((h.analytic_eval hT.le (hRl u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩)).continuousAt.comp hRc.continuousAt).sub continuousAt_const)
      apply hcH.continuousWithinAt.congr_of_eventuallyEq_of_mem _ hu
      have hne : ∀ᶠ v in 𝓝 u, v ≠ (0:ℝ) := isOpen_ne.mem_nhds hu0
      filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with v hv
      exact Function.update_of_ne hv _ _
  refine ⟨η,hηcont,by simp [η],?_,?_⟩
  · rw [show η 1 = H 1 by simp [η]]
    dsimp [H]
    rw [hR1,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hN)]
    exact inv_mul_cancel₀ hN.ne'
  · intro u hu
    have hη : η u = H u := Function.update_of_ne (ne_of_gt hu.1) _ _
    rw [hη]
    constructor
    · have hy := h.im_pos hT.le (hRl u hu)
      dsimp [H]
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,
        add_zero,Complex.sub_im,sub_zero] using mul_pos (inv_pos.2 hN) hy
    · have heq : (U T:ℂ)+(N:ℂ)*H u = g T (R u) := by
        dsimp [H]
        rw [Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ hNc,one_mul]
        ring
      change f T ((U T:ℂ)+(N:ℂ)*H u) = R u
      rw [heq]
      exact h.2.2.2.2.2.2.2.2.2.1 T hT.le _ (hRl u hu)

end SLEExactGauge

end

end

end OAI
