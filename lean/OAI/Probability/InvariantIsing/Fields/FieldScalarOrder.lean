import OAI.Probability.InvariantIsing.Fields.FieldScalarChain

namespace OAI

/-! Radial order of the actual scalar backward values and physical spin
means, with covariance increments fixed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_even (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (he : Function.Even F) :
    Function.Even (fieldScalarValue L F) := by
  induction L with
  | nil => exact he
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldScalarValue_regular L ht hF hG
    exact gaussianOperator_even av.1 av.2 hr.1 (ih ht)

lemma fieldScalarValue_difference_monotone (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F G : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0)) :
    MonotoneOn (fun z => fieldScalarValue L G z - fieldScalarValue L F z) (Ici 0) := by
  induction L with
  | nil => exact hFG
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hFr := fieldScalarValue_regular L ht hF hFg
    have hGr := fieldScalarValue_regular L ht hG hGg
    exact gaussianOperator_difference_monotone av.2 (hL av List.mem_cons_self).le
      _ _ hFr.1 hGr.1 (fieldScalarValue_even L ht hF hFg hFe)
      (fieldScalarValue_even L ht hG hGg hGe) hFr.2 hGr.2 (ih ht)

lemma fieldScalarMean_shape (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hFe : Function.Even F)
    (ha : Measurable a) (hao : Function.Odd a)
    (ham : MonotoneOn a (Ici 0)) (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z)
    {K : ℝ} (haB : ∀ z, |a z| ≤ K) :
    Function.Odd (fieldScalarMean L F a) ∧
      MonotoneOn (fieldScalarMean L F a) (Ici 0) ∧
      ∀ z ∈ Ici (0 : ℝ), 0 ≤ fieldScalarMean L F a z := by
  induction L with
  | nil => exact ⟨hao, ham, hap⟩
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldScalarValue_regular L ht hF hG
    have hm := fieldScalarMean_regular L ht hF hG ha haB
    have hs := ih ht
    have he := fieldScalarValue_even L ht hF hG hFe
    refine ⟨fieldSpinTransition_odd av.1 av.2 hr.1 he hm.1 hs.1, ?_, ?_⟩
    · exact fieldSpinTransition_monotone (hL av List.mem_cons_self).le av.2
        hr.1 he hr.2 hm.1 hs.1 hs.2.1 hs.2.2 hm.2
    · intro z hz
      exact fieldSpinTransition_nonneg av.1 av.2 hr.1 he hr.2 hm.1 hs.1 hs.2.2 hm.2 hz

lemma fieldScalarMean_order (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F G a b : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0))
    (ha : Measurable a) (hb : Measurable b)
    (hao : Function.Odd a) (hbo : Function.Odd b)
    (ham : MonotoneOn a (Ici 0)) (hbm : MonotoneOn b (Ici 0))
    (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z) (hbp : ∀ z ∈ Ici (0 : ℝ), 0 ≤ b z)
    {K : ℝ} (haB : ∀ z, |a z| ≤ K) (hbB : ∀ z, |b z| ≤ K)
    (hab : ∀ z ∈ Ici (0 : ℝ), a z ≤ b z) :
    ∀ z ∈ Ici (0 : ℝ), fieldScalarMean L F a z ≤ fieldScalarMean L G b z := by
  induction L with
  | nil => exact hab
  | cons av L ih =>
    have ht (bv) (hc : bv ∈ L) := hL bv (List.mem_cons_of_mem av hc)
    have hFr := fieldScalarValue_regular L ht hF hFg
    have hGr := fieldScalarValue_regular L ht hG hGg
    have hmr := fieldScalarMean_regular L ht hF hFg ha haB
    have hnr := fieldScalarMean_regular L ht hG hGg hb hbB
    have hms := fieldScalarMean_shape L ht hF hFg hFe ha hao ham hap haB
    have hns := fieldScalarMean_shape L ht hG hGg hGe hb hbo hbm hbp hbB
    intro z hz
    by_cases hv : av.2 = 0
    · simpa only [fieldScalarMean, hv, fieldSpinTransition_zero_variance] using ih ht z hz
    · exact field_gaussian_spin_transition_order av.2 hv (hL av List.mem_cons_self).le
        _ _ _ _ hFr.1 hGr.1 (fieldScalarValue_even L ht hF hFg hFe)
        (fieldScalarValue_even L ht hG hGg hGe) hFr.2 hGr.2
        (fieldScalarValue_difference_monotone L ht hF hG hFg hGg hFe hGe hFG)
        hmr.1 hnr.1 hms.1 hns.1 hms.2.1 hms.2.2 (ih ht) hmr.2 hnr.2 hz le_rfl

end InvariantIsing

end

end OAI
