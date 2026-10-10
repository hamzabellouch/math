import OAI.Probability.InvariantIsing.Fields.FieldScalarOrder
import OAI.Probability.InvariantIsing.Fields.FieldScalarOverlap
import OAI.Probability.InvariantIsing.Fields.FieldEvenTransition

namespace OAI

/-! Ordered even second-moment tests propagated through the actual
finite tilted position chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_shape (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hFe : Function.Even F)
    (ha : Measurable a) (hao : Function.Odd a)
    (ham : MonotoneOn a (Ici 0)) (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z)
    (haB : ∀ z, |a z| ≤ 1) :
    ∀ i, Function.Even (fieldScalarSquares L F a i) ∧
      MonotoneOn (fieldScalarSquares L F a i) (Ici 0) := by
  have hsq (f : ℝ → ℝ) (ho : Function.Odd f)
      (hm : MonotoneOn f (Ici 0)) (hp : ∀ z ∈ Ici (0 : ℝ), 0 ≤ f z) :
      Function.Even (fun z => (f z) ^ 2) ∧ MonotoneOn (fun z => (f z) ^ 2) (Ici 0) := by
    refine ⟨fun z => by dsimp only; rw [ho z, neg_sq], ?_⟩
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (hp x hx) (hm hx hy hxy) 2
  induction L with
  | nil => intro i; exact hsq a hao ham hap
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    have he := fieldScalarValue_even L ht hF hG hFe
    have hs := fieldScalarMean_shape (av :: L) hL hF hG hFe ha hao ham hap haB
    have hr := fieldScalarSquares_regular L ht hF hG ha haB
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hsq _ hs.1 hs.2.1 hs.2.2
    · have hj := ih ht j
      have hb (z : ℝ) : |fieldScalarSquares L F a j z| ≤ 1 := by
        rw [abs_of_nonneg ((hr j).2 z).1]
        exact ((hr j).2 z).2
      exact ⟨fieldSpinTransition_even av.1 av.2 hv.1 he (hr j).1 hj.1,
        fieldSpinTransition_even_monotone av.1 av.2 hv.1 he hv.2
          (hr j).1 hj.1 hj.2 hb⟩

lemma fieldScalarSquares_order (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F G a b : ℝ → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (hFg : HasLinearGrowth F) (hGg : HasLinearGrowth G)
    (hFe : Function.Even F) (hGe : Function.Even G)
    (hFG : MonotoneOn (fun z => G z - F z) (Ici 0))
    (ha : Measurable a) (hb : Measurable b)
    (hao : Function.Odd a) (hbo : Function.Odd b)
    (ham : MonotoneOn a (Ici 0)) (hbm : MonotoneOn b (Ici 0))
    (hap : ∀ z ∈ Ici (0 : ℝ), 0 ≤ a z) (hbp : ∀ z ∈ Ici (0 : ℝ), 0 ≤ b z)
    (haB : ∀ z, |a z| ≤ 1) (hbB : ∀ z, |b z| ≤ 1)
    (hab : ∀ z ∈ Ici (0 : ℝ), a z ≤ b z) :
    ∀ i z, fieldScalarSquares L F a i z ≤ fieldScalarSquares L G b i z := by
  induction L with
  | nil =>
    intro i z
    have heF : (a z) ^ 2 = (a |z|) ^ 2 := by
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
      · rw [abs_of_nonpos hz, hao z, neg_sq]
    have heG : (b z) ^ 2 = (b |z|) ^ 2 := by
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
      · rw [abs_of_nonpos hz, hbo z, neg_sq]
    change (a z) ^ 2 ≤ (b z) ^ 2
    rw [heF, heG]
    exact pow_le_pow_left₀ (hap _ (abs_nonneg z)) (hab _ (abs_nonneg z)) 2
  | cons av L ih =>
    have ht (bv) (hc : bv ∈ L) := hL bv (List.mem_cons_of_mem av hc)
    have hFr := fieldScalarValue_regular L ht hF hFg
    have hGr := fieldScalarValue_regular L ht hG hGg
    have hFs := fieldScalarSquares_shape (av :: L) hL hF hFg hFe ha hao ham hap haB
    have hGs := fieldScalarSquares_shape (av :: L) hL hG hGg hGe hb hbo hbm hbp hbB
    have hms := fieldScalarMean_shape (av :: L) hL hF hFg hFe ha hao ham hap haB
    have hmorder := fieldScalarMean_order (av :: L) hL hF hG hFg hGg hFe hGe hFG
      ha hb hao hbo ham hbm hap hbp haB hbB hab
    have hFreg := fieldScalarSquares_regular L ht hF hFg ha haB
    have hGreg := fieldScalarSquares_regular L ht hG hGg hb hbB
    intro i z
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← field_even_abs (hFs 0).1 z, ← field_even_abs (hGs 0).1 z]
      simp only [fieldScalarSquares_zero]
      exact pow_le_pow_left₀ (hms.2.2 _ (abs_nonneg z)) (hmorder _ (abs_nonneg z)) 2
    · have hshape := fieldScalarSquares_shape L ht hF hFg hFe ha hao ham hap haB j
      have hgshape := fieldScalarSquares_shape L ht hG hGg hGe hb hbo hbm hbp hbB j
      have hFb (u : ℝ) : |fieldScalarSquares L F a j u| ≤ 1 := by
        rw [abs_of_nonneg ((hFreg j).2 u).1]
        exact ((hFreg j).2 u).2
      have hGb (u : ℝ) : |fieldScalarSquares L G b j u| ≤ 1 := by
        rw [abs_of_nonneg ((hGreg j).2 u).1]
        exact ((hGreg j).2 u).2
      exact fieldSpinTransition_even_order av.2 (hL av List.mem_cons_self).le
        hFr.1 hGr.1 (fieldScalarValue_even L ht hF hFg hFe)
        (fieldScalarValue_even L ht hG hGg hGe) hFr.2 hGr.2
        (fieldScalarValue_difference_monotone L ht hF hG hFg hGg hFe hGe hFG)
        (hFreg j).1 (hGreg j).1 hshape.1 hgshape.1 hshape.2 hFb hGb
        (fun u _ => ih ht j u) z

end InvariantIsing

end

end OAI
