import OAI.InformationTheory.Entanglement.HilbertChannel
import OAI.InformationTheory.Entanglement.HilbertLawFinite

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
lemma hilbertENorm_add_le (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H}
    (hA : HermitianTraceClass b A) (hB : HermitianTraceClass b B) :
    hilbertENorm b (A+B)≤hilbertENorm b A+hilbertENorm b B := by
  obtain ⟨hC,hc⟩ := hilbertTraceNorm_triangle b hA hB
  rw [hilbertENorm_eq b hC.2,hilbertENorm_eq b hA.2,hilbertENorm_eq b hB.2]
  exact (ENNReal.ofReal_le_ofReal hc).trans ENNReal.ofReal_add_le
lemma hilbertVariation_congr (b : HilbertBasis ι ℂ H) {F G : Set T→H→L[ℂ]H}
    (h : ∀ s, MeasurableSet s → F s=G s) : hilbertVariation b F=hilbertVariation b G := by
  unfold hilbertVariation
  congr 1
  funext P
  congr 1
  funext hm
  congr 1
  funext hd
  exact Finset.sum_congr rfl fun s hs => congrArg (hilbertENorm b) (h s (hm s hs))
lemma hilbertVariation_add_le (b : HilbertBasis ι ℂ H) (F G : Set T→H→L[ℂ]H)
    (hF : ∀ s, MeasurableSet s → HermitianTraceClass b (F s))
    (hG : ∀ s, MeasurableSet s → HermitianTraceClass b (G s)) :
    hilbertVariation b (fun s => F s+G s)≤hilbertVariation b F+hilbertVariation b G := by
  apply iSup_le; intro P
  apply iSup_le; intro hm
  apply iSup_le; intro hd
  calc
    _ ≤ ∑ s∈P, (hilbertENorm b (F s)+hilbertENorm b (G s)) :=
      Finset.sum_le_sum fun s hs => hilbertENorm_add_le b (hF s (hm s hs)) (hG s (hm s hs))
    _ = (∑ s∈P, hilbertENorm b (F s))+(∑ s∈P, hilbertENorm b (G s)) := Finset.sum_add_distrib
    _ ≤ hilbertVariation b F+hilbertVariation b G := add_le_add
      (le_iSup_of_le P (le_iSup_of_le hm (le_iSup_of_le hd le_rfl)))
      (le_iSup_of_le P (le_iSup_of_le hm (le_iSup_of_le hd le_rfl)))
lemma hilbertVariation_neg (b : HilbertBasis ι ℂ H) (F : Set T→H→L[ℂ]H) :
    hilbertVariation b (fun s => -F s)=hilbertVariation b F := by
  simp only [hilbertVariation,hilbertENorm,CFC.abs_neg]
lemma hilbertVariation_difference_comm (b : HilbertBasis ι ℂ H)
    (W V : PositiveHilbertMeasure T H b) :
    hilbertVariation b (fun s => W.value s-V.value s)=
      hilbertVariation b (fun s => V.value s-W.value s) := by
  calc
    _ = hilbertVariation b (fun s => -(V.value s-W.value s)) := by simp only [neg_sub]
    _ = _ := hilbertVariation_neg _ _

theorem hilbertVariation_difference_triangle (b : HilbertBasis ι ℂ H)
    (W V Z : PositiveHilbertMeasure T H b) :
    hilbertVariation b (fun s => W.value s-Z.value s)≤
      hilbertVariation b (fun s => W.value s-V.value s)+
      hilbertVariation b (fun s => V.value s-Z.value s) := by
  have he : (fun s => W.value s-Z.value s)=
      (fun s => (W.value s-V.value s)+(V.value s-Z.value s)) := by
    funext s; abel
  rw [he]
  exact hilbertVariation_add_le b _ _
    (fun s hs => (positive_difference_traceClass b (W.positive s hs) (V.positive s hs)).1)
    (fun s hs => (positive_difference_traceClass b (V.positive s hs) (Z.positive s hs)).1)

def hilbertClassicalDistance {a : Type*} [Fintype a] (b : HilbertBasis ι ℂ H)
    (W V : a→PositiveHilbertMeasure T H b) : ℝ≥0∞ :=
  ∑ i, hilbertVariation b (fun s => (W i).value s-(V i).value s)
lemma hilbertClassicalDistance_ne_top {a : Type*} [Fintype a] (b : HilbertBasis ι ℂ H)
    (W V : a→PositiveHilbertMeasure T H b) : hilbertClassicalDistance b W V≠⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro i hi
  exact hilbertVariation_difference_ne_top b (W i) (V i)
lemma hilbertClassicalDistance_triangle {a : Type*} [Fintype a] (b : HilbertBasis ι ℂ H)
    (W V Z : a→PositiveHilbertMeasure T H b) :
    hilbertClassicalDistance b W Z≤hilbertClassicalDistance b W V+hilbertClassicalDistance b V Z := by
  unfold hilbertClassicalDistance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i hi => hilbertVariation_difference_triangle b (W i) (V i) (Z i))
lemma hilbertClassicalDistance_le_two {a : Type*} [Fintype a] (b : HilbertBasis ι ℂ H)
    (W V : a→PositiveHilbertMeasure T H b)
    (hW : ∑ i, (W i).traceMeasure Set.univ=1) (hV : ∑ i, (V i).traceMeasure Set.univ=1) :
    hilbertClassicalDistance b W V≤2 := by
  apply (Finset.sum_le_sum (fun i hi => hilbertVariation_difference_le b (W i) (V i))).trans
  rw [Finset.sum_add_distrib,hW,hV]
  norm_num

end SecretKey

end

end OAI
