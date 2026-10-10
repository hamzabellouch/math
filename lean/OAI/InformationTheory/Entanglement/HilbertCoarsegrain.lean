import OAI.InformationTheory.Entanglement.HilbertLawAlgebra

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι a d : Type*} [Fintype a] [Fintype d] [DecidableEq d]

def classicalPush (b : HilbertBasis ι ℂ H) (f : a→d) (W : a→PositiveHilbertMeasure T H b) :
    d→PositiveHilbertMeasure T H b :=
  fun j => PositiveHilbertMeasure.familySum (Finset.univ.filter (fun i => f i=j)) W
omit [Fintype d] in
lemma classicalPush_value (b : HilbertBasis ι ℂ H) (f : a→d) (W : a→PositiveHilbertMeasure T H b)
    (j : d) (s : Set T) :
    (classicalPush b f W j).value s=∑ i∈Finset.univ.filter (fun i => f i=j), (W i).value s := rfl
lemma classicalPush_trace (b : HilbertBasis ι ℂ H) (f : a→d) (W : a→PositiveHilbertMeasure T H b)
    (s : Set T) : ∑ j, (classicalPush b f W j).traceMeasure s=∑ i, (W i).traceMeasure s := by
  simp only [classicalPush,PositiveHilbertMeasure.familySum,Measure.finsetSum_apply]
  exact Finset.sum_fiberwise _ f _

theorem classicalPush_contract (b : HilbertBasis ι ℂ H) (f : a→d)
    (W V : a→PositiveHilbertMeasure T H b) :
    hilbertClassicalDistance b (classicalPush b f W) (classicalPush b f V)≤hilbertClassicalDistance b W V := by
  unfold hilbertClassicalDistance
  calc
    _ ≤ ∑ j, ∑ i∈Finset.univ.filter (fun i => f i=j),
        hilbertVariation b (fun s => (W i).value s-(V i).value s) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [classicalPush_value,← Finset.sum_sub_distrib]
      exact hilbertVariation_sum_le b _ _ (fun i hi s hs =>
        (positive_difference_traceClass b ((W i).positive s hs) ((V i).positive s hs)).1)
    _ = _ := Finset.sum_fiberwise _ f _

def localClassicalPush {a₁ a₂ d₁ d₂ : Type*}
    [Fintype a₁] [Fintype a₂] [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (b : HilbertBasis ι ℂ H) (f : a₁→d₁) (g : a₂→d₂)
    (W : (a₁×a₂)→PositiveHilbertMeasure T H b) : (d₁×d₂)→PositiveHilbertMeasure T H b :=
  classicalPush b (Prod.map f g) W

def abortToZero : Option (Fin 2) → Fin 2 := fun x => x.getD 0
lemma abortToZero_none : abortToZero none=0 := rfl
lemma abortToZero_some (i : Fin 2) : abortToZero (some i)=i := rfl

end SecretKey

end

end OAI
