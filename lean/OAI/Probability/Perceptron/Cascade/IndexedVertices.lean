import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedCascadeRegular

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

@[reducible] def IndexedVertex : ℕ → Type
  | 0 => Empty
  | n+1 => ℕ × ℕ × (Unit ⊕ IndexedVertex n)

instance indexedVertex_countable (n : ℕ) : Countable (IndexedVertex n) := by
  induction n with
  | zero => dsimp [IndexedVertex]; infer_instance
  | succ n ih => dsimp [IndexedVertex]; infer_instance

def indexedMarksFromVertices {S : Type} [MeasurableSpace S] : (n : ℕ) →
    (IndexedVertex n → S) → IndexedCascadeMarks S n
  | 0,_ => ()
  | n+1,f => fun i j => (f (i,j,.inl ()),
      indexedMarksFromVertices n (fun v => f (i,j,.inr v)))

lemma indexedMarksFromVertices_measurable {S : Type} [MeasurableSpace S] (n : ℕ) :
    Measurable (indexedMarksFromVertices (S := S) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply (i,j,Sum.inl ())).prodMk
      (ih.comp (Measurable.of_eval fun vertex => measurable_pi_apply (i,j,Sum.inr vertex)))

lemma infinitePi_sumPiEquivProdPi {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.infinitePi μ).map (MeasurableEquiv.sumPiEquivProdPi X) =
      (Measure.infinitePi fun i => μ (.inl i)).prod
        (Measure.infinitePi fun i => μ (.inr i)) := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  exact (infinitePi_sumPiEquivProdPi_symm μ).symm

lemma indexedMarksFromVertices_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) :
    (Measure.infinitePi (fun _ : IndexedVertex n => (ν : Measure S))).map
      (indexedMarksFromVertices n) = indexedCascadeMarksLaw ν n := by
  induction n with
  | zero => simp [indexedMarksFromVertices,indexedCascadeMarksLaw,Measure.map_const]
  | succ n ih =>
    let Q := Measure.infinitePi (fun _ : Unit ⊕ IndexedVertex n => (ν : Measure S))
    let M := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))
    let a : (Unit ⊕ IndexedVertex n → S) → S×IndexedCascadeMarks S n := fun f =>
      (f (.inl ()),indexedMarksFromVertices n (fun v => f (.inr v)))
    have ha : Measurable a := (measurable_pi_apply _).prodMk
      ((indexedMarksFromVertices_measurable n).comp (Measurable.of_eval fun vertex => measurable_pi_apply (Sum.inr vertex)))
    have haQ : Q.map a = (ν : Measure S).prod M := by
      let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ IndexedVertex n => S)
      have he : a = (Prod.map (fun f : Unit → S => f ()) (indexedMarksFromVertices n)) ∘ e := rfl
      rw [he,← Measure.map_map ((measurable_pi_apply ()).prodMap (indexedMarksFromVertices_measurable n)) e.measurable,infinitePi_sumPiEquivProdPi]
      rw [← Measure.map_prod_map _ _ (by fun_prop) (indexedMarksFromVertices_measurable n),ih]
      rw [(measurePreserving_eval_infinitePi (fun _ : Unit => (ν : Measure S)) ()).map_eq]
    let e := MeasurableEquiv.curry ℕ (ℕ × (Unit ⊕ IndexedVertex n)) S
    let r := MeasurableEquiv.curry ℕ (Unit ⊕ IndexedVertex n) S
    let c : (IndexedVertex (n+1) → S) → ℕ → ℕ → Unit ⊕ IndexedVertex n → S :=
      fun f i j v => f (i,j,v)
    have hc : Measurable c := by fun_prop
    have hcQ : (Measure.infinitePi (fun _ : IndexedVertex (n+1) => (ν : Measure S))).map c =
        Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => Q)) := by
      have he : c = (fun f i => r (f i)) ∘ e := rfl
      rw [he,← Measure.map_map (by fun_prop) e.measurable]
      dsimp only [e, IndexedVertex]
      rw [Measure.infinitePi_map_curry (fun _ _ => (ν : Measure S)),
        Measure.infinitePi_map_pi _ (fun _ => r.measurable)]
      dsimp only [r]
      simp_rw [Measure.infinitePi_map_curry (fun _ _ => (ν : Measure S))]
      rfl
    have he : indexedMarksFromVertices (S := S) (n+1) = (fun f i j => a (f i j)) ∘ c := rfl
    rw [he,← Measure.map_map (by fun_prop) hc,hcQ]
    rw [Measure.infinitePi_map_pi _ (f := fun _ (f : ℕ → Unit ⊕ IndexedVertex n → S) => fun j => a (f j))
      (fun _ => Measurable.of_eval fun column => ha.comp (measurable_pi_apply column))]
    simp_rw [Measure.infinitePi_map_pi _ (fun _ => ha),haQ]
    rfl

def indexedLeafVertex : (n : ℕ) → IndexedLeaf n → Fin n → IndexedVertex n
  | 0,_,i => i.elim0
  | n+1,l,i => Fin.cases (l.1,l.2.1,Sum.inl ())
      (fun j => (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 j))) i

lemma indexedLeafVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafVertex n l) := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simp [indexedLeafVertex] at hij
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [indexedLeafVertex] at hij
      | succ j =>
        simpa only [Fin.succ_inj] using ih l.2.2 (by simpa [indexedLeafVertex] using hij)

end SphericalPerceptronFreeEnergy
end

end OAI
