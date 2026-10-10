import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedVertices
import OAI.Probability.Perceptron.Brownian.CountableGaussianField
import OAI.Probability.Perceptron.Variational.GaussianMarkRecursion

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

def countableCoordinate {ι : Type*} [Countable ι] (i : ι) : ℕ :=
  @Encodable.encode ι (Encodable.ofCountable ι) i

lemma countableCoordinate_injective {ι : Type*} [Countable ι] :
    Function.Injective (countableCoordinate (ι := ι)) := by
  let := Encodable.ofCountable ι
  exact Encodable.encode_injective

section
variable {V I : Type} [Countable V] [Fintype I]

def countableGaussianVectors (g : ℕ → ℝ) (v : V) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => g (countableCoordinate (v,i)))

lemma countableGaussianVectors_measurable : Measurable (countableGaussianVectors (V := V) (I := I)) := by
  apply Measurable.of_eval
  intro v
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  fun_prop

lemma countableGaussianVectors_law :
    countableGaussianLaw.map (countableGaussianVectors (V := V) (I := I)) =
      Measure.infinitePi (fun _ : V => stdGaussian (EuclideanSpace ℝ I)) := by
  let c : (ℕ → ℝ) → V×I → ℝ := fun g p => g (countableCoordinate p)
  have hc : Measurable c := by fun_prop
  have hl : countableGaussianLaw.map c = Measure.infinitePi (fun _ : V×I => gaussianReal 0 1) :=
    Measure.map_infinitePi_infinitePi_of_inj countableCoordinate_injective
  let e := MeasurableEquiv.curry V I ℝ
  have he : countableGaussianVectors (V := V) (I := I) =
      ((fun f v => WithLp.toLp 2 (f v)) ∘ e) ∘ c := rfl
  have hm : Measurable (fun f : V → I → ℝ => fun v => WithLp.toLp 2 (f v)) := by fun_prop
  rw [he,← Measure.map_map (hm.comp e.measurable) hc,hl,
    ← Measure.map_map hm e.measurable]
  rw [show e = MeasurableEquiv.curry V I ℝ from rfl,Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1),
    Measure.infinitePi_map_pi _ (fun _ => (PiLp.continuous_toLp 2 _).measurable)]
  simp only [Measure.infinitePi_eq_pi,map_pi_eq_stdGaussian]

end

abbrev SharedVertex (n : ℕ) := Unit ⊕ IndexedVertex n

def indexedGaussianDisorder (n : ℕ) (I : Type) [Fintype I] (g : ℕ → ℝ) :
    EuclideanSpace ℝ I × IndexedCascadeMarks (EuclideanSpace ℝ I) n :=
  (countableGaussianVectors (V := SharedVertex n) (I := I) g (Sum.inl ()),
    indexedMarksFromVertices n (fun v => countableGaussianVectors (V := SharedVertex n) (I := I) g (Sum.inr v)))

lemma indexedGaussianDisorder_measurable (n : ℕ) (I : Type) [Fintype I] :
    Measurable (indexedGaussianDisorder n I) := by
  exact ((measurable_pi_apply (Sum.inl ())).comp (countableGaussianVectors_measurable (V := SharedVertex n) (I := I))).prodMk
    ((indexedMarksFromVertices_measurable n).comp
      ((Measurable.of_eval fun vertex => measurable_pi_apply (Sum.inr vertex)).comp
        (countableGaussianVectors_measurable (V := SharedVertex n) (I := I))))

lemma indexedGaussianDisorder_law (n : ℕ) (I : Type) [Fintype I] :
    countableGaussianLaw.map (indexedGaussianDisorder n I) =
      (stdGaussian (EuclideanSpace ℝ I)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) n) := by
  let E := EuclideanSpace ℝ I
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : SharedVertex n => E)
  let a := Prod.map (fun f : Unit → E => f ()) (indexedMarksFromVertices (S := E) n)
  have ha : Measurable a := (measurable_pi_apply ()).prodMap (indexedMarksFromVertices_measurable n)
  have he : indexedGaussianDisorder n I = (a ∘ e) ∘ countableGaussianVectors (V := SharedVertex n) (I := I) := rfl
  rw [he,← Measure.map_map (ha.comp e.measurable) countableGaussianVectors_measurable,
    countableGaussianVectors_law,← Measure.map_map ha e.measurable,infinitePi_sumPiEquivProdPi]
  rw [← Measure.map_prod_map _ _ (measurable_pi_apply ()) (indexedMarksFromVertices_measurable n),
    Measure.infinitePi_map_eval]
  exact congrArg (Measure.prod (stdGaussian E)) (indexedMarksFromVertices_law (gaussianMarkLaw (E := E)) n)

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [SecondCountableTopology E] [BorelSpace E] in
lemma indexedLeafState_gaussianLinear (A : ℕ → E →L[ℝ] E) (n : ℕ)
    (x : ℕ → E) (f : IndexedVertex n → E) (l : IndexedLeaf n) (j : ℕ) :
    indexedLeafState (gaussianLinearMarkStep A) n (x,indexedMarksFromVertices n f) l j =
      x (j+n) + ∑ i : Fin n, A (j+n-1-i.val) (f (indexedLeafVertex n l i)) := by
  induction n generalizing x j with
  | zero => simp [indexedLeafState]
  | succ n ih =>
    change indexedLeafState (gaussianLinearMarkStep A) n
      (gaussianLinearMarkStep A (x,f (l.1,l.2.1,Sum.inl ())),
        indexedMarksFromVertices n (fun v => f (l.1,l.2.1,Sum.inr v))) l.2.2 j = _
    rw [ih,Fin.sum_univ_succ]
    simp only [gaussianLinearMarkStep,indexedLeafVertex,Fin.cases_zero,Fin.cases_succ,
      Fin.val_zero,Fin.val_succ,Nat.sub_zero]
    rw [show j+(n+1)-1 = j+n by omega]
    have he : (∑ i : Fin n, A (j+n-1-i.val) (f (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 i)))) =
        ∑ i : Fin n, A (j+n-(i.val+1)) (f (l.1,l.2.1,Sum.inr (indexedLeafVertex n l.2.2 i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      omega
    rw [he]
    simp only [add_assoc]

end

def indexedLeafSharedVertex (n : ℕ) (l : IndexedLeaf n) : Fin (n+1) → SharedVertex n :=
  Fin.cases (Sum.inl ()) (fun i => Sum.inr (indexedLeafVertex n l i))

lemma indexedLeafSharedVertex_injective (n : ℕ) (l : IndexedLeaf n) :
    Function.Injective (indexedLeafSharedVertex n l) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => simp [indexedLeafSharedVertex] at hij
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [indexedLeafSharedVertex] at hij
    | succ j =>
      simpa only [Fin.succ_inj] using indexedLeafVertex_injective n l
        (by simpa [indexedLeafSharedVertex] using hij)

end SphericalPerceptronFreeEnergy

end

end OAI
