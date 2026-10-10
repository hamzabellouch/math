import Mathlib
import OAI.Probability.Perceptron.Variational.CovarianceMatrix

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]

def compactMapArray (e : K→L) (Q : CompactArray K) : CompactArray L := fun i j => e (Q i j)
def compactMapBlock (e : K→L) (n : ℕ) (Q : CompactBlock K n) : CompactBlock L n := fun i j => e (Q i j)

lemma compactMapArray_continuous {e : K→L} (he : Continuous e) : Continuous (compactMapArray e) := by
  unfold compactMapArray
  fun_prop
lemma compactMapBlock_continuous {e : K→L} (he : Continuous e) (n : ℕ) :
    Continuous (compactMapBlock e n) := by
  unfold compactMapBlock
  fun_prop

def compactDiagonalMapArray (e d : K→L) (Q : CompactArray K) : CompactArray L :=
  fun i j => if i=j then d (Q i j) else e (Q i j)
def compactDiagonalMapBlock (e d : K→L) (n : ℕ) (Q : CompactBlock K n) : CompactBlock L n :=
  fun i j => if i=j then d (Q i j) else e (Q i j)

lemma compactDiagonalMapArray_continuous {e d : K→L} (he : Continuous e) (hd : Continuous d) :
    Continuous (compactDiagonalMapArray e d) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold compactDiagonalMapArray
  split_ifs <;> fun_prop
lemma compactDiagonalMapBlock_continuous {e d : K→L} (he : Continuous e) (hd : Continuous d) (n : ℕ) :
    Continuous (compactDiagonalMapBlock e d n) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  unfold compactDiagonalMapBlock
  split_ifs <;> fun_prop

omit [TopologicalSpace K] [TopologicalSpace L] in
lemma compactDiagonalMapBlock_compactBlock (e d : K→L) (n : ℕ) (Q : CompactArray K) :
    compactBlock n (compactDiagonalMapArray e d Q)=compactDiagonalMapBlock e d n (compactBlock n Q) := by
  funext i j
  simp only [compactBlock,compactDiagonalMapArray,compactDiagonalMapBlock,Fin.val_inj]


variable [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
  [SecondCountableTopology K] [SecondCountableTopology L]

def compactMapLaw (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K)) :
    ProbabilityMeasure (CompactArray L) :=
  ⟨(μ : Measure (CompactArray K)).map (compactMapArray e),
    (Measure.isProbabilityMeasure_map_iff (compactMapArray_continuous he).measurable.aemeasurable).2
      inferInstance⟩

lemma compactMapLaw_integral (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K))
    (F : CompactArray L→ℝ) (hF : Measurable F) :
    (∫ Q, F Q ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, F (compactMapArray e Q) ∂(μ : Measure (CompactArray K)) :=
  integral_map (compactMapArray_continuous he).measurable.aemeasurable hF.aestronglyMeasurable

lemma compactMapLaw_gg (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0) (n : ℕ) (i : Fin n)
    (f : CompactBlock L n →ᵇ ℝ) (g : L →ᵇ ℝ) :
    compactGGDefect (compactMapLaw e he μ) n i f g=0 := by
  let f' := f.compContinuous ⟨compactMapBlock e n,compactMapBlock_continuous he n⟩
  let g' := g.compContinuous ⟨e,he⟩
  have hmul (a b : ℕ) :
      (∫ Q, f (compactBlock n Q)*g (Q a b) ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
        ∫ Q, f' (compactBlock n Q)*g' (Q a b) ∂(μ : Measure (CompactArray K)) := by
    exact compactMapLaw_integral e he μ _
      ((f.measurable.comp (compactBlock_continuous n).measurable).mul (g.measurable.comp (by fun_prop)))
  have hf : (∫ Q, f (compactBlock n Q) ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, f' (compactBlock n Q) ∂(μ : Measure (CompactArray K)) := by
    exact compactMapLaw_integral e he μ _
      (f.measurable.comp (compactBlock_continuous n).measurable)
  have hg : (∫ Q, g (Q 0 1) ∂(compactMapLaw e he μ : Measure (CompactArray L)))=
      ∫ Q, g' (Q 0 1) ∂(μ : Measure (CompactArray K)) := by
    exact compactMapLaw_integral e he μ _ (by fun_prop)
  unfold compactGGDefect
  simp_rw [hmul,hf,hg]
  exact hGG n i f' g'

lemma compactMapLaw_pair (e : K→L) (he : Continuous e) (μ : ProbabilityMeasure (CompactArray K))
    (a b : ℕ) :
    (compactMapLaw e he μ : Measure (CompactArray L)).map (fun Q => Q a b)=
      ((μ : Measure (CompactArray K)).map (fun Q => Q a b)).map e := by
  change ((μ : Measure (CompactArray K)).map (compactMapArray e)).map (fun Q => Q a b)=_
  rw [Measure.map_map (by fun_prop) (compactMapArray_continuous he).measurable,
    Measure.map_map he.measurable (by fun_prop)]
  rfl

def compactDiagonalMapLaw (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K)) : ProbabilityMeasure (CompactArray L) :=
  ⟨(μ : Measure (CompactArray K)).map (compactDiagonalMapArray e d),
    (Measure.isProbabilityMeasure_map_iff
      (compactDiagonalMapArray_continuous he hd).measurable.aemeasurable).2 inferInstance⟩

lemma compactDiagonalMapLaw_integral (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K)) (F : CompactArray L→ℝ) (hF : Measurable F) :
    (∫ Q, F Q ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, F (compactDiagonalMapArray e d Q) ∂(μ : Measure (CompactArray K)) :=
  integral_map (compactDiagonalMapArray_continuous he hd).measurable.aemeasurable hF.aestronglyMeasurable

lemma compactDiagonalMapLaw_gg (e d : K→L) (he : Continuous e) (hd : Continuous d)
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (n : ℕ) (i : Fin n) (f : CompactBlock K n →ᵇ ℝ) (g : K →ᵇ ℝ),
      compactGGDefect μ n i f g=0) (n : ℕ) (i : Fin n)
    (f : CompactBlock L n →ᵇ ℝ) (g : L →ᵇ ℝ) :
    compactGGDefect (compactDiagonalMapLaw e d he hd μ) n i f g=0 := by
  let f' := f.compContinuous ⟨compactDiagonalMapBlock e d n,compactDiagonalMapBlock_continuous he hd n⟩
  let g' := g.compContinuous ⟨e,he⟩
  have hmul (a b : ℕ) (hab : a≠b) :
      (∫ Q, f (compactBlock n Q)*g (Q a b) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
        ∫ Q, f' (compactBlock n Q)*g' (Q a b) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => f (compactBlock n Q)*g (Q a b))
      ((f.measurable.comp (compactBlock_continuous n).measurable).mul (g.measurable.comp (by fun_prop)))]
    simp only [compactDiagonalMapBlock_compactBlock,compactDiagonalMapArray,ite_eq_right hab]
    rfl
  have hf : (∫ Q, f (compactBlock n Q) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, f' (compactBlock n Q) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => f (compactBlock n Q))
      (f.measurable.comp (compactBlock_continuous n).measurable)]
    simp only [compactDiagonalMapBlock_compactBlock]
    rfl
  have hg : (∫ Q, g (Q 0 1) ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∫ Q, g' (Q 0 1) ∂(μ : Measure (CompactArray K)) := by
    rw [compactDiagonalMapLaw_integral e d he hd μ (fun Q => g (Q 0 1)) (by fun_prop)]
    rfl
  unfold compactGGDefect
  rw [hmul i.val n (Nat.ne_of_lt i.isLt),hf,hg]
  have hs : (∑ j ∈ Finset.univ.erase i, ∫ Q, f (compactBlock n Q)*g (Q i j)
      ∂(compactDiagonalMapLaw e d he hd μ : Measure (CompactArray L)))=
      ∑ j ∈ Finset.univ.erase i, ∫ Q, f' (compactBlock n Q)*g' (Q i j)
        ∂(μ : Measure (CompactArray K)) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply hmul
    intro hij
    exact (Finset.mem_erase.mp hj).1 (Fin.ext hij.symm)
  rw [hs]
  exact hGG n i f' g'
end SphericalPerceptronFreeEnergy
end

end OAI
