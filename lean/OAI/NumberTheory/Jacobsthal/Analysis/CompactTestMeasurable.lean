import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.NumberTheory.Jacobsthal.Partitions.CompactTestGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactTestMeasurable

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open CompactTestGeometry RegeneratingInverseBands ActualCouplingUpdates ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}

theorem primeTest_measurable (F : Side → ℝ×ℝ → ℝ) :
    Measurable (primeTest (w:=w) (ell:=ell) (S:=S) (start:=start) F) := measurable_of_countable _

theorem continuousTest_measurable (v : ℝ) (F : Side → ℝ×ℝ → ℝ) (hF : ∀ i,Measurable (F i)) :
    Measurable (continuousTest v F) := by
  have hcoord : Measurable (fun z : CostState => (gapValue v z,stateRatio z.1)) :=
    (gapValue_measurable v).prodMk (stateRatio_measurable.comp measurable_fst)
  have hside : MeasurableSet {z : CostState | stateSide z.1 = .even} :=
    measurable_fst (side_set_measurable .even)
  have heq : (fun z : CostState => F (stateSide z.1) (gapValue v z,stateRatio z.1)) =
      (fun z => if stateSide z.1 = .even then F .even (gapValue v z,stateRatio z.1)
        else F .odd (gapValue v z,stateRatio z.1)) := by
    funext z
    rcases z with ⟨s,t⟩
    cases s <;> rfl
  have hb : Measurable (fun z : CostState => F (stateSide z.1) (gapValue v z,stateRatio z.1)) := by
    rw [heq]
    exact Measurable.ite hside ((hF .even).comp hcoord) ((hF .odd).comp hcoord)
  exact hb.sumElim measurable_const

theorem primeTest_bound {F : Side → ℝ×ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ i x,|F i x| ≤ A) (z : ChainState w ell S start) : |primeTest F z| ≤ A := by
  cases z with
  | none => simpa only [primeTest,abs_zero] using hA
  | some h => exact hF _ _

theorem continuousTest_bound {F : Side → ℝ×ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ i x,|F i x| ≤ A) (v : ℝ) (z : CemeteryKernel.Space CostState) :
    |continuousTest v F z| ≤ A := by
  cases z with
  | inr u => simpa only [continuousTest,abs_zero] using hA
  | inl y => exact hF _ _

theorem test_difference_bound {F : Side → ℝ×ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ i x,|F i x| ≤ A) (v : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    |primeTest F p-continuousTest v F z| ≤ 2*A := by
  exact (abs_sub _ _).trans (by linarith [primeTest_bound hA hF p,continuousTest_bound hA hF v z])

section Generic
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem bounded_integrable [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {A : ℝ} (hb : ∀ x,|f x| ≤ A) : Integrable f μ := by
  refine (integrable_const A).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem integral_difference_enorm {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ENNReal.ofReal |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)| ≤ ∫⁻ x,ENNReal.ofReal |f x-g x| ∂μ := by
  rw [← integral_sub hf hg]
  simpa only [Real.enorm_eq_ofReal_abs] using enorm_integral_le_lintegral_enorm (fun x => f x-g x)

theorem finite_integral_difference (μ : ℕ → Measure α) (f g : α → ℝ) (N : ℕ)
    (hf : ∀ n ∈ range N,Integrable f (μ n)) (hg : ∀ n ∈ range N,Integrable g (μ n)) :
    ENNReal.ofReal |(∑ n ∈ range N,∫ x,f x ∂μ n)-(∑ n ∈ range N,∫ x,g x ∂μ n)| ≤
      ∑ n ∈ range N,∫⁻ x,ENNReal.ofReal |f x-g x| ∂μ n := by
  rw [← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum (fun n hn => integral_difference_enorm (hf n hn) (hg n hn))
end Generic

end NumberTheoryLean.CompactTestMeasurable

end

end Erdos970

end OAI
