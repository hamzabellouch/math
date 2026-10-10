import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalAllParameters
import OAI.Combinatorics.KMedian.Reduction.ReductionClosure
import OAI.Combinatorics.KMedian.Optimization.ApproximationSlack
import OAI.Combinatorics.KMedian.Programs.InstanceComputedPseudo

namespace OAI


                                                 
section
namespace MetricKMedian
open Preparation Finset

structure AlgorithmParameters (s : ℝ) where
  r : ℕ
  rpos : 0 < r
  rounding : RationalAllParameters s s
  allowance : ℕ
  δ : ℚ
  a : ℕ
  b : ℕ

namespace AlgorithmParameters
variable {s : ℝ}

 def outputSet (P : AlgorithmParameters s) (I : Instance) : Finset (Fin I.n) :=
  Reduction.ordinaryReduction (fun J => J.computedPseudo P.r P.rpos P.rounding P.allowance)
    P.δ P.allowance P.a P.b I

 def algorithm (P : AlgorithmParameters s) (I : Instance) : List Bool :=
  List.ofFn (fun i : Fin I.n => decide (i ∈ P.outputSet I))

end AlgorithmParameters

theorem exists_correct_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : ℝ) (P : AlgorithmParameters s), ∀ I, Correct ε I (P.algorithm I) := by
  obtain ⟨s,r,hs,hs1,hr,hα,hfactor⟩ := exists_approximation_slack ε hε
  obtain ⟨p⟩ := exists_rational_all_parameters hs hs
  obtain ⟨C,hC⟩ := exists_nat_gt (max (0:ℝ) (1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)))
  have hCap : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ) ≤ (C:ℝ) := (le_max_right _ _).trans hC.le
  have hCp : 0 < C := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hC
  let α := ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))
  let pseudo := fun I : Instance => I.computedPseudo r hr p C
  have hPseudo : ∀ I, pseudo I⊆I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card≤I.k+C ∧ cost I (pseudo I)≤α*optimum I :=
    fun I => I.computedPseudo_spec r hr p hs.le hs hs1 C hCap
  obtain ⟨δ,a,b,hred⟩ := Reduction.ordinaryReduction_parameters pseudo α (ε/2) hα (by positivity) C hCp hPseudo
  let P : AlgorithmParameters s := ⟨r,hr,p,C,δ,a,b⟩
  refine ⟨s,P,?_⟩
  intro I
  obtain ⟨hOF,hOn,hOk,hCost⟩ := hred I
  refine ⟨P.outputSet I,hOF,hOn,hOk,rfl,hCost.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hfactor I.optimum_nonneg

end MetricKMedian
end

end OAI
