import Mathlib
import OAI.Combinatorics.KMedian.Process.SourceAverage
import OAI.Combinatorics.KMedian.Programs.InstanceRounding
import OAI.Combinatorics.KMedian.Reduction.CompletionSelection
import OAI.Combinatorics.KMedian.Reduction.RationalCompletion
import OAI.Combinatorics.KMedian.Reduction.CloseFromServing
import OAI.Combinatorics.KMedian.Reduction.BadCenterBound
import OAI.Combinatorics.KMedian.Geometry.RationalSparseTaper
import OAI.Combinatorics.KMedian.Sparse.SparsePreparedMoments
import OAI.Combinatorics.KMedian.Sparse.SparseHistoryBounds
import OAI.Combinatorics.KMedian.Compression.GaussianListPivot
import OAI.Combinatorics.KMedian.Process.TaperReindex
import OAI.Combinatorics.KMedian.Sparse.SparseMapBind
import OAI.Combinatorics.KMedian.Geometry.RationalHistorySelection
import OAI.Combinatorics.KMedian.Geometry.RationalIndexedCost
import OAI.Combinatorics.KMedian.Programs.InstanceFractionalRound
import OAI.Combinatorics.KMedian.Geometry.ComputedInstanceAlgorithm
import OAI.Combinatorics.KMedian.Reduction.OrdinaryListProgram

namespace OAI

section
namespace MetricKMedian
open Preparation Finset

theorem exists_internal_program (ε : ℝ) (hε : 0<ε) :
    ∃ algorithm : Instance → List Bool,
      Nonempty (Binary.PolyProgram InstanceProgram.encode id algorithm) ∧
      ∀ I, Correct ε I (algorithm I) := by
  obtain ⟨s,r,hs,hs1,hr,hα,hfactor⟩ := exists_approximation_slack ε hε
  obtain ⟨p⟩ := exists_rational_all_parameters hs hs
  obtain ⟨C,hC⟩ := exists_nat_gt (max (0:ℝ) (1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)))
  have hCap : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ) := (le_max_right _ _).trans hC.le
  have hCp : 0<C := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hC
  let α := ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))
  have hPseudo : ∀ I : Instance, I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
      (I.computedPseudo r hr p C).card≤I.k+C ∧ cost I (I.computedPseudo r hr p C)≤α*optimum I :=
    fun I => I.computedPseudo_spec r hr p hs.le hs hs1 C hCap
  obtain ⟨δ,a,b,hδ,hsδ,hf,ha,hb⟩ := Reduction.reduction_parameters α (ε/2) hα (by positivity) C hCp
  refine ⟨Reduction.Program.algorithm r hr p C a b δ,
    ⟨(Reduction.Program.ordinaryProgram r hr p C a b δ).comp Binary.BooleanLists.unpackProgram⟩,?_⟩
  intro I
  obtain ⟨hOF,hOn,hOk,hCost⟩ := Reduction.Program.ordinarySet_spec r hr p C a b δ α (ε/2) hCp hδ hsδ
    (by positivity) hf ha hb hPseudo I
  refine ⟨Reduction.Program.ordinarySet r hr p C a b δ I,hOF,hOn,hOk,rfl,hCost.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hfactor I.optimum_nonneg

theorem exists_binary_program (ε : ℝ) (hε : 0<ε) :
    ∃ algorithm : Instance → List Bool,
      Nonempty (Binary.PolyProgram encodeInstance id algorithm) ∧ ∀ I, Correct ε I (algorithm I) := by
  obtain ⟨algorithm, ⟨P⟩, hP⟩ := exists_internal_program ε hε
  exact ⟨algorithm, ⟨InputParser.instanceProgram.comp P⟩, hP⟩

theorem main_finite_work : ∀ ε : ℝ, 0<ε →
    ∃ (algorithm : Instance → List Bool) (P : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
      (∀ k : P.tm.K, Finite (P.tm.Γ k)) ∧ ∀ I, Correct ε I (algorithm I) := by
  intro ε hε
  obtain ⟨algorithm,⟨P⟩,hP⟩ := exists_binary_program ε hε
  exact ⟨algorithm,P.stock,P.finite_work,hP⟩

theorem main : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ algorithm : Instance → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encodeInstance id algorithm) ∧
      ∀ I, Correct epsilon I (algorithm I) := by
  intro epsilon hε
  obtain ⟨algorithm,P,_,hP⟩ := main_finite_work epsilon hε
  exact ⟨algorithm,⟨P⟩,hP⟩
end MetricKMedian
end

end OAI
