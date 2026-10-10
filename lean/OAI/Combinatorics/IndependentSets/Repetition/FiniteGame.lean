import Mathlib

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators

noncomputable def finiteGame {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (p : I → ℝ) (q : J → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * b i j

lemma finiteGame_integral_left {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (q : J → ℝ) (p p' : I → ℝ) (a a' : ℝ) :
    finiteGame b (a • p + a' • p') q =
      a * finiteGame b p q + a' * finiteGame b p' q := by
  simp only [finiteGame, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

lemma finiteGame_integral_right {I J : Type*} [Fintype I] [Fintype J]
    (b : I → J → ℝ) (p : I → ℝ) (q q' : J → ℝ) (a a' : ℝ) :
    finiteGame b p (a • q + a' • q') =
      a * finiteGame b p q + a' * finiteGame b p q' := by
  simp only [finiteGame, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_left_comm (p _), mul_assoc, Finset.mul_sum]

def finiteProbabilitySimplex (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  { weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1 }

private lemma convex_finiteProbabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (finiteProbabilitySimplex Index) := by
  intro weights hweights other hother coeff otherCoeff hcoeff hotherCoeff hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hcoeff (hweights.1 index))
    (mul_nonneg hotherCoeff (hother.1 index)), ?_⟩
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hweights.2, hother.2, mul_one] using hsum

private lemma isCompact_finiteProbabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (finiteProbabilitySimplex Index) := by
  have hrange := isCompact_range
    (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ Index).continuous
  rw [Convexity.StdSimplex.range_toFun_comp_weights] at hrange
  simpa only [finiteProbabilitySimplex, Set.ofPred_forall, Set.ofPred_and] using hrange

private lemma single_mem_finiteProbabilitySimplex {Index : Type*} [Fintype Index]
    [DecidableEq Index] (index : Index) :
    Pi.single index 1 ∈ finiteProbabilitySimplex Index := by
  refine ⟨?_, by simp⟩
  intro other
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

theorem finite_minimax_counterstatement {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (b : I → J → ℝ) (ξ : ℝ)
    (h : ∀ p ∈ finiteProbabilitySimplex I, ∃ j, ξ < ∑ i, p i * b i j) :
    ∃ q ∈ finiteProbabilitySimplex J, ∀ i, ξ < ∑ j, q j * b i j := by
  classical
  have hX : (finiteProbabilitySimplex I).Nonempty := ⟨Pi.single (Classical.arbitrary I) 1,
    single_mem_finiteProbabilitySimplex _⟩
  have hY : (finiteProbabilitySimplex J).Nonempty := ⟨Pi.single (Classical.arbitrary J) 1,
    single_mem_finiteProbabilitySimplex _⟩
  have hleft (q : J → ℝ) : Continuous (fun p => finiteGame b p q) := by
    unfold finiteGame
    fun_prop
  have hright (p : I → ℝ) : Continuous (fun q => finiteGame b p q) := by
    unfold finiteGame
    fun_prop
  have hc (q : J → ℝ) : ConvexOn ℝ (finiteProbabilitySimplex I) (fun p => finiteGame b p q) := by
    refine ⟨convex_finiteProbabilitySimplex _, ?_⟩
    intro p hp p' hp' a a' ha ha' haa'
    simpa only [smul_eq_mul] using (finiteGame_integral_left b q p p' a a').le
  have hd (p : I → ℝ) : ConcaveOn ℝ (finiteProbabilitySimplex J) (fun q => finiteGame b p q) := by
    refine ⟨convex_finiteProbabilitySimplex _, ?_⟩
    intro q hq q' hq' a a' ha ha' haa'
    simpa only [smul_eq_mul] using (finiteGame_integral_right b p q q' a a').ge
  obtain ⟨p, hp, q, hq, hs⟩ := Sion.exists_isSaddlePointOn
    hX (convex_finiteProbabilitySimplex _) (isCompact_finiteProbabilitySimplex _)
    (fun q _ => (hleft q).continuousOn.lowerSemicontinuousOn)
    (fun q _ => (hc q).quasiconvexOn)
    (convex_finiteProbabilitySimplex _) hY (isCompact_finiteProbabilitySimplex _)
    (fun p _ => (hright p).continuousOn.upperSemicontinuousOn)
    (fun p _ => (hd p).quasiconcaveOn)
  obtain ⟨j, hj⟩ := h p hp
  refine ⟨q, hq, ?_⟩
  intro i
  have hs' := hs (Pi.single i 1) (single_mem_finiteProbabilitySimplex _)
    (Pi.single j 1) (single_mem_finiteProbabilitySimplex _)
  simp [finiteGame, Pi.single_apply] at hs'
  exact hj.trans_le hs'

end LargeIndependentSets

end OAI
