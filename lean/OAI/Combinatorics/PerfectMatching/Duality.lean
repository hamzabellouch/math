import OAI.Combinatorics.PerfectMatching.Optimizer

namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Finite exponential partition function, based on a probability law p. -/
def partition {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (t*a i)

def tiltedLaw {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  p i * Real.exp (t*a i) / partition p a t

theorem partition_pos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) : 0 < partition p a t := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hp.1 i)).mp
    (show 0 < ∑ i, p i by rw [hp.2]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hp.1 i) (Real.exp_pos _).le)).mpr
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

@[simp] theorem partition_zero {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) : partition p a 0 = 1 := by
  simpa only [partition, zero_mul, Real.exp_zero, mul_one] using hp.2

theorem tiltedLaw_mem_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (t : ℝ) :
    tiltedLaw p a t ∈ probabilitySimplex ι := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hp.1 i) (Real.exp_pos _).le)
    (partition_pos hp a t).le, ?_⟩
  simp only [tiltedLaw, ← Finset.sum_div]
  exact div_self (partition_pos hp a t).ne'

/-- Gibbs' variational inequality for the explicit finite partition function,
including all boundary laws supported on p. -/
theorem entropy_partition_bound {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by
  have hlog : ∀ i, q i * Real.log (tiltedLaw p a t i) =
      q i * Real.log (p i) + t*(q i*a i) - q i*Real.log (partition p a t) := by
    intro i
    by_cases hi : p i = 0
    · simp [hsupp i hi]
    · rw [tiltedLaw, Real.log_div (mul_ne_zero hi (Real.exp_ne_zero _))
        (partition_pos hp a t).ne', Real.log_mul hi (Real.exp_ne_zero _), Real.log_exp]
      ring
  calc
    entropy q ≤ -∑ i, q i*Real.log (tiltedLaw p a t i) :=
      entropy_le_crossEntropy (tiltedLaw_mem_simplex hp a t) hq (by
        intro i hi
        have hii : p i = 0 := by
          have := (div_eq_zero_iff).mp hi
          rcases this with hh | hh
          · exact (mul_eq_zero.mp hh).resolve_right (Real.exp_ne_zero _)
          · exact ((partition_pos hp a t).ne' hh).elim
        exact hsupp i hii)
    _ = _ := by
      simp_rw [hlog]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hq.2, one_mul]
      ring


/-- A score affine in the matching vector; the constant permits centering
without changing the duality calculation. -/
def linearScore (G : LooplessGraph V E) (u : E → ℝ) (c : ℝ) (M : G.Matching) : ℝ :=
  (∑ e, u e * G.indicator M e) - c

omit [Fintype V] [DecidableEq V] in
theorem sum_mean_assoc (G : LooplessGraph V E) (p : G.Matching → ℝ) (u : E → ℝ) :
    (∑ M, p M * (∑ e, u e * G.indicator M e)) = ∑ e, u e * G.mean p e := by
  simp only [LooplessGraph.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro M _
  ring

omit [Fintype V] [DecidableEq V] in
theorem linearScore_expectation (G : LooplessGraph V E) (p : G.Matching → ℝ)
    (u : E → ℝ) (c : ℝ) :
    (∑ M, p M * linearScore G u c M) =
      (∑ e, u e * G.mean p e) - c * ∑ M, p M := by
  simp only [linearScore, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in
/-- A genuine upper bound on the actual maximum entropy at every mean in the
optimizer's face. This is proved from Gibbs' inequality, not assumed as a
replacement definition of H. -/
theorem matching_entropy_dual_bound (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {r : G.Matching → ℝ} (hr : r ∈ probabilitySimplex G.Matching)
    (hrsupport : ∀ M, p M = 0 → r M = 0)
    (u : E → ℝ) (c t : ℝ) :
    maxMatchingEntropy G (G.mean r) ≤
      Real.log (partition p (linearScore G u c) t) - ∑ M, r M * Real.log (p M) -
        t * ∑ M, r M * linearScore G u c M := by
  obtain ⟨q, hq, heq⟩ := maxMatchingEntropy_attained G (G.mean_mem_polytope hr)
  have hsuppq := matching_optimizer_face_support G hp hopt hq.1 hr hq.2 hrsupport
  have hmean : G.mean (q-r) = 0 := by
    change G.meanLinear (q-r) = 0
    rw [map_sub]
    change G.mean q-G.mean r = 0
    rw [hq.2, sub_self]
  have hsum : ∑ M, (q-r) M = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hq.1.2, hr.2, sub_self]
  have hlog := matching_optimizer_log_annihilates G hp hopt (q-r) hsum hmean
    (fun M hM => by simp [hsuppq M hM, hrsupport M hM])
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at hlog
  have hscore : (∑ M, q M*linearScore G u c M) = ∑ M, r M*linearScore G u c M := by
    rw [linearScore_expectation, linearScore_expectation, hq.2, hq.1.2, hr.2]
  rw [← heq]
  simpa only [hlog, hscore] using entropy_partition_bound hp.1 hq.1 hsuppq
    (linearScore G u c) t

end MatchingEntropy

end

end OAI
