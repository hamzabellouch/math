import OAI.Analysis.KadisonSimilarity.Tracial.TracialBoundedBalls
import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerGNS

namespace OAI

/-! Diagonal bounded representatives in the tracial ultrapower. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower TracialUltrapower Filter
open scoped Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a * b) = τ (b * a))

private theorem trace_sequence_norm_tendsto (z : ℕ →ᵇ A) :
    Tendsto (fun i => ‖τ.toPreGNS (z i)‖) (ω : Filter ℕ)
      (𝓝 ‖gnsTracialVector (quotientTrace τ h1 ω htr) (quotientHom τ h1 ω htr z)‖) := by
  rw [gnsTracialVector_apply, UniformSpace.Completion.norm_coe, quotientTrace_preGNS_norm]
  change Tendsto (fun i => ‖τ.toPreGNS (z i)‖) (ω : Filter ℕ)
    (𝓝 (sequenceTwoNorm (traceHilbertMap τ h1) ω z))
  simpa only [traceHilbertMap_apply] using
    tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω z

/-- A rapidly converging sequence of uniformly bounded representatives has
one bounded diagonal representative for its Hilbert-space limit. -/
theorem exists_bounded_diagonal_trace_limit
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (x : ℕ → (ℕ →ᵇ A)) (C : ℝ) (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (ξ : (quotientTrace τ h1 ω htr).GNS)
    (hξ : ∀ n, dist (gnsTracialVector (quotientTrace τ h1 ω htr)
      (quotientHom τ h1 ω htr (x n))) ξ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ y : ℕ →ᵇ A, ‖y‖ ≤ C ∧
      gnsTracialVector (quotientTrace τ h1 ω htr) (quotientHom τ h1 ω htr y) = ξ := by
  classical
  let V := gnsTracialVector (quotientTrace τ h1 ω htr)
  let q := quotientHom τ h1 ω htr
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hr (n : ℕ) : 0 < r n := pow_pos (by norm_num) _
  let P : ℕ → ℕ → Prop := fun i n => ∀ j ≤ n,
    ‖τ.toPreGNS (x n i - x j i)‖ ≤ 3 * r j
  have hP (n : ℕ) : ∀ᶠ i in (ω : Filter ℕ), P i n := by
    have hb (j : ℕ) (hjn : j ≤ n) : ‖V (q (x n - x j))‖ < 3 * r j := by
      have hn : r n ≤ r j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hjn
      calc
        ‖V (q (x n - x j))‖ = dist (V (q (x n))) (V (q (x j))) := by
          rw [dist_eq_norm, map_sub, map_sub]
        _ ≤ dist (V (q (x n))) ξ + dist ξ (V (q (x j))) := dist_triangle _ _ _
        _ ≤ r n + r j := add_le_add (hξ n) (by simpa only [dist_comm] using hξ j)
        _ < 3 * r j := by linarith [hr j]
    have hall : ∀ᶠ i in (ω : Filter ℕ), ∀ j ∈ Finset.range (n + 1),
        ‖τ.toPreGNS (x n i - x j i)‖ ≤ 3 * r j := by
      rw [eventually_all_finset]
      intro j hj
      have ht := (trace_sequence_norm_tendsto τ h1 ω htr (x n - x j)).eventually_lt_const
        (hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      exact ht.mono fun i hi => hi.le
    filter_upwards [hall] with i hi j hj
    exact hi j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hP0 (i : ℕ) : P i 0 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp only [sub_self, map_zero, norm_zero]
    positivity
  let k : ℕ → ℕ := fun i => Nat.findGreatest (P i) i
  have hkP (i : ℕ) : P i (k i) := Nat.findGreatest_spec (Nat.zero_le i) (hP0 i)
  have hk (j : ℕ) : ∀ᶠ i in (ω : Filter ℕ), j ≤ k i := by
    have hji : ∀ᶠ i in (ω : Filter ℕ), j ≤ i :=
      (eventually_ge_atTop j).filter_mono (hω.trans_eq Nat.cofinite_eq_atTop)
    filter_upwards [hji, hP j] with i hji hi
    exact Nat.le_findGreatest hji hi
  let y : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => x (k i) i) C (fun i => (x (k i)).norm_coe_le_norm i |>.trans (hx (k i)))
  have hy : ‖y‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr
    (fun i => (x (k i)).norm_coe_le_norm i |>.trans (hx (k i)))
  refine ⟨y, hy, ?_⟩
  have hdist (j : ℕ) : dist (V (q y)) ξ ≤ 4 * r j := by
    have hj : ‖V (q (y - x j))‖ ≤ 3 * r j := by
      apply le_of_tendsto (trace_sequence_norm_tendsto τ h1 ω htr (y - x j))
      filter_upwards [hk j] with i hi
      exact hkP i j hi
    calc
      dist (V (q y)) ξ ≤ dist (V (q y)) (V (q (x j))) + dist (V (q (x j))) ξ :=
        dist_triangle _ _ _
      _ ≤ 3 * r j + r j := by
        apply add_le_add _ (hξ j)
        simpa only [dist_eq_norm, map_sub] using hj
      _ = 4 * r j := by ring
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have ht : Tendsto (fun j => 4 * r j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 4
  exact ge_of_tendsto ht (Eventually.of_forall hdist)

end KadisonSimilarity

end

end OAI
