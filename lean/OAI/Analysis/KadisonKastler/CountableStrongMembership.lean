import OAI.Analysis.KadisonKastler.CountableConjugacyTests

namespace OAI

/-! # Countable finite-vector tests for algebra membership

For contractions, approximation on finite prefixes of a dense vector
sequence is equivalent to membership in the strongly closed target
algebra, provided the test family is strongly dense in its unit ball.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_le_iff_dense_vector_tests (ξ : ℕ → H) (hξ : DenseRange ξ)
    (T : H →L[ℂ] H) {a : ℝ} (ha : 0 ≤ a) :
    ‖T‖ ≤ a ↔ ∀ n, ‖T (ξ n)‖ ≤ a * ‖ξ n‖ := by
  constructor
  · exact fun h n => (T.le_opNorm (ξ n)).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · intro h
    apply T.opNorm_le_bound ha
    intro x
    exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n)
      (isClosed_le (T.continuous.norm) (continuous_const.mul continuous_norm)) (hξ x)

def CountableStrongTests (ξ : ℕ → H) (F : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ m k : ℕ, ∃ S ∈ F, ∀ l ≤ m, ‖(T - S) (ξ l)‖ < 1 / (k + 1 : ℝ)

omit [CompleteSpace H] in
theorem exists_strong_sequence_of_countable_tests (ξ : ℕ → H) (hξ : DenseRange ξ)
    (F : Set (H →L[ℂ] H)) (hF : ∀ S ∈ F, ‖S‖ ≤ 1)
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (htest : CountableStrongTests ξ F T) :
    ∃ S : ℕ → H →L[ℂ] H, (∀ n, S n ∈ F) ∧
      ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x)) := by
  choose S hSF hSn using (fun n => htest n n)
  refine ⟨S, hSF, ?_⟩
  apply tendsto_apply_of_dense_contractions ξ hξ S T (fun n => hF _ (hSF n)) hT
  intro l
  apply (tendsto_iff_dist_tendsto_zero).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop l] with n hn
  simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using (hSn n l hn).le

omit [CompleteSpace H] in
theorem countableStrongTests_of_strong_sequence
    (ξ : ℕ → H) (F : Set (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (S : ℕ → H →L[ℂ] H) (hSF : ∀ n, S n ∈ F)
    (hlim : ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x))) :
    CountableStrongTests ξ F T := by
  intro m k
  have hsmall : ∀ᶠ n in atTop, ∀ l ∈ Finset.range (m + 1),
      ‖(T - S n) (ξ l)‖ < 1 / (k + 1 : ℝ) := by
    apply (eventually_all_finset _).mpr
    intro l _
    have h := (Metric.tendsto_nhds.mp (hlim (ξ l))) (1 / (k + 1 : ℝ)) (by positivity)
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using h
  obtain ⟨n, hn⟩ := hsmall.exists
  exact ⟨S n, hSF n, fun l hl => hn l (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))⟩

/-- The countably quantified test predicate exactly recognizes the
contractive elements of the target algebra. -/
theorem mem_iff_countableStrongTests (N : VonNeumannAlgebra H)
    (ξ : ℕ → H) (hξ : DenseRange ξ) (F : Set (H →L[ℂ] H))
    (hFN : F ⊆ unitBall N)
    (hFdense : ∀ T ∈ unitBall N, ∃ S : ℕ → H →L[ℂ] H,
      (∀ n, S n ∈ F) ∧ ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (T x)))
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    T ∈ N ↔ CountableStrongTests ξ F T := by
  constructor
  · intro hTN
    obtain ⟨S, hSF, hlim⟩ := hFdense T ⟨hTN, hT⟩
    exact countableStrongTests_of_strong_sequence ξ F T S hSF hlim
  · intro htest
    obtain ⟨S, hSF, hlim⟩ := exists_strong_sequence_of_countable_tests ξ hξ F
      (fun S hS => (hFN hS).2) T hT htest
    simpa only [unitaryConj_one] using unitaryConj_mem_of_strong_tests N 1 S T hlim
      (fun n => by simpa only [unitaryConj_one] using (hFN (hSF n)).1)

end

end KadisonKastler

end OAI
