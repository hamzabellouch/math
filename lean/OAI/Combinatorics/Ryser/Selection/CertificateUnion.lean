import OAI.Combinatorics.Ryser.Selection.PoolGraph
import OAI.Combinatorics.Ryser.Selection.PoolCounts
import OAI.Combinatorics.Ryser.Selection.SmallCertificates
import OAI.Combinatorics.Ryser.Selection.CertificateCount
import OAI.Combinatorics.Ryser.Selection.IndependentTail

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

theorem not_hasCompatibleChoice_mem_certificate_union (data : Data F n)
    (pool : Pool F n K) (hK : 0 < K) (hbad : ¬HasCompatibleChoice data pool) :
    ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
      ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
        NoFeasibleOutside data I T pool := let _ := instFintypeF; by
  classical
  obtain ⟨I, T, hI, hT, hcard, hnone⟩ :=
    not_hasCompatibleChoice_obstruction data pool hK hbad
  have hTtarget : T ⊆ targetPositions I K := by
    simpa only [targetPositions_eq_filter] using hT
  refine ⟨I, Finset.mem_filter.mpr ⟨?_, hI⟩, T, ?_, hnone⟩
  · exact Finset.mem_powerset.mpr (Finset.subset_univ I)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTtarget, hcard⟩

theorem prob_not_hasCompatibleChoice_le_certificate_sum
    (data : Data F n) (hK : 0 < K) :
    (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
        ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
          (poolLaw F n K).prob (NoFeasibleOutside data I T) := by
  classical
  calc
    _ ≤ (poolLaw F n K).prob (fun pool =>
        ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
          ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
            NoFeasibleOutside data I T pool) :=
      (poolLaw F n K).prob_mono
        (fun pool hbad => not_hasCompatibleChoice_mem_certificate_union data pool hK hbad)
    _ ≤ ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
        (poolLaw F n K).prob (fun pool =>
          ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
            NoFeasibleOutside data I T pool) := prob_exists_mem_le _ _ _
    _ ≤ ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter Finset.Nonempty,
        ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
          (poolLaw F n K).prob (NoFeasibleOutside data I T) := by
      apply Finset.sum_le_sum
      intro I _
      exact prob_exists_mem_le _ _ _

theorem sum_certificate_probs_le (data : Data F n) (I : Finset (Fin n))
    (hK : 1 ≤ K) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ T : Finset (Position n K), T ⊆ targetPositions I K →
      T.card ≤ 2 * I.card → (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤ b) :
    (∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
      (poolLaw F n K).prob (NoFeasibleOutside data I T)) ≤
        (3 * (K : ℝ) ^ 2) ^ I.card * b := by
  classical
  calc
    _ ≤ ∑ _T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
        b := by
      apply Finset.sum_le_sum
      intro T hT
      exact hbound T (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
        (Finset.mem_filter.mp hT).2
    _ = (((targetPositions I K).powerset.filter
        (fun T => T.card ≤ 2 * I.card)).card : ℝ) * b := by simp
    _ ≤ (3 * (K : ℝ) ^ 2) ^ I.card * b := by
      apply mul_le_mul_of_nonneg_right _ hb
      apply card_small_subsets_le (targetPositions I K) K I.card hK
      simp [Nat.mul_comm, card_targetPositions I K]

theorem sum_certificate_probs_card_eq_le (data : Data F n) (m : ℕ)
    (hK : 1 ≤ K) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ I : Finset (Fin n), I.card = m →
      ∀ T : Finset (Position n K), T ⊆ targetPositions I K →
        T.card ≤ 2 * I.card →
          (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤ b) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
      ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
        (poolLaw F n K).prob (NoFeasibleOutside data I T)) ≤
      ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) * b := by
  classical
  have hcount :
      (((Finset.univ : Finset (Fin n)).powerset.filter
        (fun I => I.card = m)).card : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
    simpa using card_fixed_subsets_le (Finset.univ : Finset (Fin n)) m
  have hfactor : 0 ≤ (3 * (K : ℝ) ^ 2) ^ m * b :=
    mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (sq_nonneg (K : ℝ))) m) hb
  calc
    _ ≤ ∑ _I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
        (3 * (K : ℝ) ^ 2) ^ m * b := by
      apply Finset.sum_le_sum
      intro I hI
      have hcard := (Finset.mem_filter.mp hI).2
      simpa only [hcard] using sum_certificate_probs_le data I hK b hb (hbound I hcard)
    _ = (((Finset.univ : Finset (Fin n)).powerset.filter
        (fun I => I.card = m)).card : ℝ) * ((3 * (K : ℝ) ^ 2) ^ m * b) := by simp
    _ ≤ (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m *
        ((3 * (K : ℝ) ^ 2) ^ m * b) := mul_le_mul_of_nonneg_right hcount hfactor
    _ = ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m *
        (3 * (K : ℝ) ^ 2) ^ m) * b := (mul_assoc _ _ _).symm

theorem not_hasCompatibleChoice_mem_size_union (data : Data F n)
    (pool : Pool F n K) (hK : 0 < K) (hbad : ¬HasCompatibleChoice data pool) :
    ∃ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
      ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
        ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
          NoFeasibleOutside data I T pool := by
  classical
  obtain ⟨I, hI, T, hT, hnone⟩ :=
    not_hasCompatibleChoice_mem_certificate_union data pool hK hbad
  have hpos : 0 < I.card := Finset.card_pos.mpr (Finset.mem_filter.mp hI).2
  have hcard : I.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ I)
  refine ⟨I.card, ?_, I, ?_, T, hT, hnone⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcard), hpos⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hI).1, rfl⟩

theorem prob_not_hasCompatibleChoice_le_grouped_certificate_sum
    (data : Data F n) (hK : 0 < K) :
    (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
          ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
            (poolLaw F n K).prob (NoFeasibleOutside data I T) := by
  classical
  calc
    _ ≤ (poolLaw F n K).prob (fun pool =>
        ∃ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
          ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
            ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
              NoFeasibleOutside data I T pool) :=
      (poolLaw F n K).prob_mono
        (fun pool hbad => not_hasCompatibleChoice_mem_size_union data pool hK hbad)
    _ ≤ ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        (poolLaw F n K).prob (fun pool =>
          ∃ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
            ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
              NoFeasibleOutside data I T pool) := prob_exists_mem_le _ _ _
    _ ≤ ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
          (poolLaw F n K).prob (fun pool =>
            ∃ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
              NoFeasibleOutside data I T pool) := by
      apply Finset.sum_le_sum
      intro m _
      exact prob_exists_mem_le _ _ _
    _ ≤ ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun I => I.card = m),
          ∑ T ∈ (targetPositions I K).powerset.filter (fun T => T.card ≤ 2 * I.card),
            (poolLaw F n K).prob (NoFeasibleOutside data I T) := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro I _
      exact prob_exists_mem_le _ _ _

theorem prob_not_hasCompatibleChoice_le_size_sum
    (data : Data F n) (hK : 0 < K) (b : ℕ → ℝ) (hb : ∀ m, 0 ≤ b m)
    (hbound : ∀ I : Finset (Fin n), I.Nonempty →
      ∀ T : Finset (Position n K), T ⊆ targetPositions I K →
        T.card ≤ 2 * I.card →
          (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤ b I.card) :
    (poolLaw F n K).prob (fun pool => ¬HasCompatibleChoice data pool) ≤
      ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m),
        ((Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * (3 * (K : ℝ) ^ 2) ^ m) * b m := by
  classical
  refine (prob_not_hasCompatibleChoice_le_grouped_certificate_sum data hK).trans ?_
  apply Finset.sum_le_sum
  intro m hm
  apply sum_certificate_probs_card_eq_le data m (Nat.succ_le_of_lt hK) (b m) (hb m)
  intro I hI T hT hcard
  have hnonempty : I.Nonempty := Finset.card_pos.mp (by
    rw [hI]
    exact (Finset.mem_filter.mp hm).2)
  simpa only [hI] using hbound I hnonempty T hT hcard

end RyserCoveringCounterexample.Selection

end OAI
