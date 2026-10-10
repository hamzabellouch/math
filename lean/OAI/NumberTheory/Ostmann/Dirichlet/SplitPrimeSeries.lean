import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

noncomputable def splitPrimeSupport {q : ℕ} (chi : DirichletCharacter ℂ q)
    (M : ℕ) (Q : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Q⌋₊).filter (fun p => ¬p ∣ M ∧ chi p = 1)

noncomputable def splitPrimeMass {q : ℕ} (chi : DirichletCharacter ℂ q)
    (M : ℕ) (Q : ℝ) : ℝ :=
  ∑ p ∈ splitPrimeSupport chi M Q, Real.log p / (p : ℝ)

noncomputable def removedPrimeSeriesTerm (M : ℕ) (sigma : ℝ) (n : ℕ) : ℝ :=
  if n ∣ M then ordinaryPrimeSeriesTerm sigma n else 0

noncomputable def tailPrimeSeriesTerm (Q sigma : ℝ) (n : ℕ) : ℝ :=
  if Q < (n : ℝ) then ordinaryPrimeSeriesTerm sigma n else 0

lemma filtered_ordinary_summable {sigma : ℝ} (hs : 1 < sigma)
    (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun n => if P n then ordinaryPrimeSeriesTerm sigma n else 0) := by
  apply (ordinaryPrimeSeries_summable hs).of_nonneg_of_le
  · intro n; split_ifs <;> first | exact ordinaryPrimeSeriesTerm_nonneg _ _ | exact le_rfl
  · intro n; split_ifs <;> first | exact le_rfl | exact ordinaryPrimeSeriesTerm_nonneg _ _

lemma prime_split_pointwise {q : ℕ} (chi : DirichletCharacter ℂ q)
    (hquad : chi.IsQuadratic) {M : ℕ} (hqM : q ∣ M) {Q : ℝ} (hQ : 0 ≤ Q)
    (sigma : ℝ) (n : ℕ) :
    ordinaryPrimeSeriesTerm sigma n + realPrimeSeriesTerm chi sigma n ≤
      2 * (if n ∈ splitPrimeSupport chi M Q then ordinaryPrimeSeriesTerm sigma n else 0) +
        2 * removedPrimeSeriesTerm M sigma n + 2 * tailPrimeSeriesTerm Q sigma n := by
  have ho := ordinaryPrimeSeriesTerm_nonneg sigma n
  have hr : 0 ≤ removedPrimeSeriesTerm M sigma n := by
    unfold removedPrimeSeriesTerm; split_ifs <;> first | exact ho | exact le_rfl
  have ht : 0 ≤ tailPrimeSeriesTerm Q sigma n := by
    unfold tailPrimeSeriesTerm; split_ifs <;> first | exact ho | exact le_rfl
  have hsplit : 0 ≤ (if n ∈ splitPrimeSupport chi M Q then ordinaryPrimeSeriesTerm sigma n else 0) := by
    split_ifs <;> first | exact ho | exact le_rfl
  by_cases hp : n.Prime
  · have hreal : realPrimeSeriesTerm chi sigma n ≤ ordinaryPrimeSeriesTerm sigma n := by
      have hchi := (Complex.re_le_norm (chi n)).trans (chi.norm_le_one n)
      dsimp only [realPrimeSeriesTerm, ordinaryPrimeSeriesTerm]
      simp only [hp, ite_true]
      calc
        _ = (chi n).re * (Real.log n / (n : ℝ) ^ sigma) := by ring
        _ ≤ 1 * (Real.log n / (n : ℝ) ^ sigma) := mul_le_mul_of_nonneg_right hchi (by positivity)
        _ = _ := one_mul _
    by_cases hnM : n ∣ M
    · have he : removedPrimeSeriesTerm M sigma n = ordinaryPrimeSeriesTerm sigma n := by
        simp [removedPrimeSeriesTerm, hnM]
      rw [he]
      linarith
    by_cases hnQ : Q < (n : ℝ)
    · have he : tailPrimeSeriesTerm Q sigma n = ordinaryPrimeSeriesTerm sigma n := by
        simp [tailPrimeSeriesTerm, hnQ]
      rw [he]
      linarith
    have hne : chi (n : ZMod q) ≠ 0 := by
      intro hz
      have hd : n ∣ q := (RealCharacterAnalysis.apply_prime_eq_zero_iff chi hp).mp hz
      exact hnM (hd.trans hqM)
    rcases hquad (n : ZMod q) with hz | hz | hz
    · exact (hne hz).elim
    · have hmem : n ∈ splitPrimeSupport chi M Q := by
        simp only [splitPrimeSupport, Finset.mem_filter, Nat.mem_primesLE]
        exact ⟨⟨(Nat.le_floor_iff hQ).mpr (le_of_not_gt hnQ), hp⟩, hnM, hz⟩
      have he : realPrimeSeriesTerm chi sigma n = ordinaryPrimeSeriesTerm sigma n := by
        simp [realPrimeSeriesTerm, ordinaryPrimeSeriesTerm, hz]
      rw [ite_eq_left hmem, he]
      linarith
    · have he : realPrimeSeriesTerm chi sigma n = -ordinaryPrimeSeriesTerm sigma n := by
        simp [realPrimeSeriesTerm, ordinaryPrimeSeriesTerm, hp, hz, neg_div]
      rw [he]
      linarith
  · simp [ordinaryPrimeSeriesTerm, realPrimeSeriesTerm, hp]
    positivity

theorem prime_split_tsum_le {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hquad : chi.IsQuadratic) {M : ℕ} (hqM : q ∣ M) {Q sigma : ℝ}
    (hQ : 0 ≤ Q) (hs : 1 < sigma) :
    (∑' n, ordinaryPrimeSeriesTerm sigma n) + (∑' n, realPrimeSeriesTerm chi sigma n) ≤
      2 * splitPrimeMass chi M Q +
        2 * (∑' n, removedPrimeSeriesTerm M sigma n) + 2 * (∑' n, tailPrimeSeriesTerm Q sigma n) := by
  classical
  let A : ℕ → ℝ := fun n => if n ∈ splitPrimeSupport chi M Q then ordinaryPrimeSeriesTerm sigma n else 0
  have hA : Summable A := filtered_ordinary_summable hs _
  have hR : Summable (removedPrimeSeriesTerm M sigma) := filtered_ordinary_summable hs _
  have hT : Summable (tailPrimeSeriesTerm Q sigma) := filtered_ordinary_summable hs _
  have ho := ordinaryPrimeSeries_summable hs
  have hc := (primeSeries_hasSum chi hs).summable
  have h := (ho.add hc).tsum_le_tsum (prime_split_pointwise chi hquad hqM hQ sigma)
    (((hA.mul_left 2).add (hR.mul_left 2)).add (hT.mul_left 2))
  rw [ho.tsum_add hc, ((hA.mul_left 2).add (hR.mul_left 2)).tsum_add (hT.mul_left 2),
    (hA.mul_left 2).tsum_add (hR.mul_left 2), hA.tsum_mul_left, hR.tsum_mul_left, hT.tsum_mul_left] at h
  have hfinite : ∑' n, A n = ∑ p ∈ splitPrimeSupport chi M Q, ordinaryPrimeSeriesTerm sigma p := by
    rw [tsum_eq_sum (s := splitPrimeSupport chi M Q) (fun n hn => by simp [A, hn])]
    apply Finset.sum_congr rfl
    intro p hp
    simp [A, hp]
  have hcompare : ∑ p ∈ splitPrimeSupport chi M Q, ordinaryPrimeSeriesTerm sigma p ≤ splitPrimeMass chi M Q := by
    apply Finset.sum_le_sum
    intro p hp
    have hprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    simp only [ordinaryPrimeSeriesTerm, hprime, ite_true]
    apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by exact_mod_cast hprime.pos)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ p by exact_mod_cast hprime.one_le) hs.le
  rw [hfinite] at h
  linarith

end Ostmann.Dirichlet

end OAI
