import OAI.Combinatorics.TwoWayAutomata.DeterministicTransport
import OAI.Combinatorics.TwoWayAutomata.RelationBridge
import OAI.Combinatorics.TwoWayAutomata.TransitionBridge
import OAI.Combinatorics.Automata.Main

namespace OAI

namespace TwoWayComplementation

namespace CompanionBridge

/-- A state lower bound for every deterministic recognizer of relation liveness. -/
theorem deterministic_bound (h s : ℕ) (hh : 2 ≤ h)
    (D : TwoNFA (SetRel (Fin h) (Fin h)) (Fin s))
    (hdet : D.Deterministic) (hD : D.language = sourceLanguage (Fin h)) :
    2 ^ ((h - 2) / 31) ≤ 4 * (s + 1) ^ 2 := by
  let A := D.pullAlphabet (relationEquiv (Fin h))
  have ha : A.Deterministic := hdet.pullAlphabet _
  apply (OneWayLiveness.main_theorem h hh).2 false s (toDMachine A ha)
  intro w
  rw [toDMachine_accepts]
  change w ∈ (D.pullAlphabet (relationEquiv (Fin h))).language ↔ _
  rw [D.pullAlphabet_language, hD]
  exact sourceLanguage_map_iff w

end CompanionBridge

/-- Arithmetic specialization for the relation alphabet on n - 2 vertices. -/
theorem deterministic_rate (n s : ℕ) (hn : 131 ≤ n)
    (hb : 2 ^ ((n - 4) / 31) ≤ 4 * (s + 1) ^ 2) :
    (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (s : ℝ) := by
  let k := (n - 4) / 127
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hrate : 4 * k ≤ (n - 4) / 31 := by dsimp [k]; omega
  have hbR : (2 : ℝ) ^ ((n - 4) / 31) ≤ 4 * ((s : ℝ) + 1) ^ 2 := by
    exact_mod_cast hb
  have hp : (2 : ℝ) ^ (4 * k) ≤ 4 * ((s : ℝ) + 1) ^ 2 :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrate).trans hbR
  have he : (2 : ℝ) ^ (4 * k) = ((2 : ℝ) ^ k) ^ 4 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [he] at hp
  have ht : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
  have hsq : (((2 : ℝ) ^ k) ^ 2) ^ 2 ≤ (2 * ((s : ℝ) + 1)) ^ 2 := by
    nlinarith only [hp]
  have hs : ((2 : ℝ) ^ k) ^ 2 ≤ 2 * ((s : ℝ) + 1) :=
    (sq_le_sq₀ (sq_nonneg _) (by positivity)).mp hsq
  change (1 / 2 : ℝ) * 2 ^ k ≤ (s : ℝ)
  nlinarith [mul_nonneg (sub_nonneg.mpr ht)
    (show 0 ≤ (2 : ℝ) ^ k + 1 by positivity)]

/-- Deterministic lower bound with arbitrary finite state types. -/
theorem deterministic_liveness_lower_bound (n : ℕ) (hn : 131 ≤ n)
    (Q : Type*) [Fintype Q]
    (D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q)
    (hdet : D.Deterministic) (hD : D.language = sourceLanguage (Fin (n - 2))) :
    (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ) := by
  have hb := CompanionBridge.deterministic_bound (n - 2) (Fintype.card Q) (by omega)
    (D.reindex (Fintype.equivFin Q)) (hdet.reindex _) (by
      rw [TwoNFA.reindex_language, hD])
  apply deterministic_rate n (Fintype.card Q) hn
  simpa only [Nat.sub_sub, Nat.reduceAdd] using hb

end TwoWayComplementation

end OAI
