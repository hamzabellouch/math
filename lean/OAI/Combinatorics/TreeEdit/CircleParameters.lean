import OAI.Combinatorics.TreeEdit.CircleObstruction

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

def wordLength (k : ℕ) : ℕ := (branching k * repetitions k)^k
def alphabetSize (k : ℕ) : ℕ := branching k^k * resolution k
def binaryWidth (k : ℕ) : ℕ := 2*Nat.clog 2 (alphabetSize k)+3
def binaryLength (k : ℕ) : ℕ := wordLength k*binaryWidth k

lemma wordLength_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ wordLength k := by
  have hT : 1 ≤ repetitions k := one_le_pow₀ (by omega)
  have hm : k ≤ branching k := by
    dsimp [branching]
    have hk2 : 1 ≤ k^2 := one_le_pow₀ (by omega)
    nlinarith
  have hbase : 1 ≤ branching k * repetitions k := (show 1 ≤ branching k by omega).trans (Nat.le_mul_of_pos_right _ hT)
  exact (hm.trans (Nat.le_mul_of_pos_right _ hT)).trans (le_self_pow₀ hbase (by omega))

lemma binaryLength_ge {k : ℕ} (hk : 2 ≤ k) : k ≤ binaryLength k :=
  (wordLength_ge hk).trans (Nat.le_mul_of_pos_right _ (by dsimp [binaryWidth]; omega))

lemma binaryWidth_le {k : ℕ} (hk : 2 ≤ k) : binaryWidth k ≤ 40*k^2 := by
  have hkpow : k ≤ 2^k := (Nat.lt_two_pow_self).le
  have hm : branching k ≤ 2^(4+3*k) := by
    calc
      _ = 16*k^3 := by dsimp [branching]; ring
      _ ≤ 2^4*(2^k)^3 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hkpow 3)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hr : resolution k ≤ 2^(8*k^2) := by
    calc
      _ ≤ (2^k)^(8*k) := Nat.pow_le_pow_left hkpow _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have ha : alphabetSize k ≤ 2^(13*k^2) := by
    calc
      _ ≤ (2^(4+3*k))^k * 2^(8*k^2) := Nat.mul_le_mul (Nat.pow_le_pow_left hm k) hr
      _ = 2^((4+3*k)*k+8*k^2) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hc := Nat.clog_le_of_le_pow ha
  change Nat.clog 2 (alphabetSize k) ≤ 13*k^2 at hc
  dsimp only [binaryWidth]
  nlinarith

lemma branching_le_power {k : ℕ} (hk : 2 ≤ k) : branching k ≤ k^7 := by
  have h16 : 16 ≤ k^4 := by simpa using Nat.pow_le_pow_left hk 4
  calc
    _ = 16*k^3 := by dsimp [branching]; ring
    _ ≤ k^4*k^3 := Nat.mul_le_mul_right _ h16
    _ = _ := by rw [← pow_add]

lemma binaryLength_le_power {k : ℕ} (hk : 2 ≤ k) : binaryLength k ≤ k^(60*k^2) := by
  have hm := branching_le_power hk
  have hW : binaryWidth k ≤ k^8 := by
    have h40 : 40 ≤ k^6 := by have hh := Nat.pow_le_pow_left hk 6; norm_num at hh; omega
    exact (binaryWidth_le hk).trans ((Nat.mul_le_mul_right (k^2) h40).trans_eq (by rw [← pow_add]))
  have hN : wordLength k ≤ k^((7+52*k)*k) := by
    calc
      _ ≤ (k^7 * k^(52*k))^k := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hm) k
      _ = _ := by rw [← pow_add, ← pow_mul]
  calc
    _ ≤ k^((7+52*k)*k)*k^8 := Nat.mul_le_mul hN hW
    _ = k^((7+52*k)*k+8) := by rw [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma length_log_bound {k : ℕ} (hk : 2 ≤ k) :
    Real.log (binaryLength k : ℝ) ≤ 60*(k : ℝ)^2*Real.log k := by
  have hN : 0 < binaryLength k := lt_of_lt_of_le (by omega : 0 < k) (binaryLength_ge hk)
  calc
    _ ≤ Real.log ((k^(60*k^2) : ℕ) : ℝ) := Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast binaryLength_le_power hk)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

end TreeEdit.TorusTree

end OAI
