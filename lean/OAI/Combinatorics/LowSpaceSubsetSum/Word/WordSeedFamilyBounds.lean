import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedSeparatorPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedScalarBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredSpace

namespace OAI

/-! # Family generation stays inside the application budgets

The family count is exponential only in one top block. Range tests and
permutation materialization keep polynomial work per sampled mask.
-/

namespace LowSpaceSubsetSum.WordSeedFamilyBounds

open WordSeedMeasured

variable {n : ℕ}

private theorem self_le_power {u k : ℕ} (hu : 1 ≤ u) (hk : 1 ≤ k) : u ≤ u^k := by
  simpa only [Nat.pow_one] using Nat.pow_le_pow_right hu hk

private theorem coefficient_power {u c k : ℕ} (hc : c ≤ u) : c*u^k ≤ u^(k+1) := by
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.mul_le_mul_right (u^k) hc

theorem maskBudget_add_le (I : Instance n) (hn : 10000 ≤ n) {g : ℕ} (hg : g ≤ n) :
    maskBudget n g+100 ≤ inputScale I^5 := by
  let u := inputScale I
  have hu : 10000 ≤ u := by dsimp only [u,inputScale]; omega
  have hnu : n+1 ≤ u := by dsimp only [u,inputScale]; omega
  have hgu : g+1 ≤ u := by omega
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by omega) 3
  have hu1 : u ≤ u^4 := self_le_power (by omega) (by decide)
  have hu2 : u^2 ≤ u^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hone : 1 ≤ u^4 := by omega
  have ha : g*(14*n^3+5*g+68) ≤ 14*u^4+5*u^2+68*u := by
    calc
      _ ≤ u*(14*u^3+5*u+68) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hb : 10*(g+1)^2 ≤ 10*u^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgu 2)
  have hc : 10*(g+1)*(n^3+256) ≤ 10*u^4+2560*u := by
    calc
      _ ≤ (10*u)*(u^3+256) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hpoly : maskBudget n g+100 ≤ 3000*u^4 := by
    unfold maskBudget
    nlinarith only [ha,hb,hc,hu1,hu2,hone]
  exact hpoly.trans (coefficient_power (by omega : 3000 ≤ u))

theorem family_envelope (I : Instance n) (hn : 10000 ≤ n) {g : ℕ} (hg : g ≤ n) :
    100*(11*2^g+1)*(maskBudget n g+100) ≤ inputScale I^6*2^g := by
  have hm := maskBudget_add_le I hn hg
  have hp : 1 ≤ 2^g := Nat.one_le_two_pow
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  calc
    _ ≤ (100*(12*2^g))*inputScale I^5 := Nat.mul_le_mul (by omega) hm
    _ = (1200*inputScale I^5)*2^g := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (coefficient_power (by omega : 1200 ≤ inputScale I))

theorem prepared_envelope (I : Instance n) (hn : 10000 ≤ n) {g : ℕ} (hg : g ≤ n) :
    60*g+55+100*(11*2^g+1)*(maskBudget n g+100) ≤ inputScale I^7*2^g ∧
    264+100*(11*2^g+1)*(maskBudget n g+100) ≤ inputScale I^7*2^g := by
  let u := inputScale I
  let P := 2^g
  have hu : 10000 ≤ u := by dsimp only [u,inputScale]; omega
  have hgu : g ≤ u := by dsimp only [u,inputScale]; omega
  have hP : 1 ≤ P := Nat.one_le_two_pow
  have hbase := family_envelope I hn hg
  change _ ≤ u^6*P at hbase
  have hlow : 60*g+55 ≤ u^5 := by
    have h : 115*u ≤ u^2 := by
      simpa only [Nat.pow_one] using
        (coefficient_power (u := u) (c := 115) (k := 1) (by omega))
    have hp : u^2 ≤ u^5 := Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 2 ≤ 5)
    omega
  have hsmall : 264 ≤ u^5 := (show 264 ≤ u by omega).trans
    (self_le_power (by omega) (by decide))
  have h5 : u^5 ≤ u^6*P := by
    calc
      _ ≤ u^6 := Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 5 ≤ 6)
      _ = u^6*1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left (u^6) hP
  have hs : 2*u^6*P ≤ u^7*P := Nat.mul_le_mul_right P
    (coefficient_power (u := u) (c := 2) (k := 6) (by omega))
  rw [Nat.mul_assoc] at hs
  change _ ≤ u^7*P ∧ _ ≤ u^7*P
  constructor <;> omega

theorem familiesPrepared_bounded_scale (I : Instance n) (hn : 10000 ≤ n)
    (g k : ℕ) (hg : g ≤ n) (hlarge : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2*g ≤ 3*k) (w : ℕ) (hw : Nat.clog 2 g ≤ w) :
    (familiesPrepared g k hlarge heven hk hklo w n hw).Bounded
      (inputScale I^7*2^g) (inputScale I^7*2^g) (inputScale I^7*2^g) := by
  have h := prepared_envelope I hn hg
  exact WordSeedMeasured.bounded_mono _
    (familiesPrepared_bounded g k hlarge heven hk hklo w n hw) h.1 h.2 h.2

theorem familiesPrepared_application (I : Instance n) (hn : 10000 ≤ n)
    (g k C : ℕ) (hg : g ≤ n) (hlarge : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2*g ≤ 3*k) (w : ℕ) (hw : Nat.clog 2 g ≤ w)
    (hcodes : 2^g ≤ C) (hhalf : g ≤ (n+1)/2) :
    (familiesPrepared g k hlarge heven hk hklo w n hw).Bounded
      (inputScale I^9*2^((n+1)/2)) (inputScale I^9*(C+1)) (inputScale I^9*(C+1)) := by
  have hu : 1 ≤ inputScale I := by unfold inputScale; omega
  have hp : inputScale I^7 ≤ inputScale I^9 := Nat.pow_le_pow_right hu (by decide)
  apply WordSeedMeasured.bounded_mono _ (familiesPrepared_bounded_scale I hn g k hg
    hlarge heven hk hklo w hw)
  · exact Nat.mul_le_mul hp (Nat.pow_le_pow_right (by decide) hhalf)
  · exact Nat.mul_le_mul hp (hcodes.trans (by omega))
  · exact Nat.mul_le_mul hp (hcodes.trans (by omega))

theorem canonical_family_half (n : ℕ) :
    2*RepresentationSetup.blockHalf n 0 ≤ (n+1)/2 := by
  simp only [RepresentationSetup.blockHalf,Matrix.cons_val_zero]
  omega

theorem canonical_family_codes (n : ℕ) :
    2^(2*RepresentationSetup.blockHalf n 0) ≤ compressionDictionaryCapacity n := by
  apply (Nat.pow_le_pow_right (by decide)
    (show 2*RepresentationSetup.blockHalf n 0 ≤ 2*(2*RepresentationSetup.blockHalf n 0) by omega)).trans
  exact RepresentationSetup.separator_table_rate_le_capacity

end LowSpaceSubsetSum.WordSeedFamilyBounds

end OAI
