import OAI.NumberTheory.JointDickman.Arithmetic.BrunPrimeBlocks

namespace OAI

/-! # The dimension hypothesis controls each logarithmic prime block -/
namespace JointDickman
open Finset

 theorem prime_log_two_le {p : ℕ} (hp : p.Prime) : Real.log 2 ≤ Real.log p :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)

 theorem brunPrimeBlock_inverse_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z L : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (hL : 0 ≤ L) (hLz : L ≤ Real.log z)
    (j : ℕ) :
    (∏ p ∈ brunPrimeBlock P L j, (1-g p)⁻¹) ≤ Real.exp (κ*Real.log 2+A/Real.log 2) := by
  let a := max (Real.log 2) (L/(2:ℝ)^(j+1))
  let b := max (Real.log 2) (L/(2:ℝ)^j)
  have ha0 : 0 ≤ a := (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans (le_max_left _ _)
  have hb : b ≤ Real.log z := max_le
    (Real.log_le_log (by norm_num) hz)
    ((brun_level_antitone hL (Nat.zero_le j)).trans (by simpa using hLz))
  have hba : b ≤ 2*a := by
    apply max_le
    · have := le_max_left (Real.log 2) (L/(2:ℝ)^(j+1))
      dsimp [a] at ha0 ⊢
      linarith
    · have hh : L/(2:ℝ)^j = 2*(L/(2:ℝ)^(j+1)) := by rw [pow_succ]; field_simp
      rw [hh]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  apply sieveDimension_log_interval hg (fun p hp => by exact_mod_cast (hP p hp).1.pos)
    hκ hA hd (brunPrimeBlock_subset P L j) (le_max_left _ _)
    (max_le_max le_rfl (brun_level_antitone hL (Nat.le_succ j))) hb (by linarith) _ (by norm_num) hba
  intro p hp
  have hh := mem_filter.mp hp
  exact ⟨max_le (prime_log_two_le (hP p hh.1).1) hh.2.1.le,hh.2.2.trans (le_max_right _ _)⟩

 theorem brunPrimeTail_inverse_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) :
    (∏ p ∈ P \ P.filter (fun p : ℕ => Real.log p ≤ Real.log z/8), (1-g p)⁻¹) ≤
      Real.exp (κ*Real.log 8+A/Real.log 2) := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  apply sieveDimension_log_interval (a := max (Real.log 2) (Real.log z/8)) (b := Real.log z) (R := 8)
    hg (fun p hp => by exact_mod_cast (hP p hp).1.pos)
    hκ hA hd sdiff_subset (le_max_left _ _)
    (max_le (Real.log_le_log (by norm_num) hz) (by linarith)) le_rfl hz0 _ (by norm_num) _
  · intro p hp
    have hh := mem_sdiff.mp hp
    have hlo : Real.log z/8 ≤ Real.log p := by
      have hn : ¬ Real.log p ≤ Real.log z/8 := fun h => hh.2 (mem_filter.mpr ⟨hh.1,h⟩)
      linarith
    exact ⟨max_le (prime_log_two_le (hP p hh.1).1) hlo,
      Real.log_le_log (by exact_mod_cast (hP p hh.1).1.pos) (hP p hh.1).2⟩
  · have hh := le_max_right (Real.log 2) (Real.log z/8)
    linarith

 theorem sieve_survival_subset {P Q : Finset ℕ} {g : ℕ → ℝ} {C : ℝ}
    (hQP : Q ⊆ P) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hC : (∏ p ∈ P \ Q, (1-g p)⁻¹) ≤ C) :
    (∏ p ∈ Q, (1-g p)) ≤ C*(∏ p ∈ P, (1-g p)) := by
  have hpos : 0 < ∏ p ∈ P, (1-g p) := prod_pos (fun p hp => by linarith [(hg p hp).2])
  have hne : (∏ p ∈ P \ Q, (1-g p)) ≠ 0 :=
    (prod_pos (fun p hp => by linarith [(hg p (mem_sdiff.mp hp).1).2])).ne'
  have heq : (∏ p ∈ P, (1-g p))*(∏ p ∈ P \ Q, (1-g p)⁻¹) = ∏ p ∈ Q, (1-g p) := by
    rw [prod_inv_distrib, ← prod_sdiff hQP]
    field_simp
  calc
    _ = (∏ p ∈ P, (1-g p))*(∏ p ∈ P \ Q, (1-g p)⁻¹) := heq.symm
    _ ≤ (∏ p ∈ P, (1-g p))*C := mul_le_mul_of_nonneg_left hC hpos.le
    _ = _ := mul_comm _ _

end JointDickman

end OAI
