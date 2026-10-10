import OAI.NumberTheory.JointDickman.Probability.ResidueQuotientMean
import OAI.NumberTheory.JointDickman.Probability.ConsecutiveSiteMean

namespace OAI

/-! # Enlarging the residue period preserves the prime-site mean -/

namespace JointDickman
open Finset

theorem primeSite_modEq {P : Finset ℕ} {q n m : ℕ}
    (hP : ∀ p ∈ P, p ∣ q) (h : n ≡ m [MOD q]) :
    P.filter (fun p => p ∣ n) = P.filter (fun p => p ∣ m) := by
  ext p
  simp only [mem_filter]
  exact and_congr_right (fun hp => h.dvd_iff (hP p hp))

theorem consecutive_site_mean_at_multiple (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} [NeZero q] (hd : (∏ p ∈ P, p) ∣ q)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ a : ZMod q, F (P.filter (fun p => p ∣ a.val)) (P.filter (fun p => p ∣ a.val+1))) / (q : ℝ) =
      (∑ n ∈ range (∏ p ∈ P, p), F (P.filter (fun p => p ∣ n)) (P.filter (fun p => p ∣ n+1))) /
        (∏ p ∈ P, (p : ℝ)) := by
  classical
  let d := ∏ p ∈ P, p
  let : NeZero d := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)⟩
  let G (a : ZMod d) := F (P.filter (fun p => p ∣ a.val)) (P.filter (fun p => p ∣ a.val+1))
  have hpd : ∀ p ∈ P, p ∣ d := fun p hp => dvd_prod_of_mem id hp
  have hG (n : ℕ) : G (n : ZMod d) =
      F (P.filter (fun p => p ∣ n)) (P.filter (fun p => p ∣ n+1)) := by
    dsimp only [G]
    rw [ZMod.val_natCast, primeSite_modEq hpd (Nat.mod_modEq n d),
      primeSite_modEq hpd ((Nat.mod_modEq n d).add_right 1)]
  have h := residue_quotient_mean hd G
  simp only [hG] at h
  have hs := residue_sum_eq_range (fun a => (G a : ℂ))
  have hs' : (∑ a : ZMod d, G a) = ∑ n ∈ range d, G n := by exact_mod_cast hs
  rw [hs'] at h
  simp only [hG] at h
  simpa only [d, Nat.cast_prod] using h

end JointDickman

end OAI
