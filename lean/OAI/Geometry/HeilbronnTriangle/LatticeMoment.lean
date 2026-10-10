import OAI.Geometry.HeilbronnTriangle.LatticeShell
import OAI.Geometry.HeilbronnTriangle.ZeroMomentSum

namespace OAI


namespace Problem355.LatticeMoment

open Finset

theorem cubic_moment_of_residue_counts
    (S : Finset (Fin 3 → ℤ)) (v : (Fin 3 → ℤ) → ℕ)
    (B R b e : ℕ) (hB : 2 ≤ B) (hR : B ^ e ≤ R)
    (T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hv : ∀ x ∈ S, v x ≤ e)
    (hres : ∀ j ≤ e, ∀ x ∈ S, j ≤ v x →
      (fun i => (x i : ZMod (B ^ j))) ∈ T j)
    (hT : ∀ j ≤ e, ((T j).card : ℝ) ≤
      (B : ℝ) ^ (3 * j) / (B : ℝ) ^ (j + (j - b))) :
    ∑ x ∈ S, (B : ℝ) ^ (3 * v x) ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  have hB0 : 0 < B := by omega
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have htail : ∀ j ≤ e,
      ((S.filter fun x => j ≤ v x).card : ℝ) ≤
        (64 * (R : ℝ) ^ 3) / (B : ℝ) ^ (j + (j - b)) := by
    intro j hj
    have hq : 0 < B ^ j := pow_pos hB0 _
    have hqR : B ^ j ≤ R :=
      (Nat.pow_le_pow_right (by omega : 1 ≤ B) hj).trans hR
    have hdensity : ((T j).card : ℝ) ≤
        ((B ^ j : ℕ) : ℝ) ^ 3 / (B : ℝ) ^ (j + (j - b)) := by
      simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm j 3] using hT j hj
    have hc := LatticeShell.card_symmetric_box_of_residue_density_le
      (S.filter fun x => j ≤ v x) R (B ^ j) hq hqR (T j)
      ((B : ℝ) ^ (j + (j - b))) (by positivity)
      (fun x hx i => hbox x (mem_filter.mp hx).1 i)
      (fun x hx => hres j hj x (mem_filter.mp hx).1 (mem_filter.mp hx).2)
      hdensity
    norm_num only [show (4 : ℝ) ^ 3 = 64 by norm_num] at hc
    exact hc
  calc
    ∑ x ∈ S, (B : ℝ) ^ (3 * v x) ≤
        2 * (64 * (R : ℝ) ^ 3) * (B : ℝ) ^ (b + e) :=
      ZeroMoment.cubic_moment_of_tail S v b e hBR (by positivity) hv htail
    _ = 128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by ring

theorem cubic_divisor_moment_of_residue_counts
    (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
    (B R b e : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R)
    (T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hg : ∀ x ∈ S, g x ∣ B ^ e)
    (hres : ∀ j ≤ e, ∀ x ∈ S, B ^ j ∣ g x →
      (fun i => (x i : ZMod (B ^ j))) ∈ T j)
    (hT : ∀ j ≤ e, ((T j).card : ℝ) ≤
      (B : ℝ) ^ (3 * j) / (B : ℝ) ^ (j + (j - b))) :
    ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  have hex : ∀ x : Fin 3 → ℤ, ∃ a ≤ e, x ∈ S → g x = B ^ a := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hB).mp (hg x hx)
      exact ⟨a, ha, fun _ => hga⟩
    · exact ⟨0, Nat.zero_le _, fun h => (hx h).elim⟩
  choose v hv hgv using hex
  have hm := cubic_moment_of_residue_counts S v B R b e hB.two_le hR T hbox
    (fun x _ => hv x) (fun j hj x hx hjv => hres j hj x hx (by
      rw [hgv x hx]
      exact Nat.pow_dvd_pow B hjv)) hT
  calc
    ∑ x ∈ S, (g x : ℝ) ^ 3 = ∑ x ∈ S, (B : ℝ) ^ (3 * v x) := by
      apply sum_congr rfl
      intro x hx
      rw [hgv x hx, Nat.cast_pow, ← pow_mul, Nat.mul_comm (v x) 3]
    _ ≤ 128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := hm

end Problem355.LatticeMoment

end OAI
