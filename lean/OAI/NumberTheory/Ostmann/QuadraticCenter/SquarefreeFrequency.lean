import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace OAI

/-! # The unique squarefree frequency decomposition -/

namespace Ostmann

theorem squarefree_square_decomposition_unique {a b c d : ℕ}
    (ha : Squarefree a) (hc : Squarefree c) (hb : 0 < b) (hd : 0 < d)
    (h : a * b ^ 2 = c * d ^ 2) : a = c ∧ b = d := by
  have hac : a = c := by
    apply Nat.eq_of_factorization_eq ha.ne_zero hc.ne_zero
    intro p
    have he := congrArg (fun n : ℕ => n.factorization p) h
    simp only [Nat.factorization_mul ha.ne_zero (pow_ne_zero _ hb.ne'),
      Nat.factorization_mul hc.ne_zero (pow_ne_zero _ hd.ne'),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
    have hpa := ha.natFactorization_le_one p
    have hpc := hc.natFactorization_le_one p
    omega
  refine ⟨hac, ?_⟩
  rw [hac] at h
  have hbd : b ^ 2 = d ^ 2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc.ne_zero) h
  nlinarith

/-- The squarefree kernel is divided into the part supported on `L` and
the part coprime to `L`. Positivity excludes the zero frequency. -/
structure SquarefreeFrequency (L u : ℕ) where
  s : ℕ
  v : ℕ
  w : ℕ
  s_pos : 0 < s
  v_pos : 0 < v
  w_pos : 0 < w
  kernel_squarefree : Squarefree (s * v)
  v_dvd : v ∣ L
  s_coprime : s.Coprime L
  value : s * v * w ^ 2 = u

theorem exists_squarefreeFrequency {L u : ℕ} (hL : 0 < L) (hu : 0 < u) :
    Nonempty (SquarefreeFrequency L u) := by
  obtain ⟨a, w, ha, hw, he, hs⟩ := Nat.sq_mul_squarefree_of_pos hu
  let v := Nat.gcd a L
  let s := a / v
  have hv : 0 < v := Nat.gcd_pos_of_pos_left L ha
  have hvd : v ∣ a := Nat.gcd_dvd_left a L
  have hsa : s * v = a := Nat.div_mul_cancel hvd
  have hsp : 0 < s := by
    by_contra hh
    have hz : s = 0 := Nat.eq_zero_of_not_pos hh
    rw [hz, zero_mul] at hsa
    omega
  refine ⟨⟨s, v, w, hsp, hv, hw, hsa ▸ hs, Nat.gcd_dvd_right a L,
    Nat.coprime_div_gcd_of_squarefree hs hL.ne', ?_⟩⟩
  rw [hsa, mul_comm a]
  exact he

namespace SquarefreeFrequency

theorem v_eq_gcd {L u : ℕ} (a : SquarefreeFrequency L u) :
    a.v = Nat.gcd (a.s * a.v) L := by
  exact (Nat.gcd_mul_of_coprime_of_dvd a.s_coprime a.v_dvd).symm

theorem unique {L u : ℕ} (a b : SquarefreeFrequency L u) : a = b := by
  obtain ⟨hkernel, hw⟩ := squarefree_square_decomposition_unique
    a.kernel_squarefree b.kernel_squarefree a.w_pos b.w_pos (a.value.trans b.value.symm)
  have hv : a.v = b.v := by rw [a.v_eq_gcd, b.v_eq_gcd, hkernel]
  have hs : a.s = b.s := by
    rw [hv] at hkernel
    exact Nat.eq_of_mul_eq_mul_right b.v_pos hkernel
  cases a
  cases b
  simp_all

theorem s_squarefree {L u : ℕ} (a : SquarefreeFrequency L u) : Squarefree a.s :=
  a.kernel_squarefree.of_mul_left

theorem v_squarefree {L u : ℕ} (a : SquarefreeFrequency L u) : Squarefree a.v :=
  a.kernel_squarefree.of_mul_right

theorem s_le {L u : ℕ} (a : SquarefreeFrequency L u) : a.s ≤ u := by
  calc
    a.s ≤ a.s * a.v := Nat.le_mul_of_pos_right _ a.v_pos
    _ ≤ a.s * a.v * a.w ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos a.w_pos _)
    _ = u := a.value

theorem w_sq_le {L u : ℕ} (a : SquarefreeFrequency L u) : a.w ^ 2 ≤ u := by
  calc
    a.w ^ 2 ≤ a.s * a.v * a.w ^ 2 := Nat.le_mul_of_pos_left _ (Nat.mul_pos a.s_pos a.v_pos)
    _ = u := a.value

end SquarefreeFrequency

end Ostmann

end OAI
