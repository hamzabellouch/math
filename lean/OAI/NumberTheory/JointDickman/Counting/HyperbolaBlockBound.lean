import OAI.NumberTheory.JointDickman.Amplification.HyperbolaRounding
import OAI.NumberTheory.JointDickman.Arithmetic.NaturalPrimeRectangle

namespace OAI

/-! # From prime rectangles to a truncated hyperbola block -/
namespace JointDickman
open Finset

lemma prime_subset_log_sum_le (P : Finset ℕ) (Q : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (∑ p ∈ P, Real.log p) ≤ Real.log 4*Q := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE Q, Real.log p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_primesLE.mpr ⟨(hP p hp).2,(hP p hp).1⟩
      · intro p hp hnot
        exact Real.log_natCast_nonneg p
    _ = Chebyshev.theta Q := (Chebyshev.theta_eq_sum_primesLE_log _).symm
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

lemma rounded_hyperbola_norm_le (P : Finset ℕ) (M : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ) (Z D H Q : ℕ) (T : ℝ)
    (hD : 0 < D) (hZ : ∀ p ∈ P, Z ≤ M p)
    (hH : ∀ p ∈ P, M p/D < H)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (hc : ∀ p ∈ P, ∀ m ∈ Ioc Z (M p), ‖c p m‖ ≤ Real.log p)
    (hrect : ∀ k ∈ range H,
      ‖∑ p ∈ P.filter (fun p => M p/D=k),
        ∑ m ∈ Ioc Z (max Z (D*k)), c p m‖ ≤ T) :
    ‖∑ p ∈ P, ∑ m ∈ Ioc Z (M p), c p m‖ ≤
      (D:ℝ)*Real.log 4*Q + H*T := by
  let S := ∑ p ∈ P, ∑ m ∈ Ioc Z (M p), c p m
  let A := ∑ p ∈ P, ∑ m ∈ Ioc Z (max Z (D*(M p/D))), c p m
  have herr : ‖S-A‖ ≤ (D:ℝ)*Real.log 4*Q := by
    apply (rounded_hyperbola_error P M c Z D hD hZ hc).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (prime_subset_log_sum_le P Q hP) (Nat.cast_nonneg D)
  have hA : ‖A‖ ≤ (H:ℝ)*T := by
    dsimp [A]
    rw [rounded_hyperbola_rectangles P M c Z D H hH]
    apply (norm_sum_le _ _).trans
    simpa using sum_le_sum hrect
  calc
    _ = ‖(S-A)+A‖ := by congr 1; dsimp [S]; abel
    _ ≤ ‖S-A‖+‖A‖ := norm_add_le _ _
    _ ≤ _ := add_le_add herr hA

/-- A block with arbitrary integer upper endpoints is controlled by H rectangles
and a rounding error of width floor(U/H)+1. -/
theorem prime_hyperbola_block_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (M : ℕ → ℕ) (b c : ℕ → ℂ) (Z U H Q q a : ℕ),
    0 < H → 2 ≤ Q → 0 < q → a.Coprime q →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) → (∀ p ∈ P, Z ≤ M p ∧ M p ≤ U) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ P, ∑ m ∈ Ioc Z (M p), b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤
      ((U/H+1:ℕ):ℝ)*Real.log 4*Q + (H:ℝ)*Real.sqrt
        (C*((Q:ℝ)*Real.log Q*(U:ℝ)^2 + Q*(U:ℝ)^2*Q*(1+Real.log q)/q +
          Q*U*Q + Q*U*q*(1+Real.log Q))) := by
  classical
  obtain ⟨C,hC,hrectangle⟩ := natural_prime_rational_rectangle_bound
  refine ⟨C,hC,?_⟩
  intro P M b c Z U H Q q a hH hQ hq ha hP hM hb hc
  let D := U/H+1
  have hD : 0 < D := Nat.succ_pos _
  have hcell (p : ℕ) (hp : p ∈ P) : M p/D < H :=
    (Nat.div_le_div_right (hM p hp).2).trans_lt (quotient_cell_count U H hH)
  have hcoeff (p : ℕ) (hp : p ∈ P) (m : ℕ) (_hm : m ∈ Ioc Z (M p)) :
      ‖b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤ Real.log p := by
    rw [norm_mul,norm_mul,show ‖additivePhase ((a:ℝ)/q*p*m)‖=1 from
      Complex.norm_exp_ofReal_mul_I _,mul_one]
    exact (mul_le_mul_of_nonneg_left (hc m) (norm_nonneg _)).trans
      (by simpa using hb p hp)
  apply rounded_hyperbola_norm_le P M
    (fun p m => b p*c m*additivePhase ((a:ℝ)/q*p*m)) Z D H Q _ hD
    (fun p hp => (hM p hp).1) hcell hP hcoeff
  intro k hk
  let R := P.filter (fun p => M p/D=k)
  by_cases hempty : R=∅
  · simp only [show P.filter (fun p => M p/D=k)=∅ from hempty,sum_empty,norm_zero]
    exact Real.sqrt_nonneg _
  obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hempty
  have hpP := (mem_filter.mp hp).1
  have hpk := (mem_filter.mp hp).2
  have hround : D*(M p/D) ≤ M p := by
    simpa [mul_comm] using Nat.div_mul_le_self (M p) D
  have hKU : max Z (D*k) ≤ U := max_le ((hM p hpP).1.trans (hM p hpP).2)
    (by rw [←hpk]; exact hround.trans (hM p hpP).2)
  apply Real.le_sqrt_of_sq_le
  apply hrectangle Q U q a Z (max Z (D*k)) R b c hQ hq ha (le_max_left _ _)
    ((Nat.sub_le _ _).trans hKU)
    (fun p hp => hP p (mem_filter.mp hp).1)
  · intro p hp
    have hpP := (mem_filter.mp hp).1
    exact (hb p hpP).trans (Real.log_le_log (by exact_mod_cast (hP p hpP).1.pos)
      (by exact_mod_cast (hP p hpP).2))
  · exact hc

end JointDickman

end OAI
