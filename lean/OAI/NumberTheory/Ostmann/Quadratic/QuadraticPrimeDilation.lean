import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPrimeTwist

namespace OAI

/-! # A finite prime-dilation comparison between actual row matrices -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_prime_dilation {P S T : Finset ℕ} {N R : ℕ} {U : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hP₀ : 0 < P.card)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ R)
    (hmap : ∀ p ∈ P, ∀ m ∈ S, ¬p ∣ m → p * m ∈ T)
    (hcount : 2 * (2 * Nat.log 2 N + Nat.log 2 R) ≤ P.card)
    (hU : 0 ≤ U) (hT : QuadraticRowBound T N U) :
    QuadraticRowBound S N (4 * U) := by
  let A := quadraticRowNorm S N
  let L : ℝ := 2 * (Nat.log 2 N : ℝ) + Nat.log 2 R
  let Q : ℝ := P.card
  have hA : 0 ≤ A := quadraticRowNorm_nonneg S N
  have hAb : QuadraticRowBound S N A := quadraticRowNorm_bound S N
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast hP₀
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLQ : 2 * L ≤ Q := by dsimp [L, Q]; exact_mod_cast hcount
  have hgood (p : ℕ) (hp : p ∈ P) (v : ℕ → ℂ) :
      (∑ m ∈ S.filter (fun m => ¬p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) ≤
        2 * U * quadraticSieveEnergy N v +
          2 * A * quadraticSieveEnergy N (fun n => if p ∣ n then v n else 0) := by
    have hfirst : (∑ m ∈ S.filter (fun m => ¬p ∣ m),
        ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2) ≤
        quadraticRowEnergy T N (quadraticPrimeTwist p v) := by
      apply Finset.sum_le_sum_of_injOn (fun m => p * m)
      · intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left (hP p hp).pos hab
      · intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        exact hmap p hp m (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2
      · intro m _
        rfl
      · intro m _ _
        exact sq_nonneg _
    have hsecond : (∑ m ∈ S.filter (fun m => ¬p ∣ m),
        ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2) ≤
        quadraticRowEnergy S N (fun n => if p ∣ n then v n else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have ht := (hT (quadraticPrimeTwist p v)).trans
      (mul_le_mul_of_nonneg_left (quadraticPrimeTwist_energy p N v) hU)
    calc
      _ ≤ ∑ m ∈ S.filter (fun m => ¬p ∣ m),
          (2 * ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2 +
            2 * ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2) :=
        Finset.sum_le_sum (fun m _ => quadratic_prime_twist_point_bound (hP p hp) N v m)
      _ = 2 * (∑ m ∈ S.filter (fun m => ¬p ∣ m),
          ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2) +
          2 * (∑ m ∈ S.filter (fun m => ¬p ∣ m),
            ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
        have h₁ := hfirst.trans ht
        have h₂ := hsecond.trans (hAb (fun n => if p ∣ n then v n else 0))
        linarith
  have hall (v : ℕ → ℂ) : Q * quadraticRowEnergy S N v ≤
      (2 * Q * U + L * A) * quadraticSieveEnergy N v := by
    have hsplit : Q * quadraticRowEnergy S N v =
        (∑ p ∈ P, ∑ m ∈ S.filter (fun m => ¬p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) +
        ∑ p ∈ P, ∑ m ∈ S.filter (fun m => p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      have hs (p : ℕ) : (∑ m ∈ S.filter (fun m => ¬p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) +
          (∑ m ∈ S.filter (fun m => p ∣ m), ‖quadraticTransposeSum N v m‖ ^ 2) =
          quadraticRowEnergy S N v := by
        simpa only [not_not, quadraticRowEnergy] using Finset.sum_filter_add_sum_filter_not S
          (fun m => ¬p ∣ m) (fun m => ‖quadraticTransposeSum N v m‖ ^ 2)
      simp_rw [hs]
      simp only [Q, Finset.sum_const, nsmul_eq_mul]
    have hg := Finset.sum_le_sum (fun p hp => hgood p hp v)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hg
    rw [← Finset.mul_sum] at hg
    have he := mul_le_mul_of_nonneg_left (quadratic_prime_restricted_energy hP N v)
      (show 0 ≤ 2 * A by positivity)
    have hb := (quadratic_prime_bad_rows hP hS N v).trans
      (mul_le_mul_of_nonneg_left (hAb v) (Nat.cast_nonneg _))
    rw [hsplit]
    dsimp [Q, L]
    nlinarith only [hg, he, hb]
  let W := (2 * Q * U + L * A) / Q
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hWb : QuadraticRowBound S N W := by
    intro v
    apply (mul_le_mul_iff_left₀ hQ).mp
    have hh := hall v
    convert hh using 1 <;> (try dsimp only [W]) <;> field_simp
  have hupper := (le_div_iff₀ hQ).mp (quadraticRowNorm_le hW hWb)
  have hhalf := mul_le_mul_of_nonneg_right hLQ hA
  have hprod : Q * A ≤ Q * (4 * U) := by nlinarith only [hupper, hhalf]
  have hfinal : A ≤ 4 * U := by nlinarith only [hprod, hQ]
  exact hAb.mono_constant hfinal

end Ostmann

end OAI
