import Mathlib

namespace OAI

section
noncomputable section
open Function

namespace CriticalPercolation.LinearGrowth
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

lemma eq_zero_of_bounded_nat_multiples (x : R) (C : ℝ)
    (h : ∀ n : ℕ, ‖(n:ℝ) • x‖≤C) : x=0 := by
  by_contra hx
  have hxpos : 0<‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨n,hn⟩ := exists_nat_gt (C/‖x‖)
  have hh := h n
  rw [norm_smul,Real.norm_natCast] at hh
  exact ((div_lt_iff₀ hxpos).mp hn).not_ge hh

lemma pow_mul_of_affine_step (a b c : R) (hab : a*b=b+c) (hac : a*c=c) :
    ∀ n : ℕ, a^n*b=b+(n:ℝ) • c := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,mul_add,mul_smul_comm,hab,hac]
    simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

lemma eq_one_of_power_bounded_unipotent (a : R) (hni : IsNilpotent (a-1))
    (C : ℝ) (hb : ∀ n : ℕ, ‖a^n‖≤C) : a=1 := by
  let N := a-1
  have hdrop : ∀ k : ℕ, N^k=0 → N=0 := by
    intro k
    induction k with
    | zero =>
      intro hz
      have ho : (1:R)=0 := by simpa only [pow_zero] using hz
      exact (mul_one N).symm.trans ((congrArg (N*·) ho).trans (mul_zero N))
    | succ k ih =>
      intro hz
      by_cases hk : k=0
      · simpa only [hk,zero_add,pow_one] using hz
      have hp : 1≤k := Nat.one_le_iff_ne_zero.mpr hk
      let b := N^(k-1)
      let c := N^k
      have hab : a*b=b+c := by
        have he : a=1+N := by dsimp [N]; noncomm_ring
        rw [he,add_mul,one_mul]
        congr 1
        dsimp [b,c]
        rw [←pow_succ',Nat.sub_add_cancel hp]
      have hac : a*c=c := by
        have he : a=1+N := by dsimp [N]; noncomm_ring
        rw [he,add_mul,one_mul]
        have hn : N*c=0 := by simpa only [c,←pow_succ'] using hz
        rw [hn,add_zero]
      have he : c=0 := by
        apply eq_zero_of_bounded_nat_multiples c ((C+1)*‖b‖)
        intro n
        have heq : (n:ℝ) • c=a^n*b-b := by
          rw [pow_mul_of_affine_step a b c hab hac n,add_sub_cancel_left]
        rw [heq]
        calc
          ‖a^n*b-b‖ ≤ ‖a^n*b‖+‖b‖ := norm_sub_le _ _
          _ ≤ C*‖b‖+‖b‖ := add_le_add ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))) le_rfl
          _ = (C+1)*‖b‖ := by ring
      exact ih he
  obtain ⟨k,hk⟩ := hni
  exact sub_eq_zero.mp (hdrop k hk)

end CriticalPercolation.LinearGrowth
end
end

end OAI
