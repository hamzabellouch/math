import OAI.Combinatorics.EditDistance.UpperBase

namespace OAI

/-!
# Uniform finite-cut embeddings at recursive capacities
-/

namespace EditUpperParameters
open scoped BigOperators

lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh

lemma scale_count_bound {l : ℕ} (hl : 0 < l) :
    ((Nat.log 2 l+1 : ℕ) : ℝ) ≤ 2*(1+Real.log (l : ℝ)) := by
  have hpow := Nat.pow_log_le_self 2 (Nat.ne_of_gt hl)
  have hpr : (2 : ℝ)^(Nat.log 2 l) ≤ l := by exact_mod_cast hpow
  have hh := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hpr
  rw [Real.log_pow] at hh
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hl)
  have hm : 0 ≤ (Nat.log 2 l : ℝ) := Nat.cast_nonneg _
  have h2 := log_two_bounds
  push_cast
  nlinarith

lemma log_square_bound {l : ℕ} (hl : 0 < l) :
    Real.log (2*(l : ℝ)^2) ≤ 2*(1+Real.log (l : ℝ)) := by
  have hp : (0 : ℝ)<l := by exact_mod_cast hl
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hp.ne'),Real.log_pow]
  have h2 := log_two_bounds
  norm_num only [Nat.cast_ofNat]
  linarith

lemma step_constant_bound {b l : ℕ} (hl : 0 < l) {D : ℝ} (hD : 0 ≤ D) :
    16*((Nat.log 2 l+1 : ℕ) : ℝ)*(2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D) ≤
      512*(1+Real.log (l : ℝ))^2*((b : ℝ)+D) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hl)
  have hcount := scale_count_bound hl
  have hsq := log_square_bound hl
  have hsnn : 0 ≤ Real.log (2*(l : ℝ)^2) := Real.log_nonneg (by
    have hh : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith)
  have hb := Nat.cast_nonneg (α := ℝ) b
  have hm := Nat.cast_nonneg (α := ℝ) (Nat.log 2 l+1)
  have hleft : 2*(b : ℝ)+4*Real.log (2*(l : ℝ)^2)*D ≤ 2*b+8*(1+Real.log (l : ℝ))*D := by nlinarith
  calc
    _ ≤ 16*(2*(1+Real.log (l : ℝ)))*(2*b+8*(1+Real.log (l : ℝ))*D) := by
      apply mul_le_mul
      · nlinarith
      · exact hleft
      · positivity
      · positivity
    _ ≤ _ := by nlinarith [mul_nonneg hlog hb,mul_nonneg (sq_nonneg (1+Real.log (l : ℝ))) hD,
        mul_nonneg (sq_nonneg (Real.log (l : ℝ))) hb]

end EditUpperParameters

namespace EditUpper

universe u

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset EditDistortion EditWindow EditCutModel

noncomputable def growth (b N : ℕ) : ℝ := 1024*(1+(N : ℝ)*Real.log (b : ℝ))^2

lemma growth_ge {b N : ℕ} (hb : 1 ≤ b) : 1 ≤ growth b N := by
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  have hn := Nat.cast_nonneg (α := ℝ) N
  dsimp [growth]
  nlinarith [mul_nonneg hn hlog]

theorem exists_level (b N : ℕ) (hb : 1 ≤ b) (k : ℕ) (hk : k ≤ N)
    (A : Type u) [Fintype A] :
    ∃ M : Model (List A),
      (∀ x y : List A, x.length ≤ b^k → y.length ≤ b^k → (indel x y : ℝ) ≤ M.dist x y) ∧
      (∀ x y : List A, M.dist x y ≤ ((b : ℝ)+2)*(growth b N)^k*(indel x y : ℝ)) := by
  induction k generalizing A with
  | zero =>
    refine ⟨base,?_,?_⟩
    · intro x y hx hy
      exact base_lower x y (by simpa using hx) (by simpa using hy)
    · intro x y
      have hh := base_upper x y
      have hi := Nat.cast_nonneg (α := ℝ) (indel x y)
      simp only [pow_zero,mul_one]
      nlinarith [Nat.cast_nonneg (α := ℝ) b]
  | succ k ih =>
    obtain ⟨M,hlo,hup⟩ := ih (by omega) (Option A)
    let D := ((b : ℝ)+2)*(growth b N)^k
    have hP := growth_ge (N := N) hb
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hpow : 1 ≤ (growth b N)^k := one_le_pow₀ hP
    have hbD : (b : ℝ) ≤ D := by
      dsimp [D]
      have hb0 := Nat.cast_nonneg (α := ℝ) b
      nlinarith
    have hl : 0 < b^k := pow_pos (by omega) _
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
    have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg (by exact_mod_cast hb)
    have hT : 1+Real.log ((b^k : ℕ) : ℝ) ≤ 1+(N : ℝ)*Real.log (b : ℝ) := by
      rw [Nat.cast_pow,Real.log_pow]
      nlinarith
    have hTnn : 0 ≤ 1+Real.log ((b^k : ℕ) : ℝ) := by
      have hh : 0 ≤ Real.log ((b^k : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.one_le_pow k b (by omega)))
      linarith
    have hconst : 512*(1+Real.log ((b^k : ℕ) : ℝ))^2*((b : ℝ)+D) ≤
        ((b : ℝ)+2)*(growth b N)^(k+1) := by
      calc
        _ ≤ 512*(1+(N : ℝ)*Real.log (b : ℝ))^2*(2*D) := by
          apply mul_le_mul
          · gcongr
          · linarith
          · positivity
          · positivity
        _ = _ := by dsimp [D,growth]; rw [pow_succ]; ring
    refine ⟨lift M b (b^k),?_,?_⟩
    · intro x y hx hy
      apply lift_lower M b (b^k) hl hlo x y
      · simpa only [pow_succ,Nat.mul_comm] using hx
      · simpa only [pow_succ,Nat.mul_comm] using hy
    · apply model_indel_lipschitz
      intro p q a
      exact (lift_insert_raw M hD hup p q a b (b^k) hl).trans
        ((EditUpperParameters.step_constant_bound hl hD).trans hconst)

end EditUpper

end OAI
