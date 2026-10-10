import OAI.Combinatorics.FiniteCircle.UpperParameters

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem one_letter_embedding {α : Type*} [Fintype α] :
    ∃ M : ℕ, ∃ F : List.Vector α 1 → Fin M → ℝ, ∀ x y,
      (deficit x.val y.val : ℝ) ≤ coordDist F x y ∧
      coordDist F x y ≤ 2 * deficit x.val y.val := by
  classical
  let X := List.Vector α 1
  let : DecidableEq X := Classical.decEq X
  let e := Fintype.equivFin X
  let F : X → Fin (Fintype.card X) → ℝ := fun x i => if e.symm i = x then 1 else 0
  have he (x y : X) : coordDist F x y = if x = y then 0 else 2 := by
    unfold coordDist
    rw [← e.sum_comp (fun i => |F x i - F y i|)]
    simp only [F, Equiv.symm_apply_apply]
    by_cases h : x = y
    · simp [h]
    · rw [ite_eq_right h]
      have hh (i : X) : |(if i = x then (1:ℝ) else 0) - (if i = y then 1 else 0)| =
          (if i = x then 1 else 0) + (if i = y then 1 else 0) := by
        split_ifs <;> simp_all
      simp_rw [hh]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  have hd (x y : X) : deficit x.val y.val = if x = y then 0 else 1 := by
    by_cases h : x = y
    · simp [h, deficit]
    · rw [ite_eq_right h]
      have hx : x.val.length = 1 := x.property
      have hy : y.val.length = 1 := y.property
      have hu := lcs_le_length_left x.val y.val
      have h0 : lcs x.val y.val = 0 := by
        by_contra hc
        have hl : lcs x.val y.val = 1 := by omega
        obtain ⟨z, hz, hw, heq⟩ := lcs_exists x.val y.val
        have hzx : z = x.val := hz.eq_of_length (by omega)
        have hzy : z = y.val := hw.eq_of_length (by omega)
        exact h (Subtype.ext (hzx.symm.trans hzy))
      simp [deficit, hx, h0]
  refine ⟨Fintype.card X, F, fun x y => ?_⟩
  rw [he, hd]
  split_ifs <;> norm_num

theorem histogram_factor_le {b m n : ℕ} (hmn : m ≤ n) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    16 * ((Nat.log 2 m : ℝ)+1) * ((b:ℝ) + 16 * Real.log ((m:ℝ)+1) * Λ) ≤
      512 * ((Nat.log 2 n : ℝ)+1)^2 * ((b:ℝ)+Λ) := by
  let K : ℝ := (Nat.log 2 n : ℝ)+1
  have hK : 1 ≤ K := by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]
  have hK0 : 0 ≤ K := by linarith
  have hl : Real.log ((m:ℝ)+1) ≤ K :=
    (log_add_one_le_dyadic_count m).trans (by
      dsimp [K]
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hmn) 1)
  have hmK : (Nat.log 2 m : ℝ)+1 ≤ K := by
    dsimp [K]
    exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hmn) 1
  have hn : (0:ℝ) ≤ b := Nat.cast_nonneg b
  have hl0 : 0 ≤ Real.log ((m:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
  calc
    _ ≤ 16*K*((b:ℝ)+16*K*Λ) := by gcongr
    _ ≤ 512*K^2*((b:ℝ)+Λ) := by
      have hKb : K*(b:ℝ) ≤ K^2*b := mul_le_mul_of_nonneg_right (by nlinarith only [hK] : K ≤ K^2) hn
      have hKΛ : 0 ≤ K^2*Λ := mul_nonneg (sq_nonneg K) hΛ
      nlinarith only [hKb, hKΛ, mul_nonneg (sq_nonneg K) hn]

theorem power_length_embedding {α : Type*} [Fintype α] (a : α) {b H : ℕ} (hb : 2 ≤ b) :
    ∃ M : ℕ, ∃ F : List.Vector α (b^H) → Fin M → ℝ, ∀ x y,
      (deficit x.val y.val : ℝ) ≤ coordDist F x y ∧
      coordDist F x y ≤ (b * (1024 * ((Nat.log 2 (b^H) : ℝ)+1)^2)^H) * deficit x.val y.val := by
  let n := b^H
  let B : ℝ := 1024 * ((Nat.log 2 n : ℝ)+1)^2
  have hb0 : 0 < b := by omega
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hB : 1 ≤ B := by
    have h : (1:ℝ) ≤ (Nat.log 2 n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]
    dsimp [B]
    nlinarith
  have hB0 : 0 ≤ B := by linarith
  have all (k : ℕ) (hk : k ≤ H) :
      ∃ M : ℕ, ∃ F : List.Vector α (b^k) → Fin M → ℝ, ∀ x y,
        (deficit x.val y.val : ℝ) ≤ coordDist F x y ∧
        coordDist F x y ≤ ((b:ℝ)*B^k) * deficit x.val y.val := by
    induction k with
    | zero =>
      obtain ⟨M, F, hF⟩ := one_letter_embedding (α := α)
      refine ⟨M, F, fun x y => ⟨(hF x y).1, ?_⟩⟩
      simpa using (hF x y).2.trans (mul_le_mul_of_nonneg_right hbR (Nat.cast_nonneg _))
    | succ k ih =>
      obtain ⟨M, F, hF⟩ := ih (by omega)
      have hΛ : (0:ℝ) ≤ (b:ℝ)*B^k := by positivity
      obtain ⟨M', F', hF'⟩ := histogram_embedding_step a (pow_pos hb0 k) b F ((b:ℝ)*B^k)
        hΛ (fun x y => (hF x y).1) (fun x y => (hF x y).2)
      have hmn : b^k ≤ n := Nat.pow_le_pow_right hb0 (by omega)
      have hfactor := histogram_factor_le (b := b) hmn hΛ
      have hΛb : (b:ℝ) ≤ (b:ℝ)*B^k := by
        exact le_mul_of_one_le_right (Nat.cast_nonneg b) (one_le_pow₀ hB)
      have hfac : 16 * ((Nat.log 2 (b^k) : ℝ)+1) *
          ((b:ℝ)+16*Real.log (((b^k : ℕ):ℝ)+1)*((b:ℝ)*B^k)) ≤ (b:ℝ)*B^(k+1) := by
        calc
          _ ≤ 512*((Nat.log 2 n : ℝ)+1)^2*((b:ℝ)+(b:ℝ)*B^k) := hfactor
          _ ≤ 512*((Nat.log 2 n : ℝ)+1)^2*(2*((b:ℝ)*B^k)) := by gcongr; linarith
          _ = _ := by dsimp [B]; rw [pow_succ]; ring
      rw [pow_succ']
      refine ⟨M', F', fun x y => ⟨(hF' x y).1, ?_⟩⟩
      exact (hF' x y).2.trans (mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg _))
  exact all H le_rfl

theorem uniform_upper_of_log_large {α : Type*} [Fintype α] {d : ℕ}
    (hd : 16 ≤ Real.log d) :
    ∃ M : ℕ, ∃ F : Words α d → Fin M → ℝ, ∀ x y,
      (editDistance x.val y.val : ℝ) ≤ coordDist F x y ∧
      coordDist F x y ≤ Real.exp (32 * exponentScale d) * editDistance x.val y.val := by
  obtain ⟨b, H, hb, _, hdn, hbound⟩ := exists_power_parameters hd
  obtain ⟨M, G, hG⟩ := power_length_embedding (α := Option α) none (H := H) hb
  let pad : Words α d → List.Vector (Option α) (b^H) := fun x =>
    ⟨freshPad (b^H) x.val, length_freshPad (x.property.trans hdn)⟩
  let F : Words α d → Fin M → ℝ := fun x i => 2 * G (pad x) i
  have he (x y : Words α d) : coordDist F x y = 2*coordDist G (pad x) (pad y) := by
    simp only [coordDist, F, ← mul_sub, abs_mul, show |(2:ℝ)| = 2 by norm_num, Finset.mul_sum]
  have hpad (x y : Words α d) : deficit (pad x).val (pad y).val = unequalDeficit x.val y.val :=
    deficit_freshPad (x.property.trans hdn) (y.property.trans hdn)
  refine ⟨M, F, fun x y => ⟨?_, ?_⟩⟩
  · rw [he]
    have h := (hG (pad x) (pad y)).1
    rw [hpad] at h
    have he := editDistance_le_two_unequalDeficit x.val y.val
    exact (by exact_mod_cast he : (editDistance x.val y.val : ℝ) ≤ 2*(unequalDeficit x.val y.val:ℝ)).trans (by linarith)
  · rw [he]
    have h := (hG (pad x) (pad y)).2
    rw [hpad] at h
    have hq : (unequalDeficit x.val y.val:ℝ) ≤ editDistance x.val y.val :=
      by exact_mod_cast unequalDeficit_le_editDistance x.val y.val
    have hB : 0 ≤ (b:ℝ)*(1024*((Nat.log 2 (b^H):ℝ)+1)^2)^H := by positivity
    calc
      _ ≤ 2*((b:ℝ)*(1024*((Nat.log 2 (b^H):ℝ)+1)^2)^H) * unequalDeficit x.val y.val := by linarith
      _ ≤ 2*((b:ℝ)*(1024*((Nat.log 2 (b^H):ℝ)+1)^2)^H) * editDistance x.val y.val := by gcongr
      _ ≤ Real.exp (32*exponentScale d) * editDistance x.val y.val := by
        gcongr
        dsimp [exponentScale]
        nlinarith only [hbound, hB]

theorem uniform_upper : ∃ d₀ : ℕ, UniformUpper 32 d₀ := by
  refine ⟨⌈Real.exp 16⌉₊, fun α _ _ d hd => ?_⟩
  have hdexp : Real.exp 16 ≤ (d:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hd)
  have hlog : 16 ≤ Real.log d := by
    have h := Real.log_le_log (Real.exp_pos 16) hdexp
    simpa only [Real.log_exp] using h
  exact uniform_upper_of_log_large hlog

end FiniteCircle

end OAI
