import Mathlib

namespace OAI


namespace Problem355.LatticeShell

open Finset

theorem sum_powers_le_twice_last (B : ℝ) (hB : 2 ≤ B)
    (f : ℕ → ℕ) (hf : ∀ j, f j + 1 ≤ f (j + 1)) (e : ℕ) :
    ∑ j ∈ range (e + 1), B ^ f j ≤ 2 * B ^ f e := by
  have hB0 : 0 ≤ B := by linarith
  induction e with
  | zero =>
    simp only [zero_add, sum_range_one]
    linarith [pow_nonneg hB0 (f 0)]
  | succ e ih =>
    rw [sum_range_succ]
    have hstep : 2 * B ^ f e ≤ B ^ f (e + 1) := by
      calc
        2 * B ^ f e ≤ B * B ^ f e :=
          mul_le_mul_of_nonneg_right hB (pow_nonneg hB0 _)
        _ = B ^ (f e + 1) := by rw [pow_succ]; ring
        _ ≤ B ^ f (e + 1) := pow_le_pow_right₀ (by linarith) (hf e)
    linarith

theorem sum_divisor_exponents_le (B : ℝ) (hB : 2 ≤ B)
    (b e : ℕ) (hbe : b ≤ e) :
    ∑ j ∈ range (e + 1), B ^ (2 * j - (j - b)) ≤ 2 * B ^ (b + e) := by
  have hstep : ∀ j : ℕ,
      (2 * j - (j - b)) + 1 ≤ 2 * (j + 1) - (j + 1 - b) := by
    intro j
    omega
  have hlast : 2 * e - (e - b) = b + e := by omega
  simpa only [hlast] using
    sum_powers_le_twice_last B hB (fun j => 2 * j - (j - b)) hstep e

theorem card_box_residue_le {d : ℕ} (s : Finset (Fin d → ℤ))
    (lo hi q : ℤ) (hq : 0 < q) (r : Fin d → ℤ)
    (hbox : ∀ x ∈ s, ∀ i, lo ≤ x i ∧ x i ≤ hi)
    (hres : ∀ x ∈ s, ∀ i, x i % q = r i) :
    s.card ≤ (hi / q + 1 - lo / q).toNat ^ d := by
  classical
  let F : ↥s → (Fin d → ↥(Icc (lo / q) (hi / q))) := fun x i =>
    ⟨x.val i / q, mem_Icc.mpr
      ⟨Int.ediv_le_ediv hq (hbox x.val x.property i).1,
       Int.ediv_le_ediv hq (hbox x.val x.property i).2⟩⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hdiv : x.val i / q = y.val i / q :=
      congrArg Subtype.val (congrFun hxy i)
    calc
      x.val i = x.val i % q + q * (x.val i / q) :=
        (Int.emod_add_mul_ediv _ _).symm
      _ = y.val i % q + q * (y.val i / q) := by
        rw [hdiv, hres x.val x.property i, hres y.val y.property i]
      _ = y.val i := Int.emod_add_mul_ediv _ _
  have hc := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin,
    Int.card_Icc] using hc

theorem symmetric_quotient_length_le (R q : ℕ) (hq : 0 < q) :
    ((R : ℤ) / q + 1 - (-(R : ℤ)) / q).toNat ≤ 2 * (R / q) + 2 := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  apply Int.toNat_le.mpr
  rw [Int.neg_ediv]
  have hs : (q : ℤ).sign = 1 := Int.sign_eq_one_of_pos hqz
  rw [hs]
  push_cast
  rw [← Int.natCast_ediv]
  split_ifs <;> omega

theorem card_symmetric_box_residue_le {d : ℕ} (s : Finset (Fin d → ℤ))
    (R q : ℕ) (hq : 0 < q) (r : Fin d → ℤ)
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, ∀ i, x i % (q : ℤ) = r i) :
    s.card ≤ (2 * (R / q) + 2) ^ d := by
  calc
    s.card ≤ ((R : ℤ) / q + 1 - (-(R : ℤ)) / q).toNat ^ d :=
      card_box_residue_le s (-(R : ℤ)) R q (by exact_mod_cast hq) r hbox hres
    _ ≤ (2 * (R / q) + 2) ^ d :=
      Nat.pow_le_pow_left (symmetric_quotient_length_le R q hq) d

theorem card_symmetric_box_zmod_residue_le {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q)
    (r : Fin d → ZMod q)
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, ∀ i, (x i : ZMod q) = r i) :
    s.card ≤ (2 * (R / q) + 2) ^ d := by
  let : NeZero q := ⟨by omega⟩
  apply card_symmetric_box_residue_le s R q hq (fun i => ((r i).val : ℤ)) hbox
  intro x hx i
  rw [← ZMod.val_intCast, hres x hx i]

theorem card_symmetric_box_residues_le {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q)
    (T : Finset (Fin d → ZMod q))
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T) :
    s.card ≤ (2 * (R / q) + 2) ^ d * T.card := by
  classical
  apply card_le_mul_card_image_of_maps_to hres
  intro r hr
  apply card_symmetric_box_zmod_residue_le _ R q hq r
  · intro x hx i
    exact hbox x (mem_filter.mp hx).1 i
  · intro x hx i
    exact congrFun (mem_filter.mp hx).2 i

theorem card_symmetric_box_residues_le_real {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (T : Finset (Fin d → ZMod q))
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T) :
    (s.card : ℝ) ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * (T.card : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : 1 ≤ (R : ℝ) / (q : ℝ) := by
    apply (le_div_iff₀ hq0).mpr
    simpa using (show (q : ℝ) ≤ R by exact_mod_cast hqR)
  have hdiv : ((R / q : ℕ) : ℝ) ≤ (R : ℝ) / (q : ℝ) := Nat.cast_div_le
  have hfactor : ((2 * (R / q) + 2 : ℕ) : ℝ) ≤ 4 * (R : ℝ) / (q : ℝ) := by
    push_cast
    rw [mul_div_assoc]
    linarith
  have hcount : (s.card : ℝ) ≤
      ((2 * (R / q) + 2 : ℕ) : ℝ) ^ d * (T.card : ℝ) := by
    exact_mod_cast card_symmetric_box_residues_le s R q hq T hbox hres
  exact hcount.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hfactor d) (by positivity))

theorem card_symmetric_box_of_residue_density_le {d : ℕ}
    (s : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (T : Finset (Fin d → ZMod q)) (D : ℝ) (hD : 0 < D)
    (hbox : ∀ x ∈ s, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ s, (fun i => (x i : ZMod q)) ∈ T)
    (hT : (T.card : ℝ) ≤ (q : ℝ) ^ d / D) :
    (s.card : ℝ) ≤ 4 ^ d * (R : ℝ) ^ d / D := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    (s.card : ℝ) ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * (T.card : ℝ) :=
      card_symmetric_box_residues_le_real s R q hq hqR T hbox hres
    _ ≤ (4 * (R : ℝ) / (q : ℝ)) ^ d * ((q : ℝ) ^ d / D) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 4 ^ d * (R : ℝ) ^ d / D := by
      rw [div_pow, mul_pow]
      field_simp

end Problem355.LatticeShell

end OAI
