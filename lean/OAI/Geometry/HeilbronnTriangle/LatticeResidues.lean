import Mathlib

namespace OAI


namespace Problem355.LatticeResidues

open Finset

theorem eq_of_ediv_eq_of_emod_eq {a b q : ℤ}
    (hdiv : a / q = b / q) (hmod : a % q = b % q) : a = b := by
  calc
    a = a / q * q + a % q := (Int.ediv_mul_add_emod a q).symm
    _ = b / q * q + b % q := by rw [hdiv, hmod]
    _ = b := Int.ediv_mul_add_emod b q

theorem card_residue_interval_le (S : Finset ℤ) (lo hi q r : ℤ)
    (hq : 0 < q)
    (hS : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi ∧ x % q = r) :
    S.card ≤ (hi / q - lo / q + 1).toNat := by
  have hinj : Set.InjOn (fun x : ℤ => x / q) S := by
    intro a ha b hb hab
    exact eq_of_ediv_eq_of_emod_eq hab ((hS a ha).2.2.trans (hS b hb).2.2.symm)
  have hsub : S.image (fun x : ℤ => x / q) ⊆ Icc (lo / q) (hi / q) := by
    intro x hx
    rcases mem_image.mp hx with ⟨a, ha, rfl⟩
    exact mem_Icc.mpr ⟨Int.ediv_le_ediv hq (hS a ha).1,
      Int.ediv_le_ediv hq (hS a ha).2.1⟩
  calc
    S.card = (S.image (fun x : ℤ => x / q)).card := (card_image_of_injOn hinj).symm
    _ ≤ (Icc (lo / q) (hi / q)).card := card_le_card hsub
    _ = (hi / q - lo / q + 1).toNat := by
      rw [Int.card_Icc]
      congr 1
      omega

theorem card_residue_box_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → ℤ)) (lo hi r : ι → ℤ) (q : ℤ)
    (hq : 0 < q)
    (hS : ∀ x ∈ S, ∀ i, lo i ≤ x i ∧ x i ≤ hi i ∧ x i % q = r i) :
    S.card ≤ ∏ i, (hi i / q - lo i / q + 1).toNat := by
  classical
  let T : ι → Finset ℤ := fun i => (Icc (lo i) (hi i)).filter (fun x => x % q = r i)
  have hsub : S ⊆ Fintype.piFinset T := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hS x hx i).1, (hS x hx i).2.1⟩,
      (hS x hx i).2.2⟩
  calc
    S.card ≤ (Fintype.piFinset T).card := card_le_card hsub
    _ = ∏ i, (T i).card := Fintype.card_piFinset T
    _ ≤ ∏ i, (hi i / q - lo i / q + 1).toNat := by
      apply prod_le_prod
      intro i _
      apply card_residue_interval_le (T i) (lo i) (hi i) q (r i) hq
      intro x hx
      rcases mem_filter.mp hx with ⟨hbox, hmod⟩
      exact ⟨(mem_Icc.mp hbox).1, (mem_Icc.mp hbox).2, hmod⟩

theorem card_residue_cube_le (d : ℕ) (S : Finset (Fin d → ℤ))
    (lo hi q : ℤ) (r : Fin d → ℤ) (hq : 0 < q)
    (hS : ∀ x ∈ S, ∀ i, lo ≤ x i ∧ x i ≤ hi ∧ x i % q = r i) :
    S.card ≤ (hi / q - lo / q + 1).toNat ^ d := by
  simpa using card_residue_box_le S (fun _ => lo) (fun _ => hi) r q hq hS

theorem card_residue_classes_cube_le (d : ℕ) (S A : Finset (Fin d → ℤ))
    (lo hi q : ℤ) (hq : 0 < q)
    (hbox : ∀ x ∈ S, ∀ i, lo ≤ x i ∧ x i ≤ hi)
    (hres : ∀ x ∈ S, (fun i => x i % q) ∈ A) :
    S.card ≤ A.card * (hi / q - lo / q + 1).toNat ^ d := by
  classical
  calc
    S.card = ∑ r ∈ A, (S.filter (fun x => (fun i => x i % q) = r)).card :=
      card_eq_sum_card_fiberwise hres
    _ ≤ ∑ _r ∈ A, (hi / q - lo / q + 1).toNat ^ d := by
      apply sum_le_sum
      intro r _hr
      apply card_residue_cube_le d _ lo hi q r hq
      intro x hx i
      rcases mem_filter.mp hx with ⟨hxS, hxres⟩
      exact ⟨(hbox x hxS i).1, (hbox x hxS i).2, congrFun hxres i⟩
    _ = A.card * (hi / q - lo / q + 1).toNat ^ d := by simp

theorem symmetric_quotient_bound (R q : ℤ) (_hR : 0 ≤ R) (hq : 0 < q) :
    (R / q - (-R) / q + 1).toNat ≤ (2 * (R / q) + 2).toNat := by
  apply Int.toNat_le_toNat
  rw [Int.neg_ediv]
  have hsign : q.sign = 1 := Int.sign_eq_one_of_pos hq
  rw [hsign]
  split_ifs <;> omega

theorem card_symmetric_residue_classes_le (d : ℕ) (S A : Finset (Fin d → ℤ))
    (R q : ℤ) (hR : 0 ≤ R) (hq : 0 < q)
    (hbox : ∀ x ∈ S, ∀ i, -R ≤ x i ∧ x i ≤ R)
    (hres : ∀ x ∈ S, (fun i => x i % q) ∈ A) :
    S.card ≤ A.card * (2 * (R / q) + 2).toNat ^ d := by
  exact (card_residue_classes_cube_le d S A (-R) R q hq hbox hres).trans
    (Nat.mul_le_mul_left A.card (Nat.pow_le_pow_left (symmetric_quotient_bound R q hR hq) d))

theorem card_symmetric_residue_classes_mul_pow_le (d : ℕ)
    (S A : Finset (Fin d → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ))
    (hres : ∀ x ∈ S, (fun i => x i % (q : ℤ)) ∈ A) :
    S.card * q ^ d ≤ A.card * (4 * R) ^ d := by
  have hs : S.card ≤ A.card * (2 * (R / q) + 2) ^ d := by
    have h := card_symmetric_residue_classes_le d S A (R : ℤ) (q : ℤ)
      (by positivity) (by exact_mod_cast hq) hbox hres
    rw [← Int.natCast_ediv, ← Nat.cast_ofNat, ← Nat.cast_mul,
      ← Nat.cast_ofNat, ← Nat.cast_add, Int.toNat_natCast] at h
    exact h
  have hscale : (2 * (R / q) + 2) * q ≤ 4 * R := by
    have hfloor : R / q * q ≤ R := Nat.div_mul_le_self R q
    nlinarith
  calc
    S.card * q ^ d ≤ (A.card * (2 * (R / q) + 2) ^ d) * q ^ d :=
      Nat.mul_le_mul_right (q ^ d) hs
    _ = A.card * ((2 * (R / q) + 2) * q) ^ d := by rw [mul_pow]; ring
    _ ≤ A.card * (4 * R) ^ d :=
      Nat.mul_le_mul_left A.card (Nat.pow_le_pow_left hscale d)

theorem card_thin_residue_classes_mul_sq_le
    (S A : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (hA : A.card ≤ q)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ))
    (hres : ∀ x ∈ S, (fun i => x i % (q : ℤ)) ∈ A) :
    S.card * q ^ 2 ≤ (4 * R) ^ 3 := by
  have h := card_symmetric_residue_classes_mul_pow_le 3 S A R q hq hqR hbox hres
  have h' : (S.card * q ^ 2) * q ≤ ((4 * R) ^ 3) * q := by
    calc
      (S.card * q ^ 2) * q = S.card * q ^ 3 := by ring
      _ ≤ A.card * (4 * R) ^ 3 := h
      _ ≤ q * (4 * R) ^ 3 := Nat.mul_le_mul_right _ hA
      _ = ((4 * R) ^ 3) * q := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right h' hq

theorem card_modular_line_mul_sq_le
    (S : Finset (Fin 3 → ℤ)) (R q : ℕ) (hq : 0 < q) (hqR : q ≤ R)
    (delta : Fin 3 → ZMod q)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ (R : ℤ))
    (hline : ∀ x ∈ S, ∃ a : ZMod q, ∀ i, (x i : ZMod q) = a * delta i) :
    S.card * q ^ 2 ≤ (4 * R) ^ 3 := by
  classical
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let A : Finset (Fin 3 → ℤ) :=
    univ.image (fun a : ZMod q => fun i => ((a * delta i).val : ℤ))
  apply card_thin_residue_classes_mul_sq_le S A R q hq hqR
  · calc
      A.card ≤ (univ : Finset (ZMod q)).card := card_image_le
      _ = q := by simp
  · exact hbox
  · intro x hx
    obtain ⟨a, ha⟩ := hline x hx
    apply mem_image.mpr
    refine ⟨a, mem_univ _, ?_⟩
    funext i
    rw [← ha i, ZMod.val_intCast]

end Problem355.LatticeResidues

end OAI
