import Mathlib

namespace OAI

/-!
Exact finite counting for the prescribed-match probability in
`polynomial-code.tex`, Lemma `lem:random-segments`.
The constraints identify distinct target coordinates with coordinates outside
that target set.
-/

namespace TreeEdit.BinaryLower.RandomMatching

open Function

variable {A I B : Type*}

/-- The coordinates outside the prescribed right endpoints are free. -/
noncomputable def constraintEquiv
    (l : I → A) (r : I ↪ A) (hdisj : ∀ i j, l i ≠ r j) :
    {f : A → B // ∀ i, f (l i) = f (r i)} ≃
      ({a : A // a ∉ Set.range r} → B) := by
  classical
  let extend (g : {a : A // a ∉ Set.range r} → B) (a : A) : B :=
    if h : a ∈ Set.range r then
      g ⟨l (Classical.choose h), by
        rintro ⟨j, hj⟩
        exact hdisj (Classical.choose h) j hj.symm⟩
    else g ⟨a, h⟩
  have hl (g : {a : A // a ∉ Set.range r} → B) (i : I) :
      extend g (l i) = g ⟨l i, by
        rintro ⟨j, hj⟩
        exact hdisj i j hj.symm⟩ := by
    simp only [extend]
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      exact False.elim (hdisj i j hj.symm)
    · rfl
  have hr (g : {a : A // a ∉ Set.range r} → B) (i : I) :
      extend g (r i) = g ⟨l i, by
        rintro ⟨j, hj⟩
        exact hdisj i j hj.symm⟩ := by
    simp only [extend]
    split_ifs with h
    · have heq : Classical.choose h = i := r.injective (Classical.choose_spec h)
      exact congrArg g (Subtype.ext (congrArg l heq))
    · exact False.elim (h ⟨i, rfl⟩)
  refine
    { toFun := fun f a => f.1 a.1
      invFun := fun g => ⟨extend g, fun i => (hl g i).trans (hr g i).symm⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    funext a
    dsimp only
    simp only [extend]
    split_ifs with h
    · exact (f.2 (Classical.choose h)).trans
        (congrArg f.1 (Classical.choose_spec h))
    · rfl
  · intro g
    funext a
    simp only [extend, dite_eq_right a.2]

/-- Each independent equality removes exactly one free coordinate. -/
theorem card_constraints [Fintype A] [Fintype I] [Fintype B]
    (l : I → A) (r : I ↪ A) (hdisj : ∀ i j, l i ≠ r j) :
    Nat.card {f : A → B // ∀ i, f (l i) = f (r i)} =
      Fintype.card B ^ (Fintype.card A - Fintype.card I) := by
  classical
  rw [Nat.card_congr (constraintEquiv l r hdisj)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_range]

/-- The number of Boolean codebooks realizing one prescribed increasing
matching in two different codewords. Only injectivity of target positions is
needed; increasing matchings in particular satisfy it. -/
theorem card_prescribed_matching {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    Nat.card {c : Fin K × Fin P → Bool //
      ∀ t, c (i, u t) = c (j, v t)} = 2 ^ (K * P - s) := by
  let r : Fin s ↪ Fin K × Fin P :=
    ⟨fun t => (j, v t), fun _ _ h => hv (congrArg Prod.snd h)⟩
  have hd : ∀ t t', (i, u t) ≠ r t' := by
    intro t t' h
    exact hne (congrArg Prod.fst h)
  have h := card_constraints (B := Bool) (fun t => (i, u t)) r hd
  change Nat.card {c : Fin K × Fin P → Bool //
    ∀ t, c (i, u t) = c (j, v t)} =
      Fintype.card Bool ^ (Fintype.card (Fin K × Fin P) - Fintype.card (Fin s)) at h
  simpa only [Fintype.card_bool, Fintype.card_prod, Fintype.card_fin] using h

/-- Curried codebooks have the same exact count. -/
theorem card_prescribed_matching_curried {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    Nat.card {c : Fin K → Fin P → Bool //
      ∀ t, c i (u t) = c j (v t)} = 2 ^ (K * P - s) := by
  let e : {c : Fin K → Fin P → Bool // ∀ t, c i (u t) = c j (v t)} ≃
      {c : Fin K × Fin P → Bool // ∀ t, c (i, u t) = c (j, v t)} :=
    { toFun := fun c => ⟨fun p => c.1 p.1 p.2, c.2⟩
      invFun := fun c => ⟨fun a b => c.1 (a, b), c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_prescribed_matching i j hne u v hv)

/-- Denominator-free form of the probability `2^(-s)`. -/
theorem card_prescribed_matching_mul {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    Nat.card {c : Fin K → Fin P → Bool //
      ∀ t, c i (u t) = c j (v t)} * 2 ^ s = 2 ^ (K * P) := by
  have hs : s ≤ P := by simpa using Fintype.card_le_of_injective v hv
  have hK : 1 ≤ K := by have := i.isLt; omega
  have hsKP : s ≤ K * P := by nlinarith
  rw [card_prescribed_matching_curried i j hne u v hv, ← pow_add,
    Nat.sub_add_cancel hsKP]

/-- The fraction of all independent uniform Boolean assignments satisfying a
fixed prescribed matching equals `1 / 2^s`. -/
theorem prescribed_matching_fraction {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    (Nat.card {c : Fin K → Fin P → Bool //
      ∀ t, c i (u t) = c j (v t)} : ℝ) / (2 : ℝ) ^ (K * P) =
      1 / (2 : ℝ) ^ s := by
  apply (div_eq_div_iff (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))).2
  simp only [one_mul]
  exact_mod_cast card_prescribed_matching_mul i j hne u v hv

/-- Finset form, suitable for a finite union bound over forbidden matchings. -/
theorem filter_card_prescribed_matching {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    (Finset.univ.filter (fun c : Fin K → Fin P → Bool =>
      ∀ t, c i (u t) = c j (v t))).card = 2 ^ (K * P - s) := by
  classical
  rw [← Fintype.card_subtype]
  simpa only [Nat.card_eq_fintype_card] using
    card_prescribed_matching_curried i j hne u v hv

end TreeEdit.BinaryLower.RandomMatching

end OAI
