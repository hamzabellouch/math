import Mathlib

namespace OAI

/-!
# Counting colorings subject to vertex constraints
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

variable {X I C : Type*}

noncomputable def coloringEquiv (f : I → X) (hf : Function.Injective f) :
    (X → C) ≃ (I → C) × ({x : X // x ∉ Set.range f} → C) := by
  classical
  refine
    { toFun := fun c => (c ∘ f, fun x => c x.val)
      invFun := fun ab x => if h : x ∈ Set.range f then ab.1 h.choose else ab.2 ⟨x, h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    funext x
    dsimp
    split_ifs with h
    · exact congrArg c h.choose_spec
    · rfl
  · rintro ⟨a, b⟩
    ext i
    · simp only [Function.comp_apply, dite_eq_left (Set.mem_range_self i)]
      exact congrArg a (hf (Set.mem_range_self i).choose_spec)
    · simp only [dite_eq_right i.property]

@[simp] theorem coloringEquiv_fst (f : I → X) (hf : Function.Injective f)
    (c : X → C) (i : I) : (coloringEquiv f hf c).1 i = c (f i) := rfl

noncomputable def goodColoringEquiv (f : I → X) (hf : Function.Injective f)
    (P : I → C → Prop) :
    {c : X → C // ∀ i, P i (c (f i))} ≃
      {a : I → C // ∀ i, P i (a i)} × ({x : X // x ∉ Set.range f} → C) where
  toFun c := (⟨(coloringEquiv f hf c.val).1, c.property⟩,
    (coloringEquiv f hf c.val).2)
  invFun ab := ⟨(coloringEquiv f hf).symm (ab.1.val, ab.2), by
    intro i
    have h := congrArg (fun z : (I → C) × ({x : X // x ∉ Set.range f} → C) => z.1 i)
      ((coloringEquiv f hf).apply_symm_apply (ab.1.val, ab.2))
    change (coloringEquiv f hf).symm (ab.1.val, ab.2) (f i) = ab.1.val i at h
    rw [h]
    exact ab.1.property i⟩
  left_inv c := by
    apply Subtype.ext
    exact (coloringEquiv f hf).symm_apply_apply c.val
  right_inv ab := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((coloringEquiv f hf).apply_symm_apply (ab.1.val, ab.2))
    · change ((coloringEquiv f hf) ((coloringEquiv f hf).symm (ab.1.val, ab.2))).2 = ab.2
      exact congrArg Prod.snd ((coloringEquiv f hf).apply_symm_apply (ab.1.val, ab.2))

theorem cardinal_identity [Fintype X] [Fintype I] [Fintype C]
    (f : I → X) (hf : Function.Injective f) (P : I → Finset C) :
    Fintype.card {c : X → C // ∀ i, c (f i) ∈ P i} *
        Fintype.card C ^ Fintype.card I =
      (∏ i, (P i).card) * Fintype.card (X → C) := by
  classical
  have hg := Fintype.card_congr (goodColoringEquiv f hf (fun i c => c ∈ P i))
  have hp := Fintype.card_congr
    (Equiv.subtypePiEquivPi (p := fun i c => c ∈ P i))
  simp only [Fintype.card_pi, Fintype.card_coe] at hp
  simp only [Fintype.card_prod, hp, Fintype.card_fun] at hg
  have ht := Fintype.card_congr (coloringEquiv (C := C) f hf)
  simp only [Fintype.card_prod, Fintype.card_fun] at ht
  rw [hg, Fintype.card_fun, ht]
  ring

theorem cardinal_bound [Fintype X] [Fintype I] [Fintype C]
    (f : I → X) (hf : Function.Injective f) (P : I → Finset C)
    (H : ℕ) (hH : ∀ i, (P i).card ≤ H) :
    Fintype.card {c : X → C // ∀ i, c (f i) ∈ P i} *
        Fintype.card C ^ Fintype.card I ≤
      H ^ Fintype.card I * Fintype.card (X → C) := by
  classical
  rw [cardinal_identity f hf P]
  apply Nat.mul_le_mul_right
  simpa using Finset.prod_le_prod
    (fun index (_ : index ∈ (Finset.univ : Finset I)) => hH index)

end DiscreteFree.ColorCounting

noncomputable section
namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

theorem union_bound {X P : Type*} [Fintype X] [Fintype P] (r : P → X → Prop) :
    Fintype.card {x : X // ∃ p, r p x} ≤ ∑ p, Fintype.card {x : X // r p x} := by
  let f : (Σ p : P, {x : X // r p x}) → {x : X // ∃ p, r p x} :=
    fun z => ⟨z.2.val, z.1, z.2.property⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, p, hp⟩
    exact ⟨⟨p, x, hp⟩, rfl⟩
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_surjective f hf

theorem weighted_union_bound {X P : Type*} [Fintype X] [Fintype P]
    (r : P → X → Prop) (a b : ℕ)
    (h : ∀ p, Fintype.card {x : X // r p x} * a ≤ b) :
    Fintype.card {x : X // ∃ p, r p x} * a ≤ Fintype.card P * b := by
  calc
    _ ≤ (∑ p, Fintype.card {x : X // r p x}) * a :=
      Nat.mul_le_mul_right _ (union_bound r)
    _ = ∑ p, Fintype.card {x : X // r p x} * a := Finset.sum_mul _ _ _
    _ ≤ ∑ _p : P, b := Finset.sum_le_sum (fun p _ => h p)
    _ = _ := by simp

theorem many_walks_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : W → I → X) (hf : ∀ w, Function.Injective (f w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {c : X → C // ∃ w s, ∀ i, c (f w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card (X → C) := by
  have h := weighted_union_bound
    (fun ws : W × S => fun c : X → C => ∀ i, c (f ws.1 i) ∈ P ws.2 i)
    (Fintype.card C ^ Fintype.card I) (H ^ Fintype.card I * Fintype.card (X → C))
    (fun ws => by
      convert cardinal_bound (f ws.1) (hf ws.1) (P ws.2) H (hH ws.2) using 1
      simp only [← Nat.card_eq_fintype_card])
  simp only [Prod.exists, Fintype.card_prod] at h
  exact h.trans_eq (by ring)

theorem colored_roots_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : X → W → I → X) (hf : ∀ x w, Function.Injective (f x w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card ((X → C) × X) := by
  let e : {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} ≃
      Σ x : X, {c : X → C // ∃ w s, ∀ i, c (f x w i) ∈ P s i} :=
    { toFun := fun z => ⟨z.val.2, z.val.1, z.property⟩
      invFun := fun z => ⟨(z.2.val, z.1), z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma, Finset.sum_mul]
  calc
    _ ≤ ∑ _x : X, Fintype.card W * Fintype.card S * H ^ Fintype.card I *
        Fintype.card (X → C) :=
      Finset.sum_le_sum (fun x _ => many_walks_bound (f x) (hf x) P H hH)
    _ = _ := by simp; ring

end DiscreteFree.ColorCounting
end

end

end OAI
