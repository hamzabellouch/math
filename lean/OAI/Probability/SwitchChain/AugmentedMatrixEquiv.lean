import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.AugmentedMatrix

variable {I W A : Type*} [sectionFintypeI : Fintype I] [sectionFintypeW : Fintype W]

def join (c : I → Fin 2) (B : I → W → Fin 2) : I → Option W → Fin 2 :=
  fun i j => match j with
    | none => c i
    | some w => B i w

include sectionFintypeI sectionFintypeW in
@[simp] theorem join_none (c : I → Fin 2) (B : I → W → Fin 2) (i : I) :
    join c B i none = c i := by
  have retainedsectionFintypeI := sectionFintypeI
  have retainedsectionFintypeW := sectionFintypeW
  exact rfl

include sectionFintypeI sectionFintypeW in
@[simp] theorem join_some (c : I → Fin 2) (B : I → W → Fin 2) (i : I) (w : W) :
    join c B i (some w) = B i w := by
  have retainedsectionFintypeI := sectionFintypeI
  have retainedsectionFintypeW := sectionFintypeW
  exact rfl

include sectionFintypeI in
theorem rowSum_join (c : I → Fin 2) (B : I → W → Fin 2) (i : I) :
    (∑ j : Option W, (join c B i j).val) = (c i).val + ∑ w, (B i w).val := by
  have retainedsectionFintypeI := sectionFintypeI
  simp [Fintype.sum_option]

def BlockCompatible (degree : A → I → Nat) (d : I → Nat) (columns : W → Nat)
    (a : A) (B : I → W → Fin 2) : Prop :=
  (∀ i, degree a i + ∑ w, (B i w).val = d i) ∧
    ∀ w, ∑ i, (B i w).val = columns w

def Compatible (offset d : I → Nat) (columns : W → Nat) (q : Nat)
    (M : I → Option W → Fin 2) : Prop :=
  (∀ i, offset i + ∑ j, (M i j).val = d i) ∧
    (∑ i, (M i none).val = q) ∧
    ∀ w, ∑ i, (M i (some w)).val = columns w

def augmentedMatrixEquiv (degree : A → I → Nat) (offset d : I → Nat)
    (columns : W → Nat) (q : Nat)
    (e : A ≃ {c : I → Fin 2 // ∑ i, (c i).val = q})
    (hdegree : ∀ a i, degree a i = offset i + ((e a).val i).val) :
    {p : A × (I → W → Fin 2) // BlockCompatible degree d columns p.1 p.2} ≃
      {M : I → Option W → Fin 2 // Compatible offset d columns q M} where
  toFun p := ⟨join (e p.val.1).val p.val.2, by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rw [rowSum_join]
      simpa only [hdegree, Nat.add_assoc] using p.property.1 i
    · simpa only [join_none] using (e p.val.1).property
    · intro w
      simpa only [join_some] using p.property.2 w⟩
  invFun M := ⟨(e.symm ⟨fun i => M.val i none, M.property.2.1⟩,
    fun i w => M.val i (some w)), by
      constructor
      · intro i
        rw [hdegree]
        simp only [Equiv.apply_symm_apply]
        have hi := M.property.1 i
        simpa only [Fintype.sum_option, Nat.add_assoc] using hi
      · exact M.property.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change e.symm _ = p.val.1
      apply e.injective
      simp only [Equiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    · rfl
  right_inv M := by
    apply Subtype.ext
    funext i j
    cases j with
    | none => simp only [join_none, Equiv.apply_symm_apply]
    | some w => rfl

theorem augmented_row_eq_iff_boundary_row_eq
    (degree : A → I → Nat) (offset d : I → Nat) (columns : W → Nat) (q : Nat)
    (e : A ≃ {c : I → Fin 2 // ∑ i, (c i).val = q})
    (hdegree : ∀ a i, degree a i = offset i + ((e a).val i).val)
    (a a' : A) (B B' : I → W → Fin 2)
    (h : BlockCompatible degree d columns a B)
    (h' : BlockCompatible degree d columns a' B') (i : I) :
    join (e a).val B i = join (e a').val B' i ↔ B i = B' i := by
  constructor
  · intro heq
    funext w
    exact congrFun heq (some w)
  · intro hrow
    have hsum : (∑ w, (B i w).val) = ∑ w, (B' i w).val := by rw [hrow]
    have hdeg : degree a i = degree a' i := by
      have ha := h.1 i
      have ha' := h'.1 i
      omega
    have hcol : (e a).val i = (e a').val i := by
      apply Fin.ext
      rw [hdegree, hdegree] at hdeg
      omega
    funext j
    cases j with
    | none => exact hcol
    | some w => exact congrFun hrow w

theorem compatible_iff_fixed_margins (offset d : I → Nat) (columns : W → Nat)
    (q : Nat) (hd : ∀ i, offset i ≤ d i) (M : I → Option W → Fin 2) :
    Compatible offset d columns q M ↔
      (∀ i, ∑ j, (M i j).val = d i - offset i) ∧
        (∑ i, (M i none).val = q) ∧
        ∀ w, ∑ i, (M i (some w)).val = columns w := by
  unfold Compatible
  constructor
  · rintro ⟨hrow, hcol⟩
    refine ⟨?_, hcol⟩
    intro i
    have h := hrow i
    omega
  · rintro ⟨hrow, hcol⟩
    refine ⟨?_, hcol⟩
    intro i
    have h := hrow i
    have hle := hd i
    omega

end Problem315.AugmentedMatrix

end

end OAI
