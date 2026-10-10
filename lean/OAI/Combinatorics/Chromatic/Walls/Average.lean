import Mathlib

namespace OAI

section
namespace ElementaryPositivity.SeparatedSymmetry
open MvPolynomial

variable {α β G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

noncomputable def average (ρ : G →* Equiv.Perm α) :
    MvPolynomial α ℚ →ₗ[ℚ] MvPolynomial α ℚ :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, (rename (ρ g)).toLinearMap

lemma average_apply (ρ : G →* Equiv.Perm α) (p : MvPolynomial α ℚ) :
    average ρ p = (Fintype.card G : ℚ)⁻¹ • ∑ g : G, rename (ρ g) p := by
  simp [average]

lemma rename_average (ρ : G →* Equiv.Perm α) (g : G) (p : MvPolynomial α ℚ) :
    rename (ρ g) (average ρ p) = average ρ p := by
  rw [average_apply, map_smul, map_sum]
  congr 1
  calc
    _ = ∑ h : G, rename (ρ (g*h)) p := by
      apply Finset.sum_congr rfl
      intro h _
      rw [rename_rename]
      congr 1
      ext a
      simp
    _ = _ := Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => rename (ρ h) p)

lemma average_fixed (ρ : G →* Equiv.Perm α) (p : MvPolynomial α ℚ)
    (hp : ∀ g, rename (ρ g) p = p) : average ρ p = p := by
  rw [average_apply]
  simp only [hp, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

def sumAction (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β) :
    G × H →* Equiv.Perm (α ⊕ β) where
  toFun g := Equiv.sumCongr (ρ g.1) (τ g.2)
  map_one' := by ext x; cases x <;> simp
  map_mul' := by intro g h; ext x; cases x <;> simp

omit [Fintype G] [Fintype H] in
lemma rename_sumAction_left (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (g : G) (h : H) (p : MvPolynomial α ℚ) :
    rename (sumAction ρ τ (g,h)) (rename Sum.inl p) = rename Sum.inl (rename (ρ g) p) := by
  simp only [rename_rename]
  rfl

omit [Fintype G] [Fintype H] in
lemma rename_sumAction_right (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (g : G) (h : H) (p : MvPolynomial β ℚ) :
    rename (sumAction ρ τ (g,h)) (rename Sum.inr p) = rename Sum.inr (rename (τ h) p) := by
  simp only [rename_rename]
  rfl

lemma average_separated (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ) :
    average (sumAction ρ τ) (rename Sum.inl f * rename Sum.inr g) =
      rename Sum.inl (average ρ f) * rename Sum.inr (average τ g) := by
  simp only [average_apply, map_mul, Fintype.sum_prod_type,
    rename_sumAction_left, rename_sumAction_right, map_smul, map_sum,
    Fintype.card_prod, Nat.cast_mul, mul_inv_rev, smul_mul_smul_comm,
    Finset.sum_mul, Finset.mul_sum]
  rw [mul_comm (Fintype.card H : ℚ)⁻¹ (Fintype.card G : ℚ)⁻¹]
  congr 1
  exact Finset.sum_comm

lemma separated_span (p : MvPolynomial (α ⊕ β) ℚ) :
    p ∈ Submodule.span ℚ {q | ∃ (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ),
      q = rename Sum.inl f * rename Sum.inr g} := by
  let V : Submodule ℚ (MvPolynomial (α ⊕ β) ℚ) := Submodule.span ℚ
    {q | ∃ (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ),
      q = rename Sum.inl f * rename Sum.inr g}
  change p ∈ V
  induction p using MvPolynomial.induction_on with
  | C r => exact Submodule.subset_span ⟨C r, 1, by simp⟩
  | add p q hp hq => exact V.add_mem hp hq
  | mul_X p x hp =>
    induction hp using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨f,g,rfl⟩ := hq
      cases x with
      | inl a =>
        apply Submodule.subset_span
        exact ⟨f * X a, g, by simp; ring⟩
      | inr b =>
        apply Submodule.subset_span
        exact ⟨f, g * X b, by simp [mul_assoc]⟩
    | zero => simp
    | add q r hq hr ihq ihr => simpa [add_mul] using V.add_mem ihq ihr
    | smul c q hq ih => simpa [smul_mul_assoc] using V.smul_mem c ih

theorem invariant_separated_span (ρ : G →* Equiv.Perm α) (τ : H →* Equiv.Perm β)
    (p : MvPolynomial (α ⊕ β) ℚ)
    (hp : ∀ x, rename (sumAction ρ τ x) p = p) :
    p ∈ Submodule.span ℚ {q | ∃ (f : MvPolynomial α ℚ) (g : MvPolynomial β ℚ),
      (∀ x, rename (ρ x) f = f) ∧ (∀ y, rename (τ y) g = g) ∧
      q = rename Sum.inl f * rename Sum.inr g} := by
  rw [← average_fixed (sumAction ρ τ) p hp]
  clear hp
  have h := separated_span p
  induction h using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨f,g,rfl⟩ := hq
    rw [average_separated]
    exact Submodule.subset_span ⟨average ρ f, average τ g,
      fun x => rename_average ρ x f, fun y => rename_average τ y g, rfl⟩
  | zero => simp
  | add q r hq hr ihq ihr => simpa using (Submodule.span ℚ _).add_mem ihq ihr
  | smul c q hq ih => simpa using (Submodule.span ℚ _).smul_mem c ih

end ElementaryPositivity.SeparatedSymmetry

end

end OAI
