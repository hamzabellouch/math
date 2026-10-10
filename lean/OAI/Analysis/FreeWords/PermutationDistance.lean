import Mathlib

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

def permutationLinear {ι : Type*} (π : Equiv.Perm ι) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun f := f ∘ π
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def permutationDistance {r : ℕ} (π σ : Equiv.Perm (Fin r)) : ℕ :=
  Module.finrank ℂ (LinearMap.range (permutationLinear π-permutationLinear σ))

def matchingSetoid {ι : Type*} (π σ : Equiv.Perm ι) : Setoid ι :=
  Relation.EqvGen.setoid (fun i j => ∃ k, i=π k ∧ j=σ k)

instance matchingQuotientFintype {ι : Type*} [Fintype ι] (π σ : Equiv.Perm ι) :
    Fintype (Quotient (matchingSetoid π σ)) := Fintype.ofFinite _

theorem matching_respects {ι β : Type*} {π σ : Equiv.Perm ι} (f : ι → β)
    (hf : f ∘ π=f ∘ σ) {i j : ι} (h : matchingSetoid π σ i j) : f i=f j := by
  induction h with
  | rel a b hab =>
    obtain ⟨k,rfl,rfl⟩ := hab
    exact congrFun hf k
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def matchingEquiv {ι β : Type*} (π σ : Equiv.Perm ι) :
    {f : ι → β // f ∘ π=f ∘ σ} ≃ (Quotient (matchingSetoid π σ) → β) where
  toFun f := Quotient.lift f.val (fun _ _ h => matching_respects f.val f.property h)
  invFun F := ⟨fun i => F (Quotient.mk _ i),by
    funext i
    exact congrArg F (Quotient.sound (.rel _ _ ⟨i,rfl,rfl⟩))⟩
  left_inv _ := rfl
  right_inv F := by funext q; exact Quotient.inductionOn q (fun _ => rfl)

def matchingLinearEquiv {ι : Type*} (π σ : Equiv.Perm ι) :
    LinearMap.ker (permutationLinear π-permutationLinear σ) ≃ₗ[ℂ]
      (Quotient (matchingSetoid π σ) → ℂ) where
  toFun f := (matchingEquiv π σ) ⟨f.val, sub_eq_zero.mp f.property⟩
  invFun F := ⟨(matchingEquiv π σ).symm F,sub_eq_zero.mpr ((matchingEquiv π σ).symm F).property⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv F := (matchingEquiv π σ).apply_symm_apply F
  map_add' f g := by funext q; exact Quotient.inductionOn q (fun _ => rfl)
  map_smul' z f := by funext q; exact Quotient.inductionOn q (fun _ => rfl)

theorem permutationDistance_add_classes {r : ℕ} (π σ : Equiv.Perm (Fin r)) :
    permutationDistance π σ+Fintype.card (Quotient (matchingSetoid π σ))=r := by
  have h := LinearMap.finrank_range_add_finrank_ker (permutationLinear π-permutationLinear σ)
  rw [(matchingLinearEquiv π σ).finrank_eq,Module.finrank_pi,Module.finrank_pi,Fintype.card_fin] at h
  exact h

theorem permutationDistance_self {r : ℕ} (π : Equiv.Perm (Fin r)) :
    permutationDistance π π=0 := by simp [permutationDistance]

theorem permutationDistance_eq_zero {r : ℕ} (π σ : Equiv.Perm (Fin r)) :
    permutationDistance π σ=0 ↔ π=σ := by
  classical
  constructor
  · intro h
    have he := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)
    have hl : permutationLinear π=permutationLinear σ := sub_eq_zero.mp he
    apply Equiv.ext
    intro i
    by_contra hn
    have hv := congrArg (fun L : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) =>
      L (fun j => if j=π i then 1 else 0) i) hl
    simp [permutationLinear,Ne.symm hn] at hv
  · rintro rfl; exact permutationDistance_self π

theorem permutationDistance_symm {r : ℕ} (π σ : Equiv.Perm (Fin r)) :
    permutationDistance π σ=permutationDistance σ π := by
  unfold permutationDistance
  rw [← neg_sub (permutationLinear σ) (permutationLinear π),LinearMap.range_neg]

theorem permutationDistance_triangle {r : ℕ} (π σ ρ : Equiv.Perm (Fin r)) :
    permutationDistance π ρ ≤ permutationDistance π σ+permutationDistance σ ρ := by
  unfold permutationDistance
  have he : permutationLinear π-permutationLinear ρ=
      (permutationLinear π-permutationLinear σ)+(permutationLinear σ-permutationLinear ρ) := by abel
  rw [he]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

end

end KKWeingarten
end

end OAI
