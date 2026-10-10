import Mathlib

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G H V W : Type*} [Group G] [Group H]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  (φ : H →* G) (ρ : Representation ℂ G V) (σ : Representation ℂ H W)

def toCoind (f : IntertwiningMap (ρ.comp φ) σ) : IntertwiningMap ρ (coind φ σ) where
  toLinearMap := {
    toFun := fun v => ⟨fun g => f (ρ g v), by
      intro h g
      change f (ρ (φ h * g) v) = σ h (f (ρ g v))
      rw [map_mul,Module.End.mul_apply]
      exact IntertwiningMap.isIntertwining _ _ f h (ρ g v)⟩
    map_add' := by intro a b; ext g; simp only [map_add]; rfl
    map_smul' := by intro c a; ext g; simp only [map_smul]; rfl }
  isIntertwining' a := by
    ext v g
    change f (ρ g (ρ a v)) = f (ρ (g*a) v)
    rw [map_mul,Module.End.mul_apply]

def fromCoind (f : IntertwiningMap ρ (coind φ σ)) : IntertwiningMap (ρ.comp φ) σ where
  toLinearMap := {
    toFun := fun v => (f v).val 1
    map_add' := by intros; simp only [map_add]; rfl
    map_smul' := by intros; simp only [map_smul]; rfl }
  isIntertwining' h := by
    ext v
    have he := congrArg (fun u : coindV φ σ => u.val 1)
      (IntertwiningMap.isIntertwining _ _ f (φ h) v)
    change (f (ρ (φ h) v)).val 1 = σ h ((f v).val 1)
    rw [he]
    change (f v).val (1*φ h) = _
    simpa only [one_mul,mul_one] using (f v).property h 1

def coindHomEquiv : IntertwiningMap (ρ.comp φ) σ ≃ₗ[ℂ] IntertwiningMap ρ (coind φ σ) where
  toFun := toCoind φ ρ σ
  invFun := fromCoind φ ρ σ
  left_inv f := by ext v; change f (ρ 1 v) = f v; simp
  right_inv f := by
    ext v g
    change (f (ρ g v)).val 1 = (f v).val g
    rw [IntertwiningMap.isIntertwining]
    change (f v).val (1*g) = _
    rw [one_mul]
  map_add' a b := by ext v g; rfl
  map_smul' c a := by ext v g; rfl

variable [Fintype G] [Fintype H] [Module.Finite ℂ V] [Module.Finite ℂ W]

lemma multiplicity_symm (σ : Representation ℂ G W) :
    Module.finrank ℂ (IntertwiningMap ρ σ) = Module.finrank ℂ (IntertwiningMap σ ρ) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h₁ := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h₂ := card_inv_mul_sum_char_mul_char_eq_finrank σ ρ
  have he : ∑ g : G, σ.character g * ρ.character g⁻¹ =
      ∑ g : G, ρ.character g * σ.character g⁻¹ := by
    rw [← Equiv.sum_comp (Equiv.inv G) (fun g => ρ.character g * σ.character g⁻¹)]
    simp only [Equiv.inv_apply,inv_inv,mul_comm]
  apply Nat.cast_injective (R := ℂ)
  exact h₁.symm.trans ((congrArg (fun z : ℂ => (Nat.card G : ℂ)⁻¹*z) he).trans h₂)

def coindEvaluation {I : Type*} (r : I → G) : coindV φ σ →ₗ[ℂ] (I → W) where
  toFun := fun f i => f.val (r i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [Fintype G] [Fintype H] [Module.Finite ℂ W] in
lemma coindEvaluation_injective {I : Type*} (r : I → G)
    (hr : ∀ g : G, ∃ h : H, ∃ i : I, g = φ h * r i) :
    Function.Injective (coindEvaluation φ σ r) := by
  intro f a he
  apply Subtype.ext
  funext g
  obtain ⟨h,i,rfl⟩ := hr g
  rw [f.property,a.property]
  exact congrArg (σ h) (congrFun he i)

omit [Fintype G] [Fintype H] in
lemma coind_finrank_le {I : Type*} [Fintype I] (r : I → G)
    (hr : ∀ g : G, ∃ h : H, ∃ i : I, g = φ h * r i) :
    Module.finrank ℂ (coindV φ σ) ≤ Fintype.card I * Module.finrank ℂ W := by
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul] using
    (LinearMap.finrank_le_finrank_of_injective (coindEvaluation_injective φ σ r hr))

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation Equiv Equiv.Perm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

def blockPerm : Equiv.Perm A →* Equiv.Perm X :=
  e.permCongrHom.toMonoidHom.comp ((sumCongrHom A B).comp (MonoidHom.inl _ _))

omit [Fintype A] [Fintype B] [Fintype X] in
lemma blockPerm_inr (a : Equiv.Perm A) (b : B) :
    blockPerm e a (e (Sum.inr b)) = e (Sum.inr b) := by
  change e (Equiv.sumCongr a (1:Equiv.Perm B) (e.symm (e (Sum.inr b)))) = _
  rw [e.symm_apply_apply]
  rfl

omit [Fintype X] in
lemma blockPerm_of_fixed (g : Equiv.Perm X) (hg : ∀ b, g (e (Sum.inr b)) = e (Sum.inr b)) :
    ∃ a : Equiv.Perm A, blockPerm e a = g := by
  let d := e.symm.permCongr g
  have hd (b : B) : d (Sum.inr b) = Sum.inr b := by
    change e.symm (g (e (Sum.inr b))) = _
    rw [hg,e.symm_apply_apply]
  have hh : d ∈ (sumCongrHom A B).range := by
    apply mem_sumCongrHom_range_of_perm_mapsTo_inl
    apply (perm_mapsTo_inl_iff_mapsTo_inr d).mpr
    rintro y ⟨b,rfl⟩
    exact ⟨b,(hd b).symm⟩
  obtain ⟨⟨a,b⟩,hab⟩ := hh
  have hb : b = 1 := by
    ext x
    have hx := Equiv.congr_fun hab (Sum.inr x)
    rw [hd] at hx
    exact Sum.inr_injective hx
  subst b
  refine ⟨a,?_⟩
  change e.permCongr ((sumCongrHom A B) (a,1)) = g
  have he := congrArg e.permCongr hab
  simpa only [d,← Equiv.permCongr_symm,Equiv.apply_symm_apply] using he

def basePlacement : B ↪ X := ⟨fun b => e (Sum.inr b), e.injective.comp Sum.inr_injective⟩

omit [Fintype A] [Fintype X] in
lemma placement_extension (x : B ↪ X) : ∃ g : Equiv.Perm X, ∀ b, g (basePlacement e b) = x b :=
  Equiv.Perm.exists_extending_pair (basePlacement e) x (basePlacement e).injective x.injective

def placementSection (x : B ↪ X) : Equiv.Perm X := (placement_extension e x).choose

omit [Fintype A] [Fintype X] in
lemma placementSection_apply (x : B ↪ X) (b : B) :
    placementSection e x (basePlacement e b) = x b := (placement_extension e x).choose_spec b

omit [Fintype X] in
lemma placementSection_covers (g : Equiv.Perm X) :
    ∃ a : Equiv.Perm A, ∃ x : B ↪ X, g = blockPerm e a * (placementSection e x)⁻¹ := by
  let x : B ↪ X := (basePlacement e).trans g.symm.toEmbedding
  have hx : ∀ b, (g*placementSection e x) (e (Sum.inr b)) = e (Sum.inr b) := by
    intro b
    change g (placementSection e x (basePlacement e b)) = _
    rw [placementSection_apply]
    exact g.apply_symm_apply _
  obtain ⟨a,ha⟩ := blockPerm_of_fixed e (g*placementSection e x) hx
  exact ⟨a,x,by rw [ha,mul_inv_cancel_right]⟩

variable {W : Type*} [AddCommMonoid W] [Module ℂ W] [Module.Finite ℂ W]
  (σ : Representation ℂ (Equiv.Perm A) W)

theorem placement_coind_finrank :
    Module.finrank ℂ (coindV (blockPerm e) σ) ≤
      Fintype.card (B ↪ X) * Module.finrank ℂ W :=
  coind_finrank_le (blockPerm e) σ (fun x => (placementSection e x)⁻¹)
    (placementSection_covers e)

theorem placement_coind_finrank_pow :
    Module.finrank ℂ (coindV (blockPerm e) σ) ≤
      (Fintype.card X)^(Fintype.card B) * Module.finrank ℂ W := by
  apply (placement_coind_finrank e σ).trans
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_fun] using
    Fintype.card_le_of_injective (fun x : B ↪ X => (x : B → X)) DFunLike.coe_injective

end BinaryCoordinateSweeps.Irrep

end

end OAI
