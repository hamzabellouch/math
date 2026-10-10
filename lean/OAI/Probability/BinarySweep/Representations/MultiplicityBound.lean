import Mathlib

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma intertwiner_retraction (f : IntertwiningMap ρ σ) (hf : Function.Injective f) :
    ∃ r : IntertwiningMap σ ρ, ∀ v, r (f v) = v := by
  let fm := IntertwiningMap.equivLinearMapAsModule ρ σ f
  have hm : LinearMap.ker fm = ⊥ := LinearMap.ker_eq_bot.mpr hf
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨r,hr⟩ := MonoidAlgebra.exists_leftInverse_of_injective fm hm
  refine ⟨(IntertwiningMap.equivLinearMapAsModule σ ρ).symm r, fun v => ?_⟩
  exact DFunLike.congr_fun hr v

theorem multiplicity_le_commutant [ρ.IsIrreducible] :
    Module.finrank ℂ (IntertwiningMap ρ σ) ≤ Module.finrank ℂ (IntertwiningMap σ σ) := by
  by_cases h : ∃ f : IntertwiningMap ρ σ, f ≠ 0
  · obtain ⟨f,hf⟩ := h
    have hfi : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
    obtain ⟨r,hr⟩ := intertwiner_retraction ρ σ f hfi
    let T : IntertwiningMap ρ σ →ₗ[ℂ] IntertwiningMap σ σ :=
      (IntertwiningMap.llcomp σ ρ σ).flip r
    have hT : Function.Injective T := by
      intro a b hab
      ext v
      have hh := congrArg (fun t : IntertwiningMap σ σ => t (f v)) hab
      change a (r (f v)) = b (r (f v)) at hh
      change a v = b v
      simpa only [hr] using hh
    exact LinearMap.finrank_le_finrank_of_injective hT
  · have hs : Subsingleton (IntertwiningMap ρ σ) := ⟨by
      intro a b
      have ha : a=0 := by_contra (fun ha => h ⟨a,ha⟩)
      have hb : b=0 := by_contra (fun hb => h ⟨b,hb⟩)
      exact ha.trans hb.symm⟩
    rw [Module.finrank_eq_zero_of_subsingleton]
    exact Nat.zero_le _

def isotypicSpan : Submodule ℂ W :=
  ⨆ f : IntertwiningMap ρ σ, LinearMap.range f.toLinearMap

def evaluation : V ⊗[ℂ] IntertwiningMap ρ σ →ₗ[ℂ] W :=
  TensorProduct.lift {
    toFun := fun v => {
      toFun := fun f => f v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    map_add' := by intro u v; ext f; exact map_add f u v
    map_smul' := by intro c v; ext f; exact map_smul f c v }

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma evaluation_range : LinearMap.range (evaluation ρ σ) = isotypicSpan ρ σ := by
  apply le_antisymm
  · rintro _ ⟨t,rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul v f =>
      exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) f) ⟨v,rfl⟩
    | add t u ht hu => simpa only [map_add] using Submodule.add_mem _ ht hu
  · apply iSup_le
    intro f w hw
    obtain ⟨v,rfl⟩ := hw
    exact ⟨TensorProduct.tmul ℂ v f, rfl⟩

omit [Fintype G] in
lemma isotypicSpan_finrank : Module.finrank ℂ (isotypicSpan ρ σ) ≤
    Module.finrank ℂ V * Module.finrank ℂ (IntertwiningMap ρ σ) := by
  rw [← evaluation_range]
  simpa only [Module.finrank_tensorProduct] using LinearMap.finrank_range_le (evaluation ρ σ)

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma isotypicSpan_stable (g : G) (w : W) (hw : w ∈ isotypicSpan ρ σ) :
    σ g w ∈ isotypicSpan ρ σ := by
  apply Submodule.iSup_induction (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap)
    (motive := fun w => σ g w ∈ isotypicSpan ρ σ) hw
  · intro f x hx
    obtain ⟨v,rfl⟩ := hx
    change σ g (f v) ∈ isotypicSpan ρ σ
    rw [← IntertwiningMap.isIntertwining ρ σ f g v]
    exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) f)
      ⟨ρ g v,rfl⟩
  · simpa only [map_zero] using (isotypicSpan ρ σ).zero_mem
  · intro x y hx hy
    simpa only [map_add] using (isotypicSpan ρ σ).add_mem hx hy

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma isotypicSpan_map (g : G) : (isotypicSpan ρ σ).map (σ g) = isotypicSpan ρ σ := by
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact isotypicSpan_stable ρ σ g w hw
  · intro w hw
    refine ⟨σ g⁻¹ w, isotypicSpan_stable ρ σ g⁻¹ w hw, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

def schurScalar : IntertwiningMap ρ ρ ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofBijective (Algebra.linearMap ℂ (IntertwiningMap ρ ρ))
    IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm

omit [Fintype G] in
lemma schurScalar_smul (f : IntertwiningMap ρ ρ) (v : V) :
    schurScalar ρ f • v = f v := by
  have he := (schurScalar ρ).symm_apply_apply f
  exact congrArg (fun t : IntertwiningMap ρ ρ => t v) he

omit [Fintype G] in
lemma schurScalar_one : schurScalar ρ (1 : IntertwiningMap ρ ρ) = 1 := by
  apply (schurScalar ρ).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (1 : IntertwiningMap ρ ρ) = algebraMap ℂ (IntertwiningMap ρ ρ) 1
  exact (map_one _).symm

def intertwinerPairing : IntertwiningMap ρ σ →ₗ[ℂ]
    IntertwiningMap σ ρ →ₗ[ℂ] ℂ :=
  (LinearMap.compr₂ ((IntertwiningMap.llcomp ρ σ ρ).flip) (schurScalar ρ).toLinearMap)

omit [FiniteDimensional ℂ W] in
lemma intertwinerPairing_injective : Function.Injective (intertwinerPairing ρ σ) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  by_contra hn
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hn
  obtain ⟨r,hr⟩ := intertwiner_retraction ρ σ f hfi
  have hc : r.comp f = 1 := by ext v; exact hr v
  have hz : intertwinerPairing ρ σ f = 0 := hf
  have he := DFunLike.congr_fun hz r
  change schurScalar ρ (r.comp f) = 0 at he
  rw [hc,schurScalar_one] at he
  exact one_ne_zero he

lemma exists_intertwiner_dual (l : Module.Dual ℂ (IntertwiningMap ρ σ)) :
    ∃ r : IntertwiningMap σ ρ, ∀ f : IntertwiningMap ρ σ, ∀ v : V,
      r (f v) = l f • v := by
  have hs := (LinearMap.flip_surjective_iff₁ (B := intertwinerPairing ρ σ)).mpr
    (intertwinerPairing_injective ρ σ)
  obtain ⟨r,hr⟩ := hs l
  refine ⟨r,fun f v => ?_⟩
  have he := DFunLike.congr_fun hr f
  change schurScalar ρ (r.comp f) = l f at he
  rw [← he]
  exact (schurScalar_smul ρ (r.comp f) v).symm

theorem evaluation_injective : Function.Injective (evaluation ρ σ) := by
  let b := Module.finBasis ℂ (IntertwiningMap ρ σ)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro t ht
  change t = 0
  have ht0 : evaluation ρ σ t = 0 := ht
  apply e.injective
  apply Finsupp.ext
  intro i
  obtain ⟨r,hr⟩ := exists_intertwiner_dual ρ σ (b.coord i)
  have he : ∀ x : V ⊗[ℂ] IntertwiningMap ρ σ,
      r (evaluation ρ σ x) = e x i := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul v f =>
      change r (f v) = _
      rw [hr]
      exact (TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b v f i).symm
    | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  simpa only [ht0,map_zero,Finsupp.zero_apply] using (he t).symm

lemma isotypicSpan_finrank_eq : Module.finrank ℂ (isotypicSpan ρ σ) =
    Module.finrank ℂ V * Module.finrank ℂ (IntertwiningMap ρ σ) := by
  rw [← evaluation_range, LinearMap.finrank_range_of_inj (evaluation_injective ρ σ),
    Module.finrank_tensorProduct]

end BinaryCoordinateSweeps.Irrep

end

end OAI
