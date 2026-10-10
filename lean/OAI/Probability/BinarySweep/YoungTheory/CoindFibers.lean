import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.CoinductionTools

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep

section
open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [AddCommMonoid W] [Module ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

def cosetEquiv : H × I ≃ G := Equiv.ofBijective _ hc

lemma cosetEquiv_symm_mul (h : H) (g : G) :
    (cosetEquiv φ r hc).symm (φ h * g) =
      (h * ((cosetEquiv φ r hc).symm g).1, ((cosetEquiv φ r hc).symm g).2) := by
  apply (cosetEquiv φ r hc).injective
  rw [Equiv.apply_symm_apply]
  change φ h * g = φ (h * _) * r _
  rw [map_mul,mul_assoc]
  exact congrArg (fun a => φ h*a) ((cosetEquiv φ r hc).apply_symm_apply g).symm

lemma cosetEquiv_symm_rep (i : I) : (cosetEquiv φ r hc).symm (r i) = (1,i) := by
  apply (cosetEquiv φ r hc).injective
  simp only [Equiv.apply_symm_apply, cosetEquiv, Equiv.ofBijective_apply]
  simp

def coindFiberInverse (v : I → W) : coindV φ σ :=
  ⟨fun g => σ ((cosetEquiv φ r hc).symm g).1 (v ((cosetEquiv φ r hc).symm g).2), by
    intro h g
    dsimp only
    rw [cosetEquiv_symm_mul]
    simp only [map_mul,Module.End.mul_apply]⟩

def coindFiberEquiv : coindV φ σ ≃ₗ[ℂ] (I → W) where
  toFun := coindEvaluation φ σ r
  invFun := coindFiberInverse φ σ r hc
  left_inv f := by
    ext g
    change σ _ (f.val (r _)) = f.val g
    rw [← f.property]
    exact congrArg f.val ((cosetEquiv φ r hc).apply_symm_apply g)
  right_inv v := by
    funext i
    change σ _ (v _) = v i
    rw [cosetEquiv_symm_rep]
    simp
  map_add' := (coindEvaluation φ σ r).map_add
  map_smul' := (coindEvaluation φ σ r).map_smul

lemma coindFiberEquiv_action (a : G) (f : coindV φ σ) (i : I) :
    coindFiberEquiv φ σ r hc (coind φ σ a f) i =
      σ ((cosetEquiv φ r hc).symm (r i*a)).1
        (coindFiberEquiv φ σ r hc f ((cosetEquiv φ r hc).symm (r i*a)).2) := by
  change f.val (r i*a) = σ _ (f.val (r _))
  rw [← f.property]
  exact congrArg f.val ((cosetEquiv φ r hc).apply_symm_apply (r i*a)).symm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

omit [Fintype X] in
lemma placement_cosets_bijective : Function.Bijective
    (fun u : Equiv.Perm A × (B ↪ X) => blockPerm e u.1 * (placementSection e u.2)⁻¹) := by
  constructor
  · rintro ⟨a,x⟩ ⟨b,y⟩ h
    have hxy : x = y := by
      ext k
      have he := Equiv.congr_fun (congrArg (fun g : Equiv.Perm X => g⁻¹) h)
        (basePlacement e k)
      simp only [mul_inv_rev,inv_inv,Equiv.Perm.mul_apply] at he
      have ha : (blockPerm e a)⁻¹ (basePlacement e k) = basePlacement e k := by
        rw [← map_inv]; exact blockPerm_inr e a⁻¹ k
      have hb : (blockPerm e b)⁻¹ (basePlacement e k) = basePlacement e k := by
        rw [← map_inv]; exact blockPerm_inr e b⁻¹ k
      simpa only [ha,hb,placementSection_apply] using he
    subst y
    have hab : blockPerm e a = blockPerm e b := mul_right_cancel h
    have hh : a = b := by
      ext k
      have hk := Equiv.congr_fun hab (e (Sum.inl k))
      change e (Equiv.sumCongr a 1 (e.symm (e (Sum.inl k)))) =
        e (Equiv.sumCongr b 1 (e.symm (e (Sum.inl k)))) at hk
      simpa only [e.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.inl.injEq] using e.injective hk
    simp only [hh]
  · intro g
    obtain ⟨a,x,h⟩ := placementSection_covers e g
    exact ⟨(a,x),h.symm⟩

end

open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [Fintype I] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

omit [Fintype I] in
lemma cosetIndex_mul (a b : G) (i : I) :
    ((cosetEquiv φ r hc).symm (r i*(a*b))).2 =
      ((cosetEquiv φ r hc).symm
        (r ((cosetEquiv φ r hc).symm (r i*a)).2 * b)).2 := by
  have he := (cosetEquiv φ r hc).apply_symm_apply (r i*a)
  change φ _ * r _ = r i*a at he
  conv_lhs => rw [← mul_assoc,← he,mul_assoc,cosetEquiv_symm_mul]

def cosetIndexAction (a : G) : I ≃ I where
  toFun i := ((cosetEquiv φ r hc).symm (r i*a)).2
  invFun i := ((cosetEquiv φ r hc).symm (r i*a⁻¹)).2
  left_inv i := by dsimp only; rw [← cosetIndex_mul,mul_inv_cancel,mul_one,cosetEquiv_symm_rep]
  right_inv i := by dsimp only; rw [← cosetIndex_mul,inv_mul_cancel,mul_one,cosetEquiv_symm_rep]

abbrev CoindHilbertSpace := PiLp 2 (fun _ : I => W)

def coindHilbertEquiv : coindV φ σ ≃ₗ[ℂ] CoindHilbertSpace (I := I) (W := W) :=
  (coindFiberEquiv φ σ r hc).trans (WithLp.linearEquiv 2 ℂ (I → W)).symm

def coindHilbertRep : Representation ℂ G (CoindHilbertSpace (I := I) (W := W)) where
  toFun g := (coindHilbertEquiv φ σ r hc).conj (coind φ σ g)
  map_one' := by rw [map_one]; exact (coindHilbertEquiv φ σ r hc).conjRingEquiv.map_one
  map_mul' a b := by rw [map_mul]; exact (coindHilbertEquiv φ σ r hc).conjRingEquiv.map_mul _ _

omit [Fintype I] in
lemma coindHilbertEquiv_apply (f : coindV φ σ) (i : I) :
    coindHilbertEquiv φ σ r hc f i = f.val (r i) := rfl

omit [Fintype I] in
lemma coindHilbertRep_apply (a : G) (v : CoindHilbertSpace (I := I) (W := W)) (i : I) :
    coindHilbertRep φ σ r hc a v i =
      σ ((cosetEquiv φ r hc).symm (r i*a)).1
        (v (cosetIndexAction φ r hc a i)) := by
  obtain ⟨f,rfl⟩ := (coindHilbertEquiv φ σ r hc).surjective v
  change coindHilbertEquiv φ σ r hc
    (coind φ σ a ((coindHilbertEquiv φ σ r hc).symm
      (coindHilbertEquiv φ σ r hc f))) i = _
  rw [LinearEquiv.symm_apply_apply]
  exact coindFiberEquiv_action φ σ r hc a f i

lemma coindHilbert_unitary (hu : ∀ h v w, inner ℂ (σ h v) (σ h w) = inner ℂ v w)
    (a : G) (v w : CoindHilbertSpace (I := I) (W := W)) :
    inner ℂ (coindHilbertRep φ σ r hc a v) (coindHilbertRep φ σ r hc a w) = inner ℂ v w := by
  simp only [PiLp.inner_apply,coindHilbertRep_apply,hu]
  exact Equiv.sum_comp (cosetIndexAction φ r hc a) (fun i => inner ℂ (v i) (w i))

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W V' W' : Type*} [Group G]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid V'] [Module ℂ V'] [AddCommMonoid W'] [Module ℂ W']
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}

def homCongr (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    IntertwiningMap ρ σ ≃ₗ[ℂ] IntertwiningMap ρ' σ' where
  toFun a := f.toIntertwiningMap.comp (a.comp e.symm.toIntertwiningMap)
  invFun a := f.symm.toIntertwiningMap.comp (a.comp e.toIntertwiningMap)
  left_inv a := by
    ext v
    change f.symm (f (a (e.symm (e v)))) = a v
    rw [Representation.Equiv.symm_apply_apply,Representation.Equiv.symm_apply_apply]
  right_inv a := by
    ext v
    change f (f.symm (a (e (e.symm v)))) = a v
    rw [Representation.Equiv.apply_symm_apply,Representation.Equiv.apply_symm_apply]
  map_add' a b := by
    ext v
    change f (a (e.symm v) + b (e.symm v)) = _
    rw [map_add]
    rfl
  map_smul' c a := by
    ext v
    change f (c • a (e.symm v)) = _
    rw [map_smul]
    rfl

lemma multiplicity_congr (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    Module.finrank ℂ (IntertwiningMap ρ σ) = Module.finrank ℂ (IntertwiningMap ρ' σ') :=
  (homCongr e f).finrank_eq

def repEquiv_comp {H : Type*} [Group H] (e : ρ.Equiv ρ') (φ : H →* G) :
    Representation.Equiv (ρ.comp φ) (ρ'.comp φ) :=
  .mk e.toLinearEquiv (fun h => e.isIntertwining' (φ h))

end BinaryCoordinateSweeps.Irrep

end

end OAI
