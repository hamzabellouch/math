import OAI.Combinatorics.HadwigerCounterexample.BinaryMatrices
import Mathlib.LinearAlgebra.Projection

namespace OAI

/-! # Linear Extension -/

noncomputable section
namespace HadwigerCounterexample

open Matrix Module Submodule LinearMap Function

abbrev dim (V : Type) [AddCommGroup V] [Module F V] := finrank F V
abbrev rk {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) := dim (LinearMap.range f)

variable {V W U V' : Type}
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
variable [AddCommGroup U] [Module F U] [AddCommGroup V'] [Module F V']

theorem mem_range_comp {f : V →ₗ[F] W} {g : V →ₗ[F] U} (h : ker f ≤ ker g) :
    ∃ L : W →ₗ[F] U, L ∘ₗ f = g := by
  obtain ⟨i,hi⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨L,hL⟩ := (g ∘ₗ i).exists_extend
  refine ⟨L,LinearMap.ext fun x => ?_⟩
  have hm := LinearMap.congr_fun hL (f.rangeRestrict x)
  change L (f x) = g _ at hm
  change L (f x) = _
  rw [hm]
  have heq : f (i (f.rangeRestrict x)) = f x :=
    congrArg Subtype.val (LinearMap.congr_fun hi (f.rangeRestrict x))
  have ha : i (f.rangeRestrict x) - x ∈ ker f := by rw [mem_ker,map_sub,heq,sub_self]
  simpa only [mem_ker,map_sub,sub_eq_zero] using h ha

/-- Transport equal-sized domain embeddings in equal-dimensional spaces. -/
theorem equate {f : U →ₗ[F] V} {g : U →ₗ[F] V'} [FiniteDimensional F V]
    [FiniteDimensional F V'] (hf : Injective f) (hg : Injective g)
    (h : dim V = dim V') :
    ∃ A : V ≃ₗ[F] V', ∀ x, A (f x) = g x := by
  let p := LinearMap.range f
  let p' := LinearMap.range g
  let e := LinearEquiv.ofInjective f hf
  let e' := LinearEquiv.ofInjective g hg
  obtain ⟨q,hq⟩ := p.exists_isCompl
  obtain ⟨q',hq'⟩ := p'.exists_isCompl
  let B := Submodule.prodEquivOfIsCompl p q hq
  let B' := Submodule.prodEquivOfIsCompl p' q' hq'
  have hk : dim q = dim q' := by
    have h₁ := B.finrank_eq
    have h₂ := B'.finrank_eq
    rw [finrank_prod] at h₁ h₂
    have h₃ : dim p = dim p' := (e.symm.trans e').finrank_eq
    dsimp only [dim] at *
    omega
  let C : q ≃ₗ[F] q' := LinearEquiv.ofFinrankEq _ _ hk
  refine ⟨B.symm.trans ((LinearEquiv.prodCongr (e.symm.trans e') C).trans B'), fun x => ?_⟩
  have hb : B.symm (f x) = (e x,0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left p q hq (e x)
  change B' ((e.symm.trans e') (B.symm (f x)).1, C (B.symm (f x)).2) = _
  rw [hb]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,map_zero]
  change (e' x).val + (0:q').val = g x
  simp only [Submodule.coe_zero,add_zero]
  rfl

/-- Split projection into kernel plus section. -/
theorem lin_split (f : V →ₗ[F] W) (h : Surjective f) :
    ∃ (B : W →ₗ[F] V) (k : V →ₗ[F] ker f), (∀ x, f (B x) = x) ∧
      ∀ x, B (f x) + (k x).val = x := by
  obtain ⟨B,hB⟩ := f.exists_rightInverse_of_surjective (range_eq_top.mpr h)
  have hb x : f (B x) = x := LinearMap.congr_fun hB x
  let K := LinearMap.id - B ∘ₗ f
  have hk x : K x ∈ ker f := by
    change f (x - B (f x)) = 0
    rw [map_sub,hb,sub_self]
  exact ⟨B,K.codRestrict _ hk,hb,fun x => by change B _ + (x-B _) = x; abel⟩

/-- Extend simultaneous diagram A' = L A, G = G' L to some change of basis L.
Here the two maps A, A' are injective, G, G' are onto, and G A = G' A'. -/
theorem equate_pair {A A' : U →ₗ[F] V} {G G' : V →ₗ[F] W}
    [FiniteDimensional F V] (hA : Injective A) (hA' : Injective A')
    (hG : Surjective G) (hG' : Surjective G') (h : G ∘ₗ A = G' ∘ₗ A') :
    ∃ L : V ≃ₗ[F] V, (∀ x, L (A x) = A' x) ∧ (∀ y, G y = G' (L y)) := by
  let f := G ∘ₗ A
  obtain ⟨B,k,hB,hk⟩ := lin_split G hG
  obtain ⟨B',k',hB',hk'⟩ := lin_split G' hG'
  have eqn x : G (A x) = G' (A' x) := LinearMap.congr_fun h x
  have hh {A : U →ₗ[F] V} {G : V →ₗ[F] W} (hA : Injective A)
      (hg : ∀ x, G (A x)=f x) (B : W →ₗ[F] V) {k : V →ₗ[F] ker G}
      (hk : ∀ x, B (G x)+(k x).val=x) :
      Injective (k ∘ₗ A ∘ₗ (ker f).subtype) := by
    intro x y hxy
    have hxx (x : ker f) : ↑(k (A x.val)) = A x.val := by
      simpa only [hg, show f x.val = 0 from x.property, map_zero,zero_add] using hk (A x.val)
    apply Subtype.ext
    apply hA
    rw [←hxx x,←hxx y]
    exact congrArg Subtype.val hxy
  have hd : dim (ker G) = dim (ker G') := by
    have hr := G.finrank_range_add_finrank_ker
    have hr' := G'.finrank_range_add_finrank_ker
    rw [range_eq_top.mpr hG] at hr
    rw [range_eq_top.mpr hG'] at hr'
    exact Nat.add_left_cancel (hr.trans hr'.symm)
  obtain ⟨C,hC⟩ := equate (hh hA (fun _ => rfl) B hk)
    (hh hA' (fun x => (eqn x).symm) B' hk') hd
  let E := k' ∘ₗ A' - C.toLinearMap ∘ₗ k ∘ₗ A
  obtain ⟨D,hD⟩ := mem_range_comp (show ker f ≤ ker E by
    intro x hx
    change k' (A' x) - C (k (A x)) = 0
    have heq : C (k (A x)) = k' (A' x) := hC ⟨x,hx⟩
    rw [heq,sub_self])
  let L := B' ∘ₗ G + (ker G').subtype ∘ₗ (C.toLinearMap ∘ₗ k + D ∘ₗ G)
  have hl (x : V) : G x = G' (L x) := by
    change G x = G' (B' (G x) + ((C (k x)+D (G x)) : ker G').val)
    rw [map_add,hB', show G' ((C (k x)+D (G x)) : ker G').val = 0 from
      (C (k x)+D (G x)).property,add_zero]
  have hli : Injective L := by
    rw [← LinearMap.ker_eq_bot,eq_bot_iff]
    intro x hx
    have hy : G x=0 := by rw [hl,show L x=0 from hx,map_zero]
    change B' _ + ((C (k x)+ D (G x)) : ker G').val = 0 at hx
    simp only [hy,map_zero,zero_add,add_zero] at hx
    have h00 : C (k x) = 0 := Subtype.ext hx
    have h0 : k x = 0 := C.injective (by rw [map_zero, h00])
    have hw := hk x
    rw [h0,hy,map_zero,Submodule.coe_zero,zero_add] at hw
    rw [←hw]; exact Submodule.zero_mem _
  refine ⟨LinearEquiv.ofInjectiveEndo L hli, fun x => ?_, hl⟩
  change B' (G (A x)) + ((C (k (A x))+D (G (A x))) : ker G').val = _
  have heq : D (G (A x)) = k' (A' x) - C (k (A x)) := LinearMap.congr_fun hD x
  rw [heq,add_sub_cancel,eqn,hk']

end HadwigerCounterexample

end

end OAI
