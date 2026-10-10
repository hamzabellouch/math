import OAI.RepresentationTheory.RestrictedTilting.GoodKernel
import OAI.RepresentationTheory.RestrictedTilting.RepProducts

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
variable (k : Type u) [Field k]

 
noncomputable def extensionCoverMap {A B P Q : FDRep k (SL2 k)}
    (f : A ⟶ B) (a : P ⟶ A) (s : Q ⟶ B) : repProduct k P Q ⟶ B :=
  repFst k P Q ≫ a ≫ f + repSnd k P Q ≫ s

lemma extensionCoverMap_goodKernel {A B C P Q : FDRep k (SL2 k)}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact)
    (a : P ⟶ A) (q : Q ⟶ C) (ha : HasGoodKernel k a) (hq : HasGoodKernel k q)
    (s : Q ⟶ B) (hs : s ≫ g = q) :
    HasGoodKernel k (extensionCoverMap k f a s) := by
  have := hS.mono_f
  have := ha.epi k
  have := hq.epi k
  have hf := fdrep_injective k f
  have hex := fdrep_exact k hS.exact
  have hfg (x : A) : fdrepLinear k g (fdrepLinear k f x) = 0 :=
    congrArg (fun z => fdrepLinear k z x) w
  have hsg (y : Q) : fdrepLinear k g (fdrepLinear k s y) = fdrepLinear k q y :=
    congrArg (fun z => fdrepLinear k z y) hs
  let F := extensionCoverMap k f a s
  have hF (x : repProduct k P Q) : fdrepLinear k F x =
      fdrepLinear k f (fdrepLinear k a x.1) + fdrepLinear k s x.2 := rfl
  have hFsurj : Function.Surjective (fdrepLinear k F) := by
    intro b
    obtain ⟨y,hy⟩ := fdrep_surjective k q (fdrepLinear k g b)
    have hmem : b - fdrepLinear k s y ∈ LinearMap.range (fdrepLinear k f) := by
      rw [hex]
      change fdrepLinear k g (b - fdrepLinear k s y) = 0
      rw [map_sub, hsg, hy, sub_self]
    obtain ⟨x,hx⟩ := hmem
    obtain ⟨v,hv⟩ := fdrep_surjective k a x
    refine ⟨(v,y), ?_⟩
    erw [hF, hv, hx, sub_add_cancel]
  let K := fdrepKernel k F
  let Ka := fdrepKernel k a
  let Kq := fdrepKernel k q
  have hker (x : K) : fdrepLinear k q x.val.2 = 0 := by
    have h := congrArg (fdrepLinear k g) (show fdrepLinear k F x.val = 0 from x.property)
    rw [hF, map_add, hfg, hsg, zero_add, map_zero] at h
    exact h
  let i : Ka ⟶ K := fdrepHom k
    { toFun := fun x => ⟨(x.val,0), by
        change fdrepLinear k F (x.val,0) = 0
        erw [hF, show fdrepLinear k a x.val = 0 from x.property, map_zero, map_zero, add_zero]⟩
      map_add' := by intros; apply Subtype.ext; exact Prod.ext rfl (zero_add _).symm
      map_smul' := by intros; apply Subtype.ext; exact Prod.ext rfl (smul_zero _).symm }
    (by intro t x; apply Subtype.ext; exact Prod.ext rfl (map_zero (Q.ρ t)).symm)
  let j : K ⟶ Kq := fdrepHom k
    { toFun := fun x => ⟨x.val.2, hker x⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    (by intros; rfl)
  have wij : i ≫ j = 0 := by apply fdrep_hom_ext k; intro x; rfl
  have hi : Function.Injective (fdrepLinear k i) := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : K => z.val.1) h
  have hj : Function.Surjective (fdrepLinear k j) := by
    intro y
    have hmem : fdrepLinear k s y.val ∈ LinearMap.range (fdrepLinear k f) := by
      rw [hex]
      change fdrepLinear k g (fdrepLinear k s y.val) = 0
      rw [hsg]
      exact y.property
    obtain ⟨x,hx⟩ := hmem
    obtain ⟨v,hv⟩ := fdrep_surjective k a (-x)
    have hvy : fdrepLinear k F (v,y.val) = 0 := by
      erw [hF, hv, map_neg, hx, neg_add_cancel]
    exact ⟨⟨(v,y.val),hvy⟩,rfl⟩
  have he : LinearMap.range (fdrepLinear k i) = LinearMap.ker (fdrepLinear k j) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩; rfl
    · intro hx
      have hx2 : x.val.2 = 0 := congrArg Subtype.val (show fdrepLinear k j x = 0 from hx)
      have hx1 : fdrepLinear k a x.val.1 = 0 := by
        apply hf
        have h := show fdrepLinear k F x.val = 0 from x.property
        rw [hF, hx2, map_zero, add_zero] at h
        exact h.trans (map_zero _).symm
      refine ⟨⟨x.val.1,hx1⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hx2.symm
  have hK : HasGoodFiltration k K :=
    (ha.kernel_good k).extension k (hq.kernel_good k) i j wij (fdrep_shortExact k _ hi hj he)
  exact ⟨K, fdrepKernelι k F, (by apply fdrep_hom_ext k; intro x; exact x.property),
    fdrepKernel_shortExact k F hFsurj, hK⟩
end FiberFunctorProof

end OAI
