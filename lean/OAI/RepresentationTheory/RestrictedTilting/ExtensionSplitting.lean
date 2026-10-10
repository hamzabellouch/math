import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.DualSplitting
import OAI.RepresentationTheory.RestrictedTilting.RepresentationMaps

namespace OAI

/-! Representation extension splitting, duality and good filtrations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
universe u
variable (k : Type u) [Field k]
variable {G : Type u} [Monoid G]

lemma fdrep_hom_ext {A B : FDRep k G} {f g : A ⟶ B}
    (h : ∀ x, fdrepLinear k f x = fdrepLinear k g x) : f = g := by
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  exact LinearMap.ext h

@[simp] lemma fdrep_comp_apply {A B C : FDRep k G} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    fdrepLinear k (f ≫ g) x = fdrepLinear k g (fdrepLinear k f x) := rfl

@[simp] lemma fdrep_id_apply {A : FDRep k G} (x : A) :
    fdrepLinear k (𝟙 A) x = x := rfl

@[simp] lemma fdrep_zero_apply {A B : FDRep k G} (x : A) :
    fdrepLinear k (0 : A ⟶ B) x = 0 := rfl

 

def RepExtensionSplit (P : FDRep k G → Prop) (A C : FDRep k G) : Prop :=
  ∀ (B : FDRep k G), P B → ∀ (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0),
    (ShortComplex.mk f g w).ShortExact → ∃ s : C ⟶ B, s ≫ g = 𝟙 C

 
lemma fdrep_quotient_splice {A₁ A A₂ B C : FDRep k G}
    (i : A₁ ⟶ A) (j : A ⟶ A₂) (v : i ≫ j = 0)
    (hT : (ShortComplex.mk i j v).ShortExact)
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    ∃ (Q : FDRep k G) (a : A₂ ⟶ Q) (b : Q ⟶ C) (q : B ⟶ Q)
      (wab : a ≫ b = 0),
      Function.Surjective (fdrepLinear k q) ∧
      f ≫ q = j ≫ a ∧ q ≫ b = g ∧
      (ShortComplex.mk a b wab).ShortExact := by
  have := hT.mono_f
  have := hT.epi_g
  have := hS.mono_f
  have := hS.epi_g
  have hi := fdrep_injective k i
  have hj := fdrep_surjective k j
  have hf := fdrep_injective k f
  have hg := fdrep_surjective k g
  have hT' := fdrep_exact k hT.exact
  have hS' := fdrep_exact k hS.exact
  let Q := fdrepQuotient k (i ≫ f)
  let q : B ⟶ Q := fdrepQuotientπ k (i ≫ f)
  have hq := fdrepQuotientπ_surjective k (i ≫ f)
  have hqa : LinearMap.ker (fdrepLinear k j) ≤ LinearMap.ker (fdrepLinear k (f ≫ q)) := by
    intro x hx
    rw [← hT'] at hx
    obtain ⟨y,rfl⟩ := hx
    apply (fdrepQuotientπ_eq_zero k (i ≫ f) _).mpr
    exact ⟨y,rfl⟩
  let a := fdrepDesc k j hj (f ≫ q) hqa
  have ha : j ≫ a = f ≫ q := fdrepDesc_comp k j hj (f ≫ q) hqa
  have hqb : LinearMap.ker (fdrepLinear k q) ≤ LinearMap.ker (fdrepLinear k g) := by
    intro x hx
    obtain ⟨y,rfl⟩ := (fdrepQuotientπ_eq_zero k (i ≫ f) x).mp hx
    have h := LinearMap.congr_fun (congrArg (fdrepLinear k) w) (fdrepLinear k i y)
    exact h
  let b := fdrepDesc k q hq g hqb
  have hb : q ≫ b = g := fdrepDesc_comp k q hq g hqb
  have hab : a ≫ b = 0 := by
    apply fdrep_hom_ext k
    intro x
    obtain ⟨y,rfl⟩ := hj x
    have hea := LinearMap.congr_fun (congrArg (fdrepLinear k) ha) y
    have heb := LinearMap.congr_fun (congrArg (fdrepLinear k) hb) (fdrepLinear k f y)
    change fdrepLinear k b (fdrepLinear k a (fdrepLinear k j y)) = 0
    change fdrepLinear k a (fdrepLinear k j y) = fdrepLinear k q (fdrepLinear k f y) at hea
    rw [hea]
    rw [show fdrepLinear k b (fdrepLinear k q (fdrepLinear k f y)) =
      fdrepLinear k g (fdrepLinear k f y) from heb]
    exact LinearMap.congr_fun (congrArg (fdrepLinear k) w) y
  refine ⟨Q,a,b,q,hab,hq,ha.symm,hb,fdrep_shortExact k _ ?_ ?_ ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨y,rfl⟩ := hj x
    have hy : fdrepLinear k q (fdrepLinear k f y) = 0 := by
      have := LinearMap.congr_fun (congrArg (fdrepLinear k) ha) y
      exact this.symm.trans hx
    obtain ⟨z,hz⟩ := (fdrepQuotientπ_eq_zero k (i ≫ f) _).mp hy
    have hfz : fdrepLinear k i z = y := hf hz
    rw [← hfz]
    exact LinearMap.congr_fun (congrArg (fdrepLinear k) v) z
  · intro c
    obtain ⟨x,rfl⟩ := hg c
    exact ⟨fdrepLinear k q x, LinearMap.congr_fun (congrArg (fdrepLinear k) hb) x⟩
  · apply le_antisymm
    · rw [LinearMap.range_le_ker_iff]
      exact congrArg (fdrepLinear k) hab
    · intro x hx
      obtain ⟨y,rfl⟩ := hq x
      have hy : fdrepLinear k g y = 0 := by
        have := LinearMap.congr_fun (congrArg (fdrepLinear k) hb) y
        exact this.symm.trans hx
      have hyrange : y ∈ LinearMap.range (fdrepLinear k f) := by
        rw [hS']
        exact hy
      obtain ⟨z,rfl⟩ := hyrange
      exact ⟨fdrepLinear k j z,
        LinearMap.congr_fun (congrArg (fdrepLinear k) ha) z⟩


 

lemma fdrep_kernel_splice {A₁ A A₂ B C : FDRep k G}
    (i : A₁ ⟶ A) (j : A ⟶ A₂) (v : i ≫ j = 0)
    (hT : (ShortComplex.mk i j v).ShortExact)
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact)
    (r : B ⟶ A₂) (hr : f ≫ r = j) :
    ∃ (K : FDRep k G) (a : A₁ ⟶ K) (b : K ⟶ C) (t : K ⟶ B)
      (wab : a ≫ b = 0),
      Function.Injective (fdrepLinear k t) ∧ t ≫ g = b ∧
      (ShortComplex.mk a b wab).ShortExact := by
  have := hT.mono_f
  have := hT.epi_g
  have := hS.mono_f
  have := hS.epi_g
  have hi := fdrep_injective k i
  have hj := fdrep_surjective k j
  have hf := fdrep_injective k f
  have hg := fdrep_surjective k g
  have hT' := fdrep_exact k hT.exact
  have hS' := fdrep_exact k hS.exact
  have hif : (i ≫ f) ≫ r = 0 := by rw [Category.assoc, hr, v]
  let K := fdrepKernel k r
  let t : K ⟶ B := fdrepKernelι k r
  let a : A₁ ⟶ K := fdrepKernelLift k (i ≫ f) r hif
  let b : K ⟶ C := t ≫ g
  have hab : a ≫ b = 0 := by
    change a ≫ (t ≫ g) = 0
    rw [← Category.assoc, fdrepKernelLift_ι, Category.assoc, w, comp_zero]
  refine ⟨K,a,b,t,hab,Subtype.val_injective,rfl,fdrep_shortExact k _ ?_ ?_ ?_⟩
  · intro x y hxy
    apply hi
    apply hf
    exact congrArg Subtype.val hxy
  · intro c
    obtain ⟨x,hx⟩ := hg c
    obtain ⟨y,hy⟩ := hj (fdrepLinear k r x)
    have hy' : fdrepLinear k r (fdrepLinear k f y) = fdrepLinear k j y :=
      LinearMap.congr_fun (congrArg (fdrepLinear k) hr) y
    have hz : fdrepLinear k r (x-fdrepLinear k f y) = 0 := by
      rw [map_sub, hy', hy, sub_self]
    refine ⟨⟨x-fdrepLinear k f y,hz⟩, ?_⟩
    change fdrepLinear k g (x-fdrepLinear k f y) = c
    rw [map_sub, hx]
    have hw := LinearMap.congr_fun (congrArg (fdrepLinear k) w) y
    change fdrepLinear k g (fdrepLinear k f y) = 0 at hw
    rw [hw, sub_zero]
  · apply le_antisymm
    · rw [LinearMap.range_le_ker_iff]
      exact congrArg (fdrepLinear k) hab
    · intro x hx
      have hx' : x.val ∈ LinearMap.range (fdrepLinear k f) := by
        rw [hS']
        exact hx
      obtain ⟨y,hy⟩ := hx'
      have hyk : y ∈ LinearMap.ker (fdrepLinear k j) := by
        have h := LinearMap.congr_fun (congrArg (fdrepLinear k) hr) y
        change fdrepLinear k r (fdrepLinear k f y) = fdrepLinear k j y at h
        change fdrepLinear k j y = 0
        rw [← h, hy]
        exact x.property
      rw [← hT'] at hyk
      obtain ⟨z,hz⟩ := hyk
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change fdrepLinear k f (fdrepLinear k i z) = x.val
      rw [hz,hy]

 

theorem RepExtensionSplit.extension_left (P : FDRep k G → Prop)
    (hSub : ∀ {X Y : FDRep k G} (f : X ⟶ Y),
      Function.Injective (fdrepLinear k f) → P Y → P X)
    (hQuot : ∀ {X Y : FDRep k G} (f : X ⟶ Y),
      Function.Surjective (fdrepLinear k f) → P X → P Y)
    {A₁ A A₂ C : FDRep k G}
    (i : A₁ ⟶ A) (j : A ⟶ A₂) (v : i ≫ j = 0)
    (hT : (ShortComplex.mk i j v).ShortExact)
    (h₁ : RepExtensionSplit k P A₁ C) (h₂ : RepExtensionSplit k P A₂ C) :
    RepExtensionSplit k P A C := by
  intro B hB f g w hS
  obtain ⟨Q,a,b,q,wab,hq,hfq,hqb,hQ⟩ :=
    fdrep_quotient_splice k i j v hT f g w hS
  obtain ⟨s,hs⟩ := h₂ Q (hQuot q hq hB) a b wab hQ
  let e := ShortComplex.Splitting.ofExactOfSection (ShortComplex.mk a b wab)
    hQ.exact s hs hQ.mono_f
  have hr : f ≫ (q ≫ e.r) = j := by
    rw [← Category.assoc, hfq, Category.assoc, e.f_r, Category.comp_id]
  obtain ⟨K,a',b',t,wab',ht,htg,hK⟩ :=
    fdrep_kernel_splice k i j v hT f g w hS (q ≫ e.r) hr
  obtain ⟨s',hs'⟩ := h₁ K (hSub t ht hB) a' b' wab' hK
  refine ⟨s' ≫ t, ?_⟩
  rw [Category.assoc, htg, hs']

end FiberFunctorProof

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k]
lemma fgmodule_mate_apply {A B : FGModuleCat k} (f : A ⟶ B)
    (l : Module.Dual k B) (x : A) :
    (show Module.Dual k A from (fᘁ).hom.hom l) x = l (f.hom.hom x) := by
  have h := rightAdjointMate_comp_evaluation f
  have hx := ConcreteCategory.congr_hom h (l ⊗ₜ[k] x)
  change contractLeft k A
      (TensorProduct.map (fᘁ).hom.hom (LinearMap.id : A →ₗ[k] A) (l ⊗ₜ[k] x)) =
    contractLeft k B
      (TensorProduct.map (LinearMap.id : Module.Dual k B →ₗ[k] Module.Dual k B)
        f.hom.hom (l ⊗ₜ[k] x)) at hx
  change (contractLeft k A)
      (((fᘁ).hom.hom : Module.Dual k B →ₗ[k] Module.Dual k A) l ⊗ₜ[k] x) =
    (contractLeft k B) (l ⊗ₜ[k] f.hom.hom x) at hx
  exact hx

lemma fdrep_dual_repr {G : Type u} [Group G] (A : FDRep k G) :
    (Aᘁ).ρ = Representation.dual A.ρ := by
  ext g l : 2
  apply LinearMap.ext
  intro x
  change (show Module.Dual k A from ((Action.ρ (Aᘁ)) g).hom.hom l) x = _
  rw [Action.rightDual_ρ]
  exact fgmodule_mate_apply k _ _ _

end

section
open CategoryTheory CategoryTheory.MonoidalCategory
universe u
variable (k : Type u) [Field k]
variable {G : Type u} [Group G]

 
noncomputable def fdrepDualMap {A B : FDRep k G} (f : A ⟶ B) : Bᘁ ⟶ Aᘁ :=
  fdrepHom k (fdrepLinear k f).dualMap (by
    intro g φ
    change Module.Dual k B at φ
    rw [fdrep_dual_repr, fdrep_dual_repr]
    apply LinearMap.ext
    intro x
    change φ (B.ρ g⁻¹ (fdrepLinear k f x)) = φ (fdrepLinear k f (A.ρ g⁻¹ x))
    exact congrArg φ (fdrepLinear_comm k f g⁻¹ x).symm)

lemma fdrepDualMap_zero_comp {A B C : FDRep k G}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
    fdrepDualMap k g ≫ fdrepDualMap k f = 0 := by
  apply fdrep_hom_ext
  intro φ
  change Module.Dual k C at φ
  apply LinearMap.ext
  intro x
  change φ (fdrepLinear k g (fdrepLinear k f x)) = 0
  have h := LinearMap.congr_fun (congrArg (fdrepLinear k) w) x
  change fdrepLinear k g (fdrepLinear k f x) = 0 at h
  rw [h, map_zero]

lemma fdrep_dual_shortExact {A B C : FDRep k G}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    (ShortComplex.mk (fdrepDualMap k g) (fdrepDualMap k f)
      (fdrepDualMap_zero_comp k f g w)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine fdrep_shortExact k _
    (LinearMap.dualMap_injective_of_surjective (fdrep_surjective k g))
    (LinearMap.dualMap_surjective_of_injective (fdrep_injective k f)) ?_
  change LinearMap.range (fdrepLinear k g).dualMap =
    LinearMap.ker (fdrepLinear k f).dualMap
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, fdrep_exact k hS.exact]

 

theorem RepExtensionSplit.of_dual (P : FDRep k G → Prop)
    (hDual : ∀ B, P B → P Bᘁ) {A C : FDRep k G}
    (h : RepExtensionSplit k P Cᘁ Aᘁ) : RepExtensionSplit k P A C := by
  intro B hB f g w hS
  obtain ⟨s,hs⟩ := h Bᘁ (hDual B hB) (fdrepDualMap k g)
    (fdrepDualMap k f) (fdrepDualMap_zero_comp k f g w)
    (fdrep_dual_shortExact k f g w hS)
  have hs' : (fdrepLinear k f).dualMap.comp (fdrepLinear k s) = LinearMap.id :=
    congrArg (fdrepLinear k) hs
  have hsρ : ∀ a φ, fdrepLinear k s (Representation.dual A.ρ a φ) =
      Representation.dual B.ρ a (fdrepLinear k s φ) := by
    intro a φ
    rw [← fdrep_dual_repr k A, ← fdrep_dual_repr k B]
    exact fdrepLinear_comm k s a φ
  obtain ⟨r,hr,hrρ⟩ := equivariant_retraction_of_dual_section A.ρ B.ρ
    (fdrepLinear k f) (fdrepLinear k s) hs' hsρ
  let r' : B ⟶ A := fdrepHom k r hrρ
  have hfr : f ≫ r' = 𝟙 A := by
    apply fdrep_hom_ext
    exact LinearMap.congr_fun hr
  let spl := ShortComplex.Splitting.ofExactOfRetraction (ShortComplex.mk f g w)
    hS.exact r' hfr hS.epi_g
  exact ⟨spl.s,spl.s_g⟩

end

section
open CategoryTheory CategoryTheory.MonoidalCategory
universe u
variable (k : Type u) [Field k]

 
abbrev RationalExtensionSplit (A C : FDRep k (SL2 k)) : Prop :=
  RepExtensionSplit k (fun B => IsRational k B.ρ) A C

lemma rationalExtensionSplit_extension_left {A₁ A A₂ C : FDRep k (SL2 k)}
    (i : A₁ ⟶ A) (j : A ⟶ A₂) (v : i ≫ j = 0)
    (hT : (ShortComplex.mk i j v).ShortExact)
    (h₁ : RationalExtensionSplit k A₁ C) (h₂ : RationalExtensionSplit k A₂ C) :
    RationalExtensionSplit k A C := by
  apply RepExtensionSplit.extension_left k _ (fun f hf h => ?_) (fun f hf h => ?_)
    i j v hT h₁ h₂
  · exact IsRational.of_injective k _ _ (fdrepLinear k f) hf (fdrepLinear_comm k f) h
  · exact IsRational.of_surjective k _ _ (fdrepLinear k f) hf (fdrepLinear_comm k f) h

lemma rationalExtensionSplit_of_dual {A C : FDRep k (SL2 k)}
    (h : RationalExtensionSplit k Cᘁ Aᘁ) : RationalExtensionSplit k A C := by
  apply RepExtensionSplit.of_dual k _ (fun B hB => ?_) h
  rw [fdrep_dual_repr]
  exact IsRational.dual k B.ρ hB

lemma rationalExtensionSplit_zero {A C : FDRep k (SL2 k)} (hA : IsZero A) :
    RationalExtensionSplit k A C := by
  intro B _ f g w hS
  have : Mono g := hS.exact.mono_g (hA.eq_zero_of_src f)
  have := hS.epi_g
  have : IsIso g := isIso_of_mono_of_epi g
  exact ⟨inv g, IsIso.inv_hom_id g⟩

variable [Infinite k]

 
theorem costandard_standard_extension_split (m n : ℕ) :
    RationalExtensionSplit k (costandard k m) (costandard k n)ᘁ := by
  intro B hB f g w hS
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨s,hs,hsρ⟩ := standard_costandard_split k B.ρ hB n m
    (fdrepLinear k f) (fdrepLinear k g) (fdrep_injective k f) (fdrep_surjective k g)
    (fdrep_exact k hS.exact).symm (fdrepLinear_comm k f) (by
      intro a x
      have h := fdrepLinear_comm k g a x
      rw [fdrep_dual_repr] at h
      exact h)
  let s' : (costandard k n)ᘁ ⟶ B := fdrepHom k s (by
    intro a x
    rw [fdrep_dual_repr]
    exact hsρ a x)
  refine ⟨s', fdrep_hom_ext k (LinearMap.congr_fun hs)⟩

 
theorem good_standard_extension_split {A : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) (n : ℕ) :
    RationalExtensionSplit k A (costandard k n)ᘁ := by
  induction hA with
  | zero A hA => exact rationalExtensionSplit_zero k hA
  | @step A B m f g w hS hA ih =>
    exact rationalExtensionSplit_extension_left k f g w hS ih
      (costandard_standard_extension_split k m n)

 

theorem good_weyl_extension_split {A C : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) (hC : HasGoodFiltration k Cᘁ) :
    RationalExtensionSplit k A C := by
  induction hA with
  | zero A hA => exact rationalExtensionSplit_zero k hA
  | @step A B m f g w hS hA ih =>
    apply rationalExtensionSplit_extension_left k f g w hS ih
    exact rationalExtensionSplit_of_dual k (good_standard_extension_split k hC m)

end

section
open scoped ZeroObject
universe u
variable (k : Type u) [Field k]
lemma HasGoodFiltration.of_iso {A B : FDRep k (SL2 k)}
    (h : HasGoodFiltration k A) (e : A ≅ B) : HasGoodFiltration k B := by
  cases h with
  | zero A hA => exact .zero B (hA.of_iso e.symm)
  | @step A B' n f g w hS hA =>
    let f' := f ≫ e.hom
    let g' := e.inv ≫ g
    have w' : f' ≫ g' = 0 := by simpa [f', g'] using w
    have hS' : (ShortComplex.mk f' g' w').ShortExact :=
      ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (Iso.refl A) e (Iso.refl (costandard k n))
          (by simp [f']) (by simp [g'])) hS
    exact .step n f' g' w' hS' hA

lemma costandard_hasGoodFiltration (n : ℕ) : HasGoodFiltration k (costandard k n) := by
  let S : ShortComplex (FDRep k (SL2 k)) := ShortComplex.mk
    (0 : 0 ⟶ costandard k n) (𝟙 _) (by simp)
  have hS : S.ShortExact :=
    (ShortComplex.Splitting.ofIsZeroOfIsIso S (isZero_zero _) inferInstance).shortExact
  exact .step n S.f S.g S.zero hS (.zero _ (isZero_zero _))

end

universe u
variable (k : Type u) [Field k]
lemma fdrepHom_isIso_of_bijective {G : Type u} [Monoid G] {A B : FDRep k G}
    (f : A ⟶ B) (hf : Function.Bijective (fdrepLinear k f)) : IsIso f := by
  have : Mono ((fdrepForget k G).map f) := (ModuleCat.mono_iff_injective _).mpr hf.1
  have : Epi ((fdrepForget k G).map f) := (ModuleCat.epi_iff_surjective _).mpr hf.2
  have : Mono f := (fdrepForget k G).mono_of_mono_map (by infer_instance)
  have : Epi f := (fdrepForget k G).epi_of_epi_map (by infer_instance)
  exact isIso_of_mono_of_epi f

end FiberFunctorProof
end

end OAI
