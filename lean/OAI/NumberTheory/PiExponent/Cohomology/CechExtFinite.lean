import OAI.NumberTheory.PiExponent.Cohomology.CechLinear
import OAI.NumberTheory.PiExponent.Cohomology.CechZero
import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections

namespace OAI

namespace PiExponent.GeometrySupport.CechExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
variable {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤))

private abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

def ActualExt (_ρ : K →+* Γ(X,⊤)) (A M : X.Modules) (q : ℕ) : Type 1 := Ext.{1} A M q

instance (A M : X.Modules) (q : ℕ) : AddCommGroup (ActualExt ρ A M q) :=
  inferInstanceAs (AddCommGroup (Ext.{1} A M q))

instance globalModule (A M : X.Modules) (q : ℕ) :
    Module Γ(X,⊤) (ActualExt ρ A M q) :=
  inferInstanceAs (Module Γ(X,⊤) (Ext.{1} A M q))

instance scalarModule (A M : X.Modules) (q : ℕ) : Module K (ActualExt ρ A M q) :=
  Module.compHom _ ρ

def connecting (A : X.Modules) (S : ShortComplex X.Modules) (hS : S.ShortExact) (q : ℕ) :
    ActualExt ρ A S.X₃ q →ₗ[K] ActualExt ρ A S.X₁ (q+1) where
  toFun x := Ext.comp x hS.extClass rfl
  map_add' x y := Ext.add_comp x y hS.extClass rfl
  map_smul' a x := by
    change Ext.comp ((ρ a) • (show Ext.{1} A S.X₃ q from x)) hS.extClass rfl =
      (ρ a) • Ext.comp x hS.extClass rfl
    exact Ext.smul_comp (C := X.Modules) (R := Γ(X, ⊤)) x hS.extClass rfl (ρ a)

lemma connecting_surjective (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ) :
    Function.Surjective (connecting ρ A S hS q) := by
  intro x
  exact Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl

def LocallyAcyclic (M : X.Modules) : Prop :=
  ∀ (q : ℕ) (t : Fin (q+1) → J) (k : ℕ)
    (x : Ext.{1} (schemeFreeOpen (CechHigher.intersection U t)) M (k+1)), x = 0

lemma locallyAcyclic_quotient (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Injective S.X₂] (hlocal : LocallyAcyclic U S.X₁) : LocallyAcyclic U S.X₃ := by
  intro q t k y
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
    (schemeFreeOpen (CechHigher.intersection U t)) hS y
    (n₁ := k+2) rfl (hlocal q t (k+1) _)
  rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
  exact hz.symm

open CechLinear

def descent (S : ShortComplex X.Modules) [Injective S.X₂] (q : ℕ) :
    cycles U ρ S.X₁ (q+1) →ₗ[K] cycles U ρ S.X₃ q :=
  ((mapLinear U ρ S.g q).comp
    ((primitive U ρ S.X₂ q).comp (mapCycles U ρ S.f (q+1)))).codRestrict
      (cycles U ρ S.X₃ q) (fun a => by
        change differentialLinear U ρ S.X₃ q
          (mapLinear U ρ S.g q (primitive U ρ S.X₂ q (mapCycles U ρ S.f (q + 1) a))) = 0
        refine (mapLinear_differential U ρ S.g q _).symm.trans ?_
        refine (congrArg (mapLinear U ρ S.g (q + 1))
          (primitive_spec U ρ S.X₂ q (mapCycles U ρ S.f (q + 1) a))).trans ?_
        change mapLinear U ρ S.g (q + 1) (mapLinear U ρ S.f (q + 1) a.val) = 0
        rw [← LinearMap.comp_apply, ← mapLinear_comp, S.zero, mapLinear_zero]
        rfl)


lemma descent_lift (S : ShortComplex X.Modules) [Injective S.X₂] (q : ℕ)
    (a : cycles U ρ S.X₁ (q+1)) (b : Cochain U ρ S.X₂ q)
    (c : cycles U ρ S.X₃ q)
    (hdb : differentialLinear U ρ S.X₂ q b = mapLinear U ρ S.f (q+1) a.val)
    (hbg : mapLinear U ρ S.g q b = c.val) :
    ∃ z : cycles U ρ S.X₂ q, descent U ρ S q a - c = mapCycles U ρ S.g q z := by
  let β := primitive U ρ S.X₂ q (mapCycles U ρ S.f (q+1) a)
  have hβ : differentialLinear U ρ S.X₂ q β = mapLinear U ρ S.f (q+1) a.val :=
    primitive_spec U ρ S.X₂ q (mapCycles U ρ S.f (q+1) a)
  let z : cycles U ρ S.X₂ q := ⟨β-b, by
    change differentialLinear U ρ S.X₂ q (β-b) = 0
    rw [map_sub, hβ, hdb, sub_self]⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change mapLinear U ρ S.g q β - c.val = mapLinear U ρ S.g q (β-b)
  rw [map_sub, hbg]

def comparisonStep (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ A S.X₃ q) :
    cycles U ρ S.X₁ (q+1) →ₗ[K] ActualExt ρ A S.X₁ (q+1) :=
  (connecting ρ A S hS q).comp (F.comp (descent U ρ S q))

lemma comparisonStep_surjective (V : X.Opens) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (hlocal : LocallyAcyclic U S.X₁)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ (schemeFreeOpen V) S.X₃ q)
    (hF : Function.Surjective F)
    (hmiddle : ∀ z : cycles U ρ S.X₂ q,
      connecting ρ (schemeFreeOpen V) S hS q (F (mapCycles U ρ S.g q z)) = 0) :
    Function.Surjective (comparisonStep U ρ (schemeFreeOpen V) S hS q F) := by
  intro x
  obtain ⟨y, hy⟩ := connecting_surjective ρ (schemeFreeOpen V) S hS q x
  obtain ⟨c, hc⟩ := hF y
  obtain ⟨b,a,hb,ha,had⟩ := CechHigher.connecting_cocycle X.ringCatSheaf U S hS
    (fun t z => hlocal q t 0 z) c.val c.property
  let a' : cycles U ρ S.X₁ (q+1) := ⟨a,had⟩
  obtain ⟨z,hz⟩ := descent_lift U ρ S q a' b c ha.symm hb
  let H := (connecting ρ (schemeFreeOpen V) S hS q).comp F
  have he : H (descent U ρ S q a') = H c := by
    apply sub_eq_zero.mp
    rw [← H.map_sub, hz]
    exact hmiddle z
  refine ⟨a', ?_⟩
  change H (descent U ρ S q a') = x
  rw [he]
  change connecting ρ (schemeFreeOpen V) S hS q (F c) = x
  rw [hc,hy]

lemma comparisonStep_boundary (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ A S.X₃ q)
    (hmiddle : ∀ z : cycles U ρ S.X₂ q,
      connecting ρ A S hS q (F (mapCycles U ρ S.g q z)) = 0)
    (b : Cochain U ρ S.X₁ q) :
    comparisonStep U ρ A S hS q F (boundaryToCycles U ρ S.X₁ q b) = 0 := by
  have hdb : differentialLinear U ρ S.X₂ q (mapLinear U ρ S.f q b) =
      mapLinear U ρ S.f (q+1) (boundaryToCycles U ρ S.X₁ q b).val :=
    (mapLinear_differential U ρ S.f q b).symm
  have hbg : mapLinear U ρ S.g q (mapLinear U ρ S.f q b) =
      (0 : cycles U ρ S.X₃ q).val := by
    rw [← LinearMap.comp_apply, ← mapLinear_comp, S.zero, mapLinear_zero]
    rfl
  obtain ⟨z,hz⟩ := descent_lift U ρ S q (boundaryToCycles U ρ S.X₁ q b)
    (mapLinear U ρ S.f q b) 0 hdb hbg
  rw [sub_zero] at hz
  change connecting ρ A S hS q (F (descent U ρ S q (boundaryToCycles U ρ S.X₁ q b))) = 0
  rw [hz]
  exact hmiddle z

def mkZeroLinear (A M : X.Modules) :
    letI : Module Γ(X,⊤) (A ⟶ M) := sheafHomModule X A M
    letI := Module.compHom (A ⟶ M) ρ
    (A ⟶ M) →ₗ[K] ActualExt ρ A M 0 := by
  letI : Module Γ(X,⊤) (A ⟶ M) := sheafHomModule X A M
  letI := Module.compHom (A ⟶ M) ρ
  refine {
    toFun := Ext.mk₀
    map_add' := Ext.mk₀_add
    map_smul' := ?_ }
  intro r f
  change Ext.mk₀ ((ρ r) • f) = (ρ r) • (show Ext.{1} A M 0 from Ext.mk₀ f)
  exact Ext.mk₀_smul (C := X.Modules) (R := Γ(X,⊤)) (X := A) (Y := M) (ρ r) f

@[simp] theorem mkZeroLinear_apply (A M : X.Modules) (f : A ⟶ M) :
    mkZeroLinear ρ A M f = Ext.mk₀ f := rfl

def zeroComparison (M : X.Modules) (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    cycles U ρ M 0 →ₗ[K] ActualExt ρ (schemeFreeOpen V) M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  exact (mkZeroLinear ρ (schemeFreeOpen V) M).comp
    (CechZero.sectionsEquiv U ρ M V hUV hcover).symm.toLinearMap

lemma zeroComparison_surjective (M : X.Modules) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) :
    Function.Surjective (zeroComparison U ρ M V hUV hcover) := by
  intro x
  obtain ⟨f,hf⟩ := (Ext.mk₀_bijective (schemeFreeOpen V) M).surjective x
  refine ⟨CechZero.sectionsEquiv U ρ M V hUV hcover f, ?_⟩
  change Ext.mk₀ ((CechZero.sectionsEquiv U ρ M V hUV hcover).symm
    (CechZero.sectionsEquiv U ρ M V hUV hcover f)) = x
  rw [LinearEquiv.symm_apply_apply,hf]

lemma zeroComparison_middle (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (z : cycles U ρ S.X₂ 0) :
    connecting ρ (schemeFreeOpen V) S hS 0
      (zeroComparison U ρ S.X₃ V hUV hcover (mapCycles U ρ S.g 0 z)) = 0 := by
  change Ext.comp (Ext.mk₀ ((CechZero.sectionsEquiv U ρ S.X₃ V hUV hcover).symm
    (mapCycles U ρ S.g 0 z))) hS.extClass rfl = 0
  rw [CechZero.sectionsEquiv_symm_mapCycles, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

theorem exists_comparison (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (n : ℕ) (M : X.Modules)
    (hlocal : LocallyAcyclic U M) :
    ∃ F : cycles U ρ M (n+1) →ₗ[K] ActualExt ρ (schemeFreeOpen V) M (n+1),
      Function.Surjective F ∧ ∀ b : Cochain U ρ M n, F (boundaryToCycles U ρ M n b) = 0 := by
  let : EnoughInjectives X.Modules := PiExponentSeshadri.ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let F := zeroComparison U ρ S.X₃ V hUV hcover
    have hmid := zeroComparison_middle U ρ V hUV hcover S hS
    exact ⟨comparisonStep U ρ (schemeFreeOpen V) S hS 0 F,
      comparisonStep_surjective U ρ V S hS 0 hlocal F
        (zeroComparison_surjective U ρ S.X₃ V hUV hcover) hmid,
      comparisonStep_boundary U ρ (schemeFreeOpen V) S hS 0 F hmid⟩
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨F,hF,hFb⟩ := ih S.X₃ (locallyAcyclic_quotient U S hS hlocal)
    have hmid (z : cycles U ρ S.X₂ (n+1)) :
        connecting ρ (schemeFreeOpen V) S hS (n+1)
          (F (mapCycles U ρ S.g (n+1) z)) = 0 := by
      obtain ⟨b,rfl⟩ := boundaryToCycles_surjective U ρ S.X₂ n z
      rw [mapCycles_boundary,hFb,map_zero]
    exact ⟨comparisonStep U ρ (schemeFreeOpen V) S hS (n+1) F,
      comparisonStep_surjective U ρ V S hS (n+1) hlocal F hF hmid,
      comparisonStep_boundary U ρ (schemeFreeOpen V) S hS (n+1) F hmid⟩

def sourceIso {A B : X.Modules} (e : A ≅ B) (M : X.Modules) (q : ℕ) :
    ActualExt ρ A M q ≃ₗ[K] ActualExt ρ B M q where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add q)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add q)
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp (show Ext.{1} A M q from x) (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp (show Ext.{1} B M q from x) (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  map_add' x y := Ext.comp_add _ x y _
  map_smul' a x := by
    change (Ext.mk₀ e.inv).comp ((ρ a) • (show Ext.{1} A M q from x)) _ =
      (ρ a) • (Ext.mk₀ e.inv).comp x _
    exact Ext.comp_smul (C := X.Modules) (R := Γ(X, ⊤)) (Ext.mk₀ e.inv) x (zero_add q) (ρ a)

theorem affine_exists_comparison [IsNoetherian X] (hcover : ⊤ ≤ ⨆ i, U i)
    (M : X.Modules) [M.IsQuasicoherent]
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → J), IsAffineOpen (CechHigher.intersection U t))
    (n : ℕ) :
    ∃ F : cycles U ρ M (n+1) →ₗ[K] ActualExt ρ (structureSheaf X) M (n+1),
      Function.Surjective F ∧ ∀ b : Cochain U ρ M n, F (boundaryToCycles U ρ M n b) = 0 := by
  obtain ⟨F,hF,hFb⟩ := exists_comparison U ρ ⊤ (fun _ => le_top) hcover n M
    (fun q t k y => PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
      (CechHigher.intersection U t) (haffine q t) M k y)
  let e := sourceIso (X := X) ρ (A := schemeFreeOpen ⊤) (B := structureSheaf X)
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf) M (n+1)
  refine ⟨e.toLinearMap.comp F, e.surjective.comp hF, ?_⟩
  intro b
  change e (F (boundaryToCycles U ρ M n b)) = 0
  rw [hFb,map_zero]

end
end PiExponent.GeometrySupport.CechExtFinite

end OAI
