import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.DerivedSums
import OAI.Algebra.FinitisticAsymmetry.Derived.LocalizingRetracts

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u w
variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

omit [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_shortExact₁ (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    (h₂ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₂))
    (h₃ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    P ((DerivedCategory.singleFunctor _ 0).obj S.X₁) := by
  let := hS.mono_f
  let := hS.epi_g
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  apply P.prop_of_iso (e.app S.X₁).symm
  exact P.ext_of_isTriangulatedClosed₁ _
    (DerivedCategory.triangleOfSES_distinguished (hS.map F))
    (P.prop_of_iso (e.app S.X₂) h₂) (P.prop_of_iso (e.app S.X₃) h₃)

omit [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_shortExact₂ (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    (h₁ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₁))
    (h₃ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    P ((DerivedCategory.singleFunctor _ 0).obj S.X₂) := by
  let := hS.mono_f
  let := hS.epi_g
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  apply P.prop_of_iso (e.app S.X₂).symm
  exact P.ext_of_isTriangulatedClosed₂ _
    (DerivedCategory.triangleOfSES_distinguished (hS.map F))
    (P.prop_of_iso (e.app S.X₁) h₁) (P.prop_of_iso (e.app S.X₃) h₃)

omit [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_of_cofan {I : Type u} [P.IsClosedUnderColimitsOfShape (Discrete I)]
    {M : I → ModuleCat R} (s : Cofan M) (hs : IsColimit s)
    (hM : ∀ i, P ((DerivedCategory.singleFunctor _ 0).obj (M i))) :
    P ((DerivedCategory.singleFunctor _ 0).obj s.pt) := by
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  have hs' := isColimitCofanMkObjOfIsColimit F M s.inj hs
  apply P.prop_of_iso (e.app s.pt).symm
  exact P.prop_of_isColimit (derivedCofanIsColimit _ hs')
    (fun i => P.prop_of_iso (e.app (M i.as)) (hM i.as))

variable {S : Type u} [Ring S] (χ : R →+* S)
variable (hcop : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
include hcop

lemma prop_restricted_projective (M : ModuleCat.{u} S) [Module.Projective S M]
    (hS : P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars χ).obj (ModuleCat.of S S)))) :
    P ((DerivedCategory.singleFunctor _ 0).obj ((ModuleCat.restrictScalars χ).obj M)) := by
  classical
  let F := ModuleCat.restrictScalars χ ⋙ DerivedCategory.singleFunctor (ModuleCat R) 0
  let := hcop M
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := S) (P := M)).mp inferInstance
  let q : ModuleCat.of S (M →₀ S) ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination S id)
  let j : M ⟶ ModuleCat.of S (M →₀ S) := ModuleCat.ofHom s
  have hjq : j ≫ q = 𝟙 _ := by ext x; exact congrFun (congrArg DFunLike.coe hs) x
  apply localizing_of_retract (F.map j) (F.map q) (by rw [← F.map_comp, hjq, F.map_id]) P
  let cs : Cofan (fun _ : M => ModuleCat.of S S) :=
    Cofan.mk (ModuleCat.of S (M →₀ S)) (fun x => ModuleCat.ofHom (Finsupp.lsingle x))
  have hc : IsColimit cs := by
    refine Cofan.IsColimit.mk _
      (fun t => ModuleCat.ofHom (Finsupp.lsum ℤ (fun x => (t.inj x).hom))) ?_ ?_
    · intro t x
      ext
      simp [cs]
    · intro t f hf
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro x
      simpa [cs] using congrArg ModuleCat.Hom.hom (hf x)
  let G := ModuleCat.restrictScalars χ
  exact prop_single_of_cofan P (Cofan.mk (G.obj cs.pt) (fun x => G.map (cs.inj x)))
    (isColimitCofanMkObjOfIsColimit G _ cs.inj hc) (fun _ => hS)

omit hcop [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
lemma submodule_shortExact (M : ModuleCat.{u} R) (N : Submodule R M) :
    (ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
      (by ext x; exact (Submodule.Quotient.mk_eq_zero N).mpr x.property)).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr N.injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero N).mp hx⟩, rfl⟩

variable (J : Ideal R) [J.IsTwoSided] [IsSemisimpleRing (R ⧸ J)]

lemma prop_annihilated_module
    (hQ : P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of (R ⧸ J) (R ⧸ J)))))
    (M : ModuleCat.{u} R) (hM : Module.IsTorsionBySet R M J) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := hM.module
  let M' := ModuleCat.of (R ⧸ J) M
  let : Module.Projective (R ⧸ J) M' := Module.projective_of_isSemisimpleRing _ _
  have h := prop_restricted_projective P (Ideal.Quotient.mk J) hcop M' hQ
  let e : ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj M') ≅ M :=
    LinearEquiv.toModuleIso {
      toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => hM.mk_smul r x }
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e) h

lemma prop_of_nilpotent_kernel
    (hQ : P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of (R ⧸ J) (R ⧸ J)))))
    (hJ : ∃ n : ℕ, J ^ n = ⊥) (M : ModuleCat.{u} R) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have aux (n : ℕ) (M : ModuleCat.{u} R) (hn : J^n • (⊤ : Submodule R M) = ⊥) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    induction n generalizing M with
    | zero =>
      have hm : (⊤ : Submodule R M) = ⊥ := by
        simpa only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul] using hn
      apply P.prop_of_isZero
      apply (DerivedCategory.singleFunctor _ 0).map_isZero
      rw [ModuleCat.isZero_iff_subsingleton]
      exact (Submodule.subsingleton_iff R).mp (subsingleton_of_bot_eq_top hm.symm)
    | succ n ih =>
      let N : Submodule R M := J • ⊤
      have hn' : J^n • (⊤ : Submodule R N) = ⊥ := by
        apply Submodule.map_injective_of_injective N.injective_subtype
        rw [Submodule.map_bot, Submodule.map_smul'', Submodule.map_subtype_top]
        change J^n • (J • (⊤ : Submodule R M)) = ⊥
        rw [← Submodule.mul_smul, ← Submodule.pow_succ]
        exact hn
      apply prop_single_shortExact₂ P _ (submodule_shortExact M N)
      · exact ih (ModuleCat.of R N) hn'
      · exact prop_annihilated_module P hcop J hQ (ModuleCat.of R (M ⧸ N))
          (Module.isTorsionBySet_quotient_ideal_smul M J)
  obtain ⟨n, hn⟩ := hJ
  exact aux n M (by simp [hn])

variable {k ι : Type u} [Field k] [Fintype ι] (ψ : R →+* (ι → k))

abbrev coordinateModule (j : ι) : ModuleCat R :=
  (ModuleCat.restrictScalars ((Pi.evalRingHom (fun _ : ι => k) j).comp ψ)).obj
    (ModuleCat.of k k)

omit [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_restricted_pi
    (hcoord : ∀ j, P ((DerivedCategory.singleFunctor _ 0).obj (coordinateModule ψ j))) :
    P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k)))) := by
  classical
  let := hcop ι
  let Z := coordinateModule ψ
  have h := prop_single_of_cofan P (ModuleCat.coproductCocone Z)
    (ModuleCat.coproductCoconeIsColimit Z) hcoord
  let e₁ : (Π₀ i, Z i) ≃ₗ[R] (∀ i, Z i) := DFinsupp.linearEquivFunOnFintype
  let e₂ : (∀ i, Z i) ≃ₗ[R]
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k))) := {
    toFun := fun x i => x i
    invFun := fun x i => x i
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    ((e₁.trans e₂).toModuleIso)) h

lemma prop_all_of_product_augmentation (hψ : Function.Surjective ψ)
    (hnil : ∃ n : ℕ, (RingHom.ker ψ)^n = ⊥)
    (hcoord : ∀ j, P ((DerivedCategory.singleFunctor _ 0).obj (coordinateModule ψ j)))
    (M : ModuleCat.{u} R) : P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let e := RingHom.quotientKerEquivOfSurjective hψ
  let : IsSemisimpleRing (R ⧸ RingHom.ker ψ) := e.isSemisimpleRing_iff.mpr inferInstance
  apply prop_of_nilpotent_kernel P hcop (RingHom.ker ψ) _ hnil M
  let e' : ((ModuleCat.restrictScalars (Ideal.Quotient.mk (RingHom.ker ψ))).obj
      (ModuleCat.of (R ⧸ RingHom.ker ψ) (R ⧸ RingHom.ker ψ))) ≅
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k))) :=
    LinearEquiv.toModuleIso (show
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (RingHom.ker ψ))).obj
        (ModuleCat.of (R ⧸ RingHom.ker ψ) (R ⧸ RingHom.ker ψ))) ≃ₗ[R]
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k))) from {
      toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun r x => by
        change e (Ideal.Quotient.mk (RingHom.ker ψ) r * (show R ⧸ RingHom.ker ψ from x)) = ψ r * e x
        rw [e.map_mul]
        rfl })
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e'.symm)
    (prop_restricted_pi P hcop ψ hcoord)

end LittleFinitistic.DerivedSupport

end

end OAI
