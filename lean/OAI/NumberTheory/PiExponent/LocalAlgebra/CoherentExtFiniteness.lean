import OAI.NumberTheory.PiExponent.Cohomology.EulerExact
import OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing

namespace OAI

namespace PiExponent.CoherentExtFiniteness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

theorem finite_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

universe w v u t k
variable {K : Type k} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear K C] [HasExt.{w} C]

def extLinearEquivBiproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ) :
    Ext.{w} A c.pt q ≃ₗ[K] ∀ j, Ext.{w} A (B j) q :=
  { Ext.addEquivBiproduct A hc q with
    map_smul' := by
      intro a x
      funext j
      exact Ext.smul_comp x (Ext.mk₀ (c.π j)) (add_zero q) a }

theorem ext_finite_of_biproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hfinite : ∀ j, Module.Finite K (Ext.{w} A (B j) q)) :
    Module.Finite K (Ext.{w} A c.pt q) := by
  let (j : J) : Module.Finite K (Ext.{w} A (B j) q) := hfinite j
  exact Module.Finite.of_surjective (extLinearEquivBiproduct (K := K) A hc q).symm.toLinearMap
    (extLinearEquivBiproduct (K := K) A hc q).symm.surjective

structure FiniteCohomologyPresentation {ι : Type t} (A : C) (F : ι → C) (i : ι) where
  kernel : ι
  middle : C
  left : F kernel ⟶ middle
  right : middle ⟶ F i
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  finite : ∀ q, Module.Finite K (Ext.{w} A middle q)

theorem ext_finite_of_presentations {ι : Type t} (A : C) (F : ι → C) (l : ℕ)
    (hbound : ∀ i q, l ≤ q → ∀ x : Ext.{w} A (F i) q, x = 0)
    (presentation : ∀ i, FiniteCohomologyPresentation (K := K) A F i)
    (i : ι) (q : ℕ) : Module.Finite K (Ext.{w} A (F i) q) := by
  have hdown : ∀ k q, l ≤ q + k → ∀ i, Module.Finite K (Ext.{w} A (F i) q) := by
    intro k
    induction k with
    | zero =>
      intro q hq i
      let : Subsingleton (Ext.{w} A (F i) q) :=
        ⟨fun x y => (hbound i q (by omega) x).trans (hbound i q (by omega) y).symm⟩
      infer_instance
    | succ k ih =>
      intro q hq i
      let P := presentation i
      let S := ShortComplex.mk P.left P.right P.comp_zero
      let : Module.Finite K (Ext.{w} A S.X₂ q) := P.finite q
      let : Module.Finite K (Ext.{w} A S.X₁ (q+1)) := ih (q+1) (by omega) P.kernel
      exact finite_middle_of_exact
        (PiExponentSeshadri.Cohomology.cohomologyMap₂ (K := K) A (S := S) q)
        (PiExponentSeshadri.Cohomology.cohomologyBoundary (K := K) A P.shortExact q)
        (PiExponentSeshadri.Cohomology.cohomology_exact₃ (K := K) A P.shortExact q)
  exact hdown l q (Nat.le_add_left _ _) i

variable {X : Scheme.{0}}

theorem cohomology_finite_of_biproduct
    (p : X ⟶ Spec (CommRingCat.of ℂ)) {J : Type*} [Fintype J]
    {B : J → X.Modules} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hfinite : ∀ j, letI := Module.compHom (cohomology (B j) q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (B j) q)) :
    letI := Module.compHom (cohomology c.pt q) (baseScalars p)
    FiniteDimensional ℂ (cohomology c.pt q) := by
  let := sheafComplexLinear p
  have hfin : ∀ j, Module.Finite ℂ (Ext.{1} (structureSheaf X) (B j) q) := by
    intro j
    change @Module.Finite ℂ (cohomology (B j) q) _ _ (complexExtModule p (B j) q)
    rw [complexExtModule_eq]
    exact hfinite j
  have hf := ext_finite_of_biproduct (K := ℂ) (structureSheaf X) hc q hfin
  change @Module.Finite ℂ (cohomology c.pt q) _ _ (complexExtModule p c.pt q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

structure CoherentFinitePresentation (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) where
  kernel : X.Modules
  kernel_coherent : kernel.IsFinitePresentation
  middle : X.Modules
  left : kernel ⟶ middle
  right : middle ⟶ M
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  middle_finite : ∀ q, letI := Module.compHom (cohomology middle q) (baseScalars p)
    FiniteDimensional ℂ (cohomology middle q)

theorem coherent_cohomology_finite_of_presentations
    [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (l : ℕ) (hl : 0 < l) (U : Fin l → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (presentation : ∀ (M : X.Modules) [M.IsFinitePresentation],
      Nonempty (CoherentFinitePresentation p M))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  let := sheafComplexLinear p
  let F : {N : X.Modules // N.IsFinitePresentation} → X.Modules := Subtype.val
  let P (i : {N : X.Modules // N.IsFinitePresentation}) :
      FiniteCohomologyPresentation (K := ℂ) (structureSheaf X) F i := by
    letI : i.val.IsFinitePresentation := i.property
    let S := Classical.choice (presentation i.val)
    exact
      { kernel := ⟨S.kernel, S.kernel_coherent⟩
        middle := S.middle
        left := S.left
        right := S.right
        comp_zero := S.comp_zero
        shortExact := S.shortExact
        finite := fun n => by
          change @Module.Finite ℂ (cohomology S.middle n) _ _ (complexExtModule p S.middle n)
          rw [complexExtModule_eq]
          exact S.middle_finite n }
  have hbound : ∀ i n, l ≤ n → ∀ x : Ext.{1} (structureSheaf X) (F i) n, x = 0 := by
    intro i n hn x
    let : i.val.IsFinitePresentation := i.property
    let : i.val.IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData i.val).choose.isQuasicoherent
    exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover i.val n hn x
  have hf := ext_finite_of_presentations (K := ℂ) (structureSheaf X) F l hbound P
    ⟨M, inferInstance⟩ q
  change @Module.Finite ℂ (cohomology M q) _ _ (complexExtModule p M q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

end
end PiExponent.CoherentExtFiniteness

end OAI
