import OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDegree

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def LowCohomologyFinite (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) : Prop :=
  ∀ n ≤ 1, letI := Module.compHom (cohomology M n) (baseScalars p)
    FiniteDimensional ℂ (cohomology M n)

theorem lowCohomologyFinite_of_iso (p : X ⟶ Spec (.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (h : LowCohomologyFinite p N) :
    LowCohomologyFinite p M := by
  intro n hn
  let := Module.compHom (cohomology M n) (baseScalars p)
  let := Module.compHom (cohomology N n) (baseScalars p)
  let := h n hn
  exact Module.Finite.of_surjective (cohomologyIso p e n).symm.toLinearMap
    (cohomologyIso p e n).symm.surjective

theorem finite_support_positive_cohomology (M : X.Modules)
    (S : Set X) (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (n : ℕ) :
    Subsingleton (cohomology M (n+1)) := by
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
    PiExponentSeshadri.FiniteSupport.finite_closed_support_flasque _ S hfin hclosed hsupp
  exact ⟨fun x y =>
    (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n M x).trans
      (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n M y).symm⟩

private theorem finite_middle {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

theorem finite_supported_quotient (p : X ⟶ Spec (.of ℂ))
    (T : ShortComplex X.Modules) (hT : T.ShortExact)
    (h₁ : LowCohomologyFinite p T.X₁) (h₂ : LowCohomologyFinite p T.X₂)
    (S : Set X) (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (T.X₃.presheaf.stalk x)) :
    LowCohomologyFinite p T.X₃ := by
  intro n hn
  let := Module.compHom (cohomology T.X₃ n) (baseScalars p)
  cases n with
  | succ n =>
      let := finite_support_positive_cohomology T.X₃ S hfin hclosed hsupp n
      infer_instance
  | zero =>
      let := sheafComplexLinear p
      let : Module.Finite ℂ (Ext (structureSheaf X) T.X₂ 0) := by
        change @Module.Finite ℂ (cohomology T.X₂ 0) _ _ (complexExtModule p T.X₂ 0)
        rw [complexExtModule_eq]
        exact h₂ 0 (by omega)
      let : Module.Finite ℂ (Ext (structureSheaf X) T.X₁ (0+1)) := by
        change @Module.Finite ℂ (cohomology T.X₁ 1) _ _ (complexExtModule p T.X₁ 1)
        rw [complexExtModule_eq]
        exact h₁ 1 le_rfl
      have he := finite_middle
        (PiExponentSeshadri.Cohomology.cohomologyMap₂ (K := ℂ) (structureSheaf X) (S := T) 0)
        (PiExponentSeshadri.Cohomology.cohomologyBoundary (K := ℂ) (structureSheaf X) hT 0)
        (PiExponentSeshadri.Cohomology.cohomology_exact₃ (K := ℂ) (structureSheaf X) hT 0)
      change @Module.Finite ℂ (cohomology T.X₃ 0) _ _ (complexExtModule p T.X₃ 0) at he
      rw [complexExtModule_eq] at he
      exact he

theorem generic_extension_tensor_euler [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (B : X.Modules) (u : structureSheaf X ⟶ B) [Mono u]
    (hu : isoOpen u ≠ ⊥) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hB : LowCohomologyFinite p B) (hL : LowCohomologyFinite p L.sheaf)
    (hBL : LowCohomologyFinite p (moduleTensor X B L.sheaf))
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic p 1 (moduleTensor X B L.sheaf) - eulerCharacteristic p 1 B =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let T := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel T (cokernelIsCokernel u) }
  let TL := T.map (moduleTensorRightFunctor L.sheaf)
  have hTL : TL.ShortExact := moduleTensorRightFunctor_shortExact L T hT
  let S : Set X := (isoOpen u : Set X)ᶜ
  obtain ⟨hfin,hclosed⟩ := finite_closed_complement hd (isoOpen u) hu
  have hsupp (x : X) (hx : x ∉ S) : Subsingleton ((cokernel u).presheaf.stalk x) :=
    cokernel_stalk_subsingleton u x (not_not.mp hx)
  have hsuppt (x : X) (hx : x ∉ S) :
      Subsingleton ((moduleTensor X (cokernel u) L.sheaf).presheaf.stalk x) := by
    let := hsupp x hx
    exact tensor_stalk_subsingleton _ L x
  have hOL := lowCohomologyFinite_of_iso p (moduleTensorUnit L.sheaf) hL
  have hQ := finite_supported_quotient p T hT hO hB S hfin hclosed hsupp
  have hQL := finite_supported_quotient p TL hTL hOL hBL S hfin hclosed hsuppt
  let : Subsingleton (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2) := by
    let := Module.compHom (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2) (baseScalars p)
    let := Module.compHom (cohomology L.sheaf 2) (baseScalars p)
    exact (cohomologyIso p (moduleTensorUnit L.sheaf) 2).injective.subsingleton
  let : Subsingleton (cohomology TL.X₁ (1+1)) := by
    change Subsingleton (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2)
    infer_instance
  have h₀ := eulerCharacteristic_add p hT 1 hO hB hQ
  have h₁ := eulerCharacteristic_add p hTL 1 hOL hBL hQL
  change eulerCharacteristic p 1 B = eulerCharacteristic p 1 (structureSheaf X) +
    eulerCharacteristic p 1 (cokernel u) at h₀
  change eulerCharacteristic p 1 (moduleTensor X B L.sheaf) =
    eulerCharacteristic p 1 (moduleTensor X (structureSheaf X) L.sheaf) +
    eulerCharacteristic p 1 (moduleTensor X (cokernel u) L.sheaf) at h₁
  rw [eulerCharacteristic_iso p (moduleTensorUnit L.sheaf),
    cokernel_tensor_euler p hd u hu L 1] at h₁
  omega

end PiExponent.CurveNormalizationDegree

end

end OAI
