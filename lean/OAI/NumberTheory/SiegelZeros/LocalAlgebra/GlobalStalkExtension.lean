import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import OAI.NumberTheory.SiegelZeros.Estimates.GlobalConstants
import OAI.NumberTheory.SiegelZeros.Intersection.NormalIntersection
import OAI.NumberTheory.SiegelZeros.Structure.CanonicalDivisorScalars

namespace OAI

namespace SiegelZeros

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace SiegelZerosAwei.Workers.W15

universe u
variable {X : Scheme.{u}} [IsIntegral X]

instance globalExtension_top_nonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩

lemma germToFunctionField_restrict (U V : X.Opens) [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op s) = X.germToFunctionField V s := by
  exact X.presheaf.germ_res_apply i _ _ s

theorem global_preimage_of_open_cover {ι : Type u} [Nonempty ι]
    (U : ι → X.Opens) [∀ i, Nonempty (U i)] (hcover : ⊤ ≤ iSup U)
    (r : X.functionField)
    (h : ∀ i, ∃ s : Γ(X, U i), X.germToFunctionField (U i) s = r) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = r := by
  classical
  choose s hs using h
  have hg (i : ι) : genericPoint X ∈ U i := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (U i))
    exact ((genericPoint_spec X).mem_open_set_iff (U i).isOpen).mpr
      ⟨x.1, trivial, x.2⟩
  have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro i j
    let nonemptyIntersection : Nonempty (U i ⊓ U j : X.Opens) :=
      ⟨⟨genericPoint X, hg i, hg j⟩⟩
    apply X.germToFunctionField_injective (U i ⊓ U j)
    rw [germToFunctionField_restrict, germToFunctionField_restrict, hs i, hs j]
  obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' U (⊤ : X.Opens)
    (fun _ => homOfLE (fun _ _ => trivial)) hcover s hcompatible
  let i : ι := Classical.choice inferInstance
  refine ⟨g, ?_⟩
  have hgi : X.presheaf.map
      (homOfLE (fun _ _ => trivial) : U i ⟶ (⊤ : X.Opens)).op g = s i := hg i
  rw [← germToFunctionField_restrict (U i) (⊤ : X.Opens)
    (homOfLE (fun _ _ => trivial)) g, hgi, hs i]

end SiegelZerosAwei.Workers.W15

end

section

open CategoryTheory AlgebraicGeometry

namespace SiegelZerosAwei.Workers.W15

universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem affine_integrallyClosed_of_stalks (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let x : X := hU.fromSpec ⟨P, hP.isPrime⟩
  have hx : x ∈ U := (hU.isoSpec.inv ⟨P, hP.isPrime⟩).2
  let stalkAlgebra : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let stalkLocalization : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ hx
  let stalkIntegrallyClosed : IsIntegrallyClosed (X.presheaf.stalk x) := hnormal x
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime P)).toRingEquiv

theorem affine_preimage_of_heightOne [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (r : X.functionField)
    (h : ∀ (P : Ideal Γ(X, U)) [P.IsPrime], P.height = 1 →
      ∃ n d : Γ(X, U), d ∉ P ∧
        r = algebraMap Γ(X, U) X.functionField n *
          (algebraMap Γ(X, U) X.functionField d)⁻¹) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = r := by
  let sectionsNoetherian : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let sectionsIntegrallyClosed : IsIntegrallyClosed Γ(X, U) :=
    affine_integrallyClosed_of_stalks U hU hnormal
  let sectionsFractionRing : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  apply mem_base_of_mem_heightOne_localizations r
  intro P hP hheight
  change ∃ (n d : Γ(X, U)) (_ : d ∈ P.primeCompl),
    r = algebraMap Γ(X, U) X.functionField n *
      (algebraMap Γ(X, U) X.functionField d)⁻¹
  obtain ⟨n, d, hd, heq⟩ := h P hheight
  exact ⟨n, d, hd, heq⟩

theorem global_preimage_of_affine_heightOne [IsLocallyNoetherian X]
    {ι : Type u} [Nonempty ι] (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⊤ ≤ iSup U)
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (r : X.functionField)
    (h : ∀ i (P : Ideal Γ(X, U i)) [P.IsPrime], P.height = 1 →
      ∃ n d : Γ(X, U i), d ∉ P ∧
        r = algebraMap Γ(X, U i) X.functionField n *
          (algebraMap Γ(X, U i) X.functionField d)⁻¹) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = r := by
  apply global_preimage_of_open_cover U hcover r
  intro i
  exact affine_preimage_of_heightOne (U i) (hU i) hnormal r (h i)

end SiegelZerosAwei.Workers.W15

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SiegelZerosAwei.Workers.W15

universe u
variable {X : Scheme.{u}} [IsIntegral X]

local instance stalkExtension_top_nonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩

theorem actualStalk_isFractionRing (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField := inferInstance

theorem affine_fraction_of_dimensionOne_stalks
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (r : X.functionField)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      r ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (P : Ideal Γ(X, U)) [hP : P.IsPrime] (hheight : P.height = 1) :
    ∃ n d : Γ(X, U), d ∉ P ∧
      r = algebraMap Γ(X, U) X.functionField n *
        (algebraMap Γ(X, U) X.functionField d)⁻¹ := by
  let x : X := hU.fromSpec ⟨P, hP⟩
  have hx : x ∈ U := (hU.isoSpec.inv ⟨P, hP⟩).2
  let xU : U := ⟨x, hx⟩
  let stalkAlgebra : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  let stalkLocalization : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
    hU.isLocalization_stalk' ⟨P, hP⟩ hx
  let stalkFunctionFieldTower : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
    functionField_isScalarTower X U xU
  let sectionsFractionRing : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    simpa [hheight] using
      (IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk x))
  obtain ⟨z, hz⟩ := h x hdim
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj P.primeCompl z
  have heq : r * algebraMap Γ(X, U) X.functionField (d : Γ(X, U)) =
      algebraMap Γ(X, U) X.functionField n := by
    have heq := congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hnd
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply, hz] using heq
  have hd0 : algebraMap Γ(X, U) X.functionField (d : Γ(X, U)) ≠ 0 := by
    exact IsFractionRing.to_map_eq_zero_iff.not.mpr (fun hd => d.2 (hd ▸ P.zero_mem))
  refine ⟨n, d, d.2, ?_⟩
  simpa only [div_eq_mul_inv] using (eq_div_iff hd0).2 heq

theorem global_preimage_of_dimensionOne_stalks [IsLocallyNoetherian X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (r : X.functionField)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      r ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = r := by
  let U : X → X.Opens := fun x => (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU (x : X) : IsAffineOpen (U x) := isAffineOpen_opensRange _
  have hx (x : X) : x ∈ U x := X.affineCover.covers x
  let nonemptyChart (x : X) : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply global_preimage_of_affine_heightOne U hU hcover hnormal r
  intro x P hP hheight
  exact affine_fraction_of_dimensionOne_stalks (U x) (hU x) r h P hheight

variable {k : Type u} [Field k]

theorem schemeScalarTower_stalk_functionField
    (s : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    letI := schemeStalkAlgebra s x
    letI := schemeFunctionFieldAlgebra s
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let stalkAlgebra := schemeStalkAlgebra s x
  let functionFieldAlgebra := schemeFunctionFieldAlgebra s
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change scalarToStalk s (genericPoint X) c =
    (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
      (scalarToStalk s x c)
  symm
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop ≫
    X.presheaf.germ ⊤ x (Opens.mem_top x) ≫
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom c = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  rfl

theorem scalarToFunctionField_constantSection [IsAlgClosed k]
    (s : X ⟶ Spec (CommRingCat.of k)) (c : k) :
    X.germToFunctionField ⊤ (constantSectionMap s c) =
      scalarToStalk s (genericPoint X) c := rfl

end SiegelZerosAwei.Workers.W15

end

end SiegelZeros

end OAI
