import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Smooth.Field
import OAI.NumberTheory.SiegelZeros.Intersection.DivisorSmoothness

namespace OAI

namespace SiegelZeros

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SiegelZerosAwei.Workers.W15

universe u
variable {k : Type u} [Field k]
variable {X Y P : Scheme.{u}}

noncomputable def scalarToStalk (s : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    k →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop ≫
    X.presheaf.germ ⊤ x trivial).hom

@[reducible] noncomputable def schemeStalkAlgebra (s : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  (scalarToStalk s x).toAlgebra

noncomputable abbrev schemeFunctionFieldAlgebra [IsIntegral X]
    (s : X ⟶ Spec (CommRingCat.of k)) : Algebra k X.functionField :=
  schemeStalkAlgebra s (genericPoint X)

@[simp] theorem scalarToStalk_stalkCongr (s : X ⟶ Spec (CommRingCat.of k))
    {x y : X} (h : x = y) (c : k) :
    (X.presheaf.stalkCongr (.of_eq h)).hom (scalarToStalk s x c) =
      scalarToStalk s y c := by
  subst y
  simp [TopCat.Presheaf.stalkCongr_hom]

@[simp] theorem scalarToStalk_stalkMap (f : X ⟶ Y)
    (s : Y ⟶ Spec (CommRingCat.of k)) (x : X) (c : k) :
    f.stalkMap x (scalarToStalk s (f x) c) = scalarToStalk (f ≫ s) x c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop ≫
    Y.presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x).hom c = _
  erw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
  simp only [scalarToStalk, Scheme.Hom.comp_appTop, Category.assoc]
  rfl

theorem scalarToStalk_stalkClosedPointTo {K : Type u} [Field K]
    (f : Spec (CommRingCat.of K) ⟶ X)
    (s : X ⟶ Spec (CommRingCat.of k)) (c : k) :
    Scheme.stalkClosedPointTo f
        (scalarToStalk s (f (IsLocalRing.closedPoint (CommRingCat.of K))) c) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f ≫ s).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom c := by
  change (stalkClosedPointIso (CommRingCat.of K)).hom
    (f.stalkMap _ (scalarToStalk s _ c)) = _
  erw [scalarToStalk_stalkMap f s (IsLocalRing.closedPoint (CommRingCat.of K)) c]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f ≫ s).appTop ≫
    (Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial ≫
      (stalkClosedPointIso (CommRingCat.of K)).hom).hom c = _
  erw [germ_stalkClosedPointIso_hom (CommRingCat.of K)]

theorem genericPointMorphism_scalars [IsIntegral X] [QuasiSeparatedSpace X]
    (s : X ⟶ Spec (CommRingCat.of k)) (c : k) :
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (genericPointMorphism X ≫ s).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom).hom c =
      scalarToStalk s (genericPoint X) c := by
  rw [← scalarToStalk_stalkClosedPointTo]
  change Scheme.stalkClosedPointTo (X.fromSpecStalk (genericPoint X))
    (scalarToStalk s _ c) = _
  rw [Scheme.stalkClosedPointTo_fromSpecStalk]
  exact scalarToStalk_stalkCongr s
    (Scheme.fromSpecStalk_closedPoint (X := X) (x := genericPoint X)) c

theorem genericNormalizationFunctionFieldEquiv_scalars
    [IsIntegral X] [QuasiSeparatedSpace X]
    (s : X ⟶ Spec (CommRingCat.of k)) (c : k) :
    genericNormalizationFunctionFieldEquiv X
      (scalarToStalk (genericNormalizationMap X ≫ s)
        (genericPoint (GenericNormalization X)) c) =
      scalarToStalk s (genericPoint X) c := by
  change Scheme.stalkClosedPointTo (genericPointMorphism X).toNormalization
    (((GenericNormalization X).presheaf.stalkCongr
      (.of_eq (toGenericNormalization_closedPoint X).symm)).hom
        (scalarToStalk _ _ c)) = _
  rw [scalarToStalk_stalkCongr (genericNormalizationMap X ≫ s)
    (toGenericNormalization_closedPoint X).symm c, scalarToStalk_stalkClosedPointTo]
  simpa only [genericNormalizationMap, ← Category.assoc,
    Scheme.Hom.toNormalization_fromNormalization] using genericPointMorphism_scalars s c

noncomputable def genericNormalizationFunctionFieldAlgEquiv
    [IsIntegral X] [QuasiSeparatedSpace X] (s : X ⟶ Spec (CommRingCat.of k)) :
    letI := schemeFunctionFieldAlgebra (genericNormalizationMap X ≫ s)
    letI := schemeFunctionFieldAlgebra s
    (GenericNormalization X).functionField ≃ₐ[k] X.functionField := by
  letI := schemeFunctionFieldAlgebra (genericNormalizationMap X ≫ s)
  letI := schemeFunctionFieldAlgebra s
  exact { genericNormalizationFunctionFieldEquiv X with
    commutes' := genericNormalizationFunctionFieldEquiv_scalars s }

theorem imageFunctionFieldEquiv_scalars (j : X ⟶ P) [QuasiCompact j]
    [IsIntegral X] [IsImmersion j] (s : P ⟶ Spec (CommRingCat.of k)) (c : k) :
    imageFunctionFieldEquiv j
      (scalarToStalk (j.imageι ≫ s) (genericPoint j.image) c) =
      scalarToStalk (j ≫ s) (genericPoint X) c := by
  change j.toImage.stalkMap (genericPoint X)
    ((j.image.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion j.toImage).symm)).hom
        (scalarToStalk _ _ c)) = _
  rw [scalarToStalk_stalkCongr (j.imageι ≫ s)
    (genericPoint_eq_of_isOpenImmersion j.toImage).symm c, scalarToStalk_stalkMap]
  simp only [← Category.assoc, Scheme.Hom.toImage_imageι]

noncomputable def imageFunctionFieldAlgEquiv (j : X ⟶ P) [QuasiCompact j]
    [IsIntegral X] [IsImmersion j] (s : P ⟶ Spec (CommRingCat.of k)) :
    letI := schemeFunctionFieldAlgebra (j.imageι ≫ s)
    letI := schemeFunctionFieldAlgebra (j ≫ s)
    j.image.functionField ≃ₐ[k] X.functionField := by
  letI := schemeFunctionFieldAlgebra (j.imageι ≫ s)
  letI := schemeFunctionFieldAlgebra (j ≫ s)
  exact { imageFunctionFieldEquiv j with commutes' := imageFunctionFieldEquiv_scalars j s }

section AffineScalars

noncomputable local instance affineSpecStalkAlgebra (R : Type u) [CommRing R]
    (x : Spec (CommRingCat.of R)) :
    Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra R x

theorem affine_scalarToStalk (R : Type u) [CommRing R] [Algebra k R]
    (x : Spec (CommRingCat.of R)) (c : k) :
    scalarToStalk (Spec.map (CommRingCat.ofHom (algebraMap k R))) x c =
      algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk x) (algebraMap k R c) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
      (Spec (CommRingCat.of R)).presheaf.germ ⊤ x trivial).hom c = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

end AffineScalars

open SiegelZeros.W17.ProjectiveChart
variable (p : Ideal (SiegelZeros.W58.TorusRing ℂ)) [p.IsPrime]

omit [p.IsPrime] in
theorem torusSubvarietyEmbedding_toBase :
    torusSubvarietyEmbedding p ≫ projectiveToBase =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (TorusSubvarietyRing ℂ p))) := by
  simp only [torusSubvarietyEmbedding, Category.assoc, affineChartEmbedding_toBase]
  dsimp only [torusAffineEmbedding]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

@[reducible] noncomputable def torusFunctionFieldAlgebra :
    Algebra ℂ (TorusSubvariety ℂ p).functionField :=
  ((algebraMap (TorusSubvarietyRing ℂ p) (TorusSubvariety ℂ p).functionField).comp
    (algebraMap ℂ (TorusSubvarietyRing ℂ p))).toAlgebra

@[reducible] noncomputable def compactifiedFunctionFieldAlgebra :
    Algebra ℂ (NormalizedProjectiveTorus p).functionField :=
  schemeFunctionFieldAlgebra (normalizedProjectiveTorusToBase p)

theorem normalizedProjectiveTorusFunctionFieldEquiv_scalars (c : ℂ) :
    normalizedProjectiveTorusFunctionFieldEquiv p
      (scalarToStalk (normalizedProjectiveTorusToBase p)
        (genericPoint (NormalizedProjectiveTorus p)) c) =
      algebraMap (TorusSubvarietyRing ℂ p) (TorusSubvariety ℂ p).functionField
        (algebraMap ℂ (TorusSubvarietyRing ℂ p) c) := by
  change torusProjectiveClosureFunctionFieldEquiv p
    (genericNormalizationFunctionFieldEquiv (TorusProjectiveClosure p)
      (scalarToStalk (genericNormalizationMap (TorusProjectiveClosure p) ≫
        torusProjectiveClosureToBase p) _ c)) = _
  rw [genericNormalizationFunctionFieldEquiv_scalars]
  change imageFunctionFieldEquiv (torusSubvarietyEmbedding p)
    (scalarToStalk ((torusSubvarietyEmbedding p).imageι ≫ projectiveToBase) _ c) = _
  rw [imageFunctionFieldEquiv_scalars, torusSubvarietyEmbedding_toBase]
  exact affine_scalarToStalk (TorusSubvarietyRing ℂ p) _ c

noncomputable def normalizedProjectiveTorusFunctionFieldAlgEquiv :
    letI := compactifiedFunctionFieldAlgebra p
    letI := torusFunctionFieldAlgebra p
    (NormalizedProjectiveTorus p).functionField ≃ₐ[ℂ]
      (TorusSubvariety ℂ p).functionField := by
  letI := compactifiedFunctionFieldAlgebra p
  letI := torusFunctionFieldAlgebra p
  exact { normalizedProjectiveTorusFunctionFieldEquiv p with
    commutes' := normalizedProjectiveTorusFunctionFieldEquiv_scalars p }

theorem normalizedProjectiveTorusFunctionFieldAlgEquiv_coordinate (i : Fin 4) :
    letI := compactifiedFunctionFieldAlgebra p
    letI := torusFunctionFieldAlgebra p
    normalizedProjectiveTorusFunctionFieldAlgEquiv p (compactifiedTorusCoordinate p i) =
      torusCoordinateFunction ℂ p i := by
  let := compactifiedFunctionFieldAlgebra p
  let := torusFunctionFieldAlgebra p
  change normalizedProjectiveTorusFunctionFieldEquiv p (compactifiedTorusCoordinate p i) =
    torusCoordinateFunction ℂ p i
  exact compactifiedTorusCoordinate_identification p i

theorem scalarToStalk_via_chart (s : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) (x : X) (hx : x ∈ U) (c : k) :
    X.presheaf.germ U x hx
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U (by simp)).hom c) =
        scalarToStalk s x c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ U (by simp) ≫
    X.presheaf.germ U x hx).hom c = _
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res, scalarToStalk]
  rfl

end SiegelZerosAwei.Workers.W15

end

end SiegelZeros

section

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace SiegelZeros.W58
open SiegelZerosAwei.Workers.W15

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

noncomputable local instance canonicalSpecStalkAlgebra
    (y : Spec (CommRingCat.of k)) :
    Algebra k ((Spec (CommRingCat.of k)).presheaf.stalk y) :=
  StructureSheaf.stalkAlgebra k y

noncomputable local instance canonicalSpecStalkLocalization
    (y : Spec (CommRingCat.of k)) :
    IsLocalization.AtPrime (hp := y.isPrime)
      ((Spec (CommRingCat.of k)).presheaf.stalk y) y.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk k y

theorem scalarToStalk_base_identity (y : Spec (CommRingCat.of k)) :
    scalarToStalk (𝟙 (Spec (CommRingCat.of k))) y =
      algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk y) := by
  ext c
  simpa using (affine_scalarToStalk (k := k) k y c)

theorem scalarToStalk_structural_factorization
    (s : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    ((s.stalkMap x).hom).comp
      (scalarToStalk (𝟙 (Spec (CommRingCat.of k))) (s x)) = scalarToStalk s x := by
  ext c
  simp

theorem canonical_schemeStalk_essFiniteType
    (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] (x : X) :
    letI := schemeStalkAlgebra s x
    Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  change (scalarToStalk s x).EssFiniteType
  rw [← scalarToStalk_structural_factorization s x]
  have hbase : (scalarToStalk (𝟙 (Spec (CommRingCat.of k))) (s x)).EssFiniteType := by
    rw [scalarToStalk_base_identity, RingHom.essFiniteType_algebraMap
      (R := k) (S := (Spec (CommRingCat.of k)).presheaf.stalk (s x))]
    exact Algebra.EssFiniteType.of_isLocalization
      ((Spec (CommRingCat.of k)).presheaf.stalk (s x))
      ((s x).asIdeal.primeCompl (hp := (s x).isPrime))
  exact hbase.comp (LocallyOfFiniteType.stalkMap s x)

theorem canonical_schemeStalk_residue_formallySmooth [PerfectField k]
    (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] (x : X) :
    letI := schemeStalkAlgebra s x
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  let := schemeStalkAlgebra s x
  let := canonical_schemeStalk_essFiniteType s x
  let : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)))
      IsLocalRing.residue_surjective
  exact Algebra.FormallySmooth.of_perfectField

variable (p : Ideal (TorusRing ℂ)) [p.IsPrime]

theorem projective_divisor_stalk_essFiniteType (x : NormalizedProjectiveTorus p) :
    letI := schemeStalkAlgebra (normalizedProjectiveTorusToBase p) x
    Algebra.EssFiniteType ℂ ((NormalizedProjectiveTorus p).presheaf.stalk x) :=
  canonical_schemeStalk_essFiniteType (normalizedProjectiveTorusToBase p) x

theorem projective_divisor_residue_formallySmooth (x : NormalizedProjectiveTorus p) :
    letI := schemeStalkAlgebra (normalizedProjectiveTorusToBase p) x
    Algebra.FormallySmooth ℂ (IsLocalRing.ResidueField ((NormalizedProjectiveTorus p).presheaf.stalk x)) :=
  canonical_schemeStalk_residue_formallySmooth (normalizedProjectiveTorusToBase p) x

end SiegelZeros.W58

end

end

end OAI
