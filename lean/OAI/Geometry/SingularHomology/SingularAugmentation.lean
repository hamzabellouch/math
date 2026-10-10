import OAI.Geometry.SingularHomology.HomologyCycle
import OAI.Geometry.SingularHomology.HomologyZero

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Problem340

def realSingularZeroClass (X : Type) [TopologicalSpace X] :
    (realSingularChainComplex X).X 0 →ₗ[ℝ] RealSingularHomology 0 X :=
  (((realSingularChainComplex X).liftCycles (𝟙 _) 0 (by simp) (by simp)) ≫
    (realSingularChainComplex X).homologyπ 0).hom

theorem realSingularZeroClass_eq_moduleHomologyClass
    (X : Type) [TopologicalSpace X] (z : (realSingularChainComplex X).X 0) :
    realSingularZeroClass X z =
      moduleHomologyClass ((realSingularChainComplex X).sc 0) z (by
        change ((realSingularChainComplex X).d 0 ((ComplexShape.down ℕ).next 0)).hom z = 0
        rw [ChainComplex.next_nat_zero, HomologicalComplex.shape _ 0 0 (by simp)]
        rfl) := by
  let C := realSingularChainComplex X
  erw [moduleHomologyClass_eq_pi]
  change (C.homologyπ 0).hom ((C.liftCycles (𝟙 _) 0 (by simp) (by simp)).hom z) = _
  apply congrArg (C.homologyπ 0).hom
  apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
  have h := congrArg (fun k : C.X 0 ⟶ C.X 0 => k.hom z)
    (C.liftCycles_i (𝟙 _) 0 (by simp) (by simp))
  change (C.iCycles 0).hom _ = (C.iCycles 0).hom _
  exact h.trans (((C.sc 0).moduleCatCyclesIso_inv_iCycles_apply
      ⟨z, by
        change (C.d 0 ((ComplexShape.down ℕ).next 0)).hom z = 0
        rw [ChainComplex.next_nat_zero, HomologicalComplex.shape _ 0 0 (by simp)]
        rfl⟩).symm)

def realSingularAugmentation (X : Type) [TopologicalSpace X] :
    (realSingularChainComplex X).X 0 →ₗ[ℝ] ℝ :=
  ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℝ ℝ)).hom.comp
    (realSingularZeroClass X)

theorem realSingularAugmentation_eq_sum (X : Type) [TopologicalSpace X] :
    realSingularAugmentation X =
      (Sigma.desc (fun _ : (TopCat.toSSet.obj (TopCat.of X)) _⦋0⦌ =>
        𝟙 (ModuleCat.of ℝ ℝ))).hom := by
  let K := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℝ ℝ
  let C := K.chainComplex R
  change (((C.liftCycles (𝟙 _) 0 (by simp) (by simp)) ≫
    C.homologyπ 0) ≫ K.homology₀ε R).hom = _
  apply congrArg (fun k : C.X 0 ⟶ R => k.hom)
  apply SSet.chainComplex_hom_ext
  intro x
  rw [Category.assoc, HomologicalComplex.comp_liftCycles_assoc]
  change C.liftCycles (K.ιChainComplex x) 0 _ _ ≫
    C.homologyπ 0 ≫ K.homology₀ε R = _
  rw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  rfl

theorem realSingularZeroClass_eq_zero_iff
    (X : Type) [TopologicalSpace X] (z : (realSingularChainComplex X).X 0) :
    realSingularZeroClass X z = 0 ↔
      ∃ w : (realSingularChainComplex X).X 1,
        ((realSingularChainComplex X).d 1 0).hom w = z := by
  rw [realSingularZeroClass_eq_moduleHomologyClass]
  have h := moduleHomologyClass_eq_zero_iff ((realSingularChainComplex X).sc 0)
    (show ((realSingularChainComplex X).sc 0).X₂ from z) (by
      change ((realSingularChainComplex X).d 0 ((ComplexShape.down ℕ).next 0)).hom z = 0
      rw [ChainComplex.next_nat_zero, HomologicalComplex.shape _ 0 0 (by simp)]
      rfl)
  change _ ↔ ∃ w : (realSingularChainComplex X).X ((ComplexShape.down ℕ).prev 0),
    ((realSingularChainComplex X).d ((ComplexShape.down ℕ).prev 0) 0).hom w = z at h
  rw [ChainComplex.prev ℕ 0] at h
  exact h

theorem realSingularAugmentation_eq_zero_iff
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (z : (realSingularChainComplex X).X 0) :
    realSingularAugmentation X z = 0 ↔
      ∃ w : (realSingularChainComplex X).X 1,
        ((realSingularChainComplex X).d 1 0).hom w = z := by
  change (realSingularHomologyZeroEquiv X) (realSingularZeroClass X z) = 0 ↔ _
  rw [map_eq_zero_iff _ (realSingularHomologyZeroEquiv X).injective,
    realSingularZeroClass_eq_zero_iff]

@[simp] theorem realSingularAugmentation_boundary
    (X : Type) [TopologicalSpace X] (w : (realSingularChainComplex X).X 1) :
    realSingularAugmentation X (((realSingularChainComplex X).d 1 0).hom w) = 0 := by
  have h := (realSingularZeroClass_eq_zero_iff X _).mpr ⟨w, rfl⟩
  simp only [realSingularAugmentation, LinearMap.comp_apply, h, map_zero]

@[simp] theorem realSingularAugmentation_generator
    (X : Type) [TopologicalSpace X]
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋0⦌) (r : ℝ) :
    realSingularAugmentation X
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ).hom r) = r := by
  rw [realSingularAugmentation_eq_sum]
  exact congrArg (fun k : ModuleCat.of ℝ ℝ ⟶ ModuleCat.of ℝ ℝ => k.hom r)
    (Sigma.ι_comp_desc (fun _ : (TopCat.toSSet.obj (TopCat.of X)) _⦋0⦌ =>
      𝟙 (ModuleCat.of ℝ ℝ)) σ)

theorem realSingularAugmentation_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    (realSingularAugmentation Y).comp ((realSingularChainMap f hf).f 0).hom =
      realSingularAugmentation X := by
  rw [realSingularAugmentation_eq_sum, realSingularAugmentation_eq_sum]
  let K := TopCat.toSSet.obj (TopCat.of X)
  let L := TopCat.toSSet.obj (TopCat.of Y)
  let R := ModuleCat.of ℝ ℝ
  let φ : K ⟶ L := TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf))
  change ((SSet.chainComplexMap φ R).f 0 ≫
    Sigma.desc (fun _ : L _⦋0⦌ => 𝟙 R)).hom = _
  apply congrArg (fun k : (K.chainComplex R).X 0 ⟶ R => k.hom)
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp only [SSet.ιChainComplex, Sigma.ι_comp_desc]
  rfl

def realSingularAugmentedBoundary (X : Type) [TopologicalSpace X] :
    (realSingularChainComplex X).X 1 →ₗ[ℝ] LinearMap.ker (realSingularAugmentation X) :=
  ((realSingularChainComplex X).d 1 0).hom.codRestrict
    (LinearMap.ker (realSingularAugmentation X))
    (fun w => realSingularAugmentation_boundary X w)

theorem realSingularAugmentedBoundary_surjective
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    Function.Surjective (realSingularAugmentedBoundary X) := by
  intro z
  obtain ⟨w, hw⟩ := (realSingularAugmentation_eq_zero_iff X z.val).mp z.property
  exact ⟨w, Subtype.ext hw⟩

def realSingularZeroFill (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    LinearMap.ker (realSingularAugmentation X) →ₗ[ℝ] (realSingularChainComplex X).X 1 :=
  Classical.choose ((realSingularAugmentedBoundary X).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (realSingularAugmentedBoundary_surjective X)))

theorem realSingularZeroFill_boundary
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (z : LinearMap.ker (realSingularAugmentation X)) :
    ((realSingularChainComplex X).d 1 0).hom (realSingularZeroFill X z) = z.val := by
  have h := LinearMap.congr_fun
    (Classical.choose_spec ((realSingularAugmentedBoundary X).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (realSingularAugmentedBoundary_surjective X)))) z
  exact congrArg Subtype.val h

end Problem340

end

end OAI
