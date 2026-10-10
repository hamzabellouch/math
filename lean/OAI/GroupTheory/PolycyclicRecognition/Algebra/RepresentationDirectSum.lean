import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationColimit

namespace OAI

/-! # Concrete sums of integral representations for the telescope resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G : Type} [Group G] {ι : Type}

abbrev integralRepresentationSum (A : ι → Rep.{0} ℤ G) : Rep.{0} ℤ G :=
  Rep.of (Representation.directSum (fun i => (A i).ρ))

abbrev integralRepresentationSumInclusion (A : ι → Rep.{0} ℤ G) (i : ι) :
    A i ⟶ integralRepresentationSum A := by
  classical
  exact Rep.ofHom ⟨DirectSum.lof ℤ ι (fun i => (A i).V) i, fun g => by
    ext x
    simp [Representation.directSum]⟩

@[simp]
theorem integralRepresentationSumInclusion_apply [DecidableEq ι] (A : ι → Rep.{0} ℤ G) (i : ι)
    (x : A i) : (integralRepresentationSumInclusion A i).hom x =
      DirectSum.of (fun i => (A i).V) i x := by
  simp [integralRepresentationSumInclusion, DirectSum.lof_eq_of]
  ext j
  simp [DirectSum.of_apply]

@[simp]
theorem integralRepresentationSumInclusion_same [DecidableEq ι]
    (A : ι → Rep.{0} ℤ G) (i : ι) (x : A i) :
    ((integralRepresentationSumInclusion A i).hom x) i = x := by
  have h := congrArg (fun y : integralRepresentationSum A => y i)
    (integralRepresentationSumInclusion_apply A i x)
  exact h.trans (by simp)

theorem integralRepresentationSumInclusion_ne [DecidableEq ι]
    (A : ι → Rep.{0} ℤ G) (i j : ι) (hij : i ≠ j) (x : A i) :
    ((integralRepresentationSumInclusion A i).hom x) j = 0 := by
  have h := congrArg (fun y : integralRepresentationSum A => y j)
    (integralRepresentationSumInclusion_apply A i x)
  exact h.trans (by simp [DirectSum.of_apply, hij])

def integralRepresentationSumDesc (A : ι → Rep.{0} ℤ G) (B : Rep.{0} ℤ G)
    (f : ∀ i, A i ⟶ B) : integralRepresentationSum A ⟶ B := by
  classical
  exact Rep.ofHom ⟨DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap), fun g => by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    change DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap)
      ((DirectSum.lmap (fun i => (A i).ρ g)) (DirectSum.lof ℤ ι _ i x)) =
      B.ρ g (DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap)
        (DirectSum.lof ℤ ι _ i x))
    rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
    exact Rep.hom_comm_apply (f i) g x⟩

@[reassoc (attr := simp)]
theorem integralRepresentationSumInclusion_desc (A : ι → Rep.{0} ℤ G)
    (B : Rep.{0} ℤ G) (f : ∀ i, A i ⟶ B) (i : ι) :
    integralRepresentationSumInclusion A i ≫ integralRepresentationSumDesc A B f = f i := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change DirectSum.toModule ℤ ι B (fun i => (f i).hom.toLinearMap)
    (DirectSum.lof ℤ ι _ i x) = (f i).hom x
  simp only [DirectSum.toModule_lof]
  rfl

theorem integralRepresentationSum_hom_ext {A : ι → Rep.{0} ℤ G} {B : Rep.{0} ℤ G}
    {f g : integralRepresentationSum A ⟶ B}
    (h : ∀ i, integralRepresentationSumInclusion A i ≫ f =
      integralRepresentationSumInclusion A i ≫ g) : f = g := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply DirectSum.linearMap_ext
  intro i
  exact congrArg (fun k : A i ⟶ B => k.hom.toLinearMap) (h i)

instance integralRepresentationSum_projective (A : ι → Rep.{0} ℤ G)
    [∀ i, Projective (A i)] : Projective (integralRepresentationSum A) where
  factors {E X} f e := by
    refine ⟨integralRepresentationSumDesc A E
      (fun i => Projective.factorThru (integralRepresentationSumInclusion A i ≫ f) e), ?_⟩
    apply integralRepresentationSum_hom_ext
    intro i
    rw [← Category.assoc, integralRepresentationSumInclusion_desc,
      Projective.factorThru_comp]

end PolycyclicRecognition

end

end OAI
