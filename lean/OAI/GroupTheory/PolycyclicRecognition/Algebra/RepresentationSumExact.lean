import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationDirectSum
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # Exact direct sums of integral coefficient sequences -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G ι : Type} [Group G]

def integralRepresentationSumMap {A B : ι → Rep.{0} ℤ G} (f : ∀ i, A i ⟶ B i) :
    integralRepresentationSum A ⟶ integralRepresentationSum B := by
  classical
  exact Rep.ofHom ⟨DirectSum.lmap (fun i => (f i).hom.toLinearMap), fun g => by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change DirectSum.lmap (fun i => (f i).hom.toLinearMap)
        (DirectSum.lmap (fun i => (A i).ρ g) (DirectSum.lof ℤ ι _ i x)) =
      DirectSum.lmap (fun i => (B i).ρ g)
        (DirectSum.lmap (fun i => (f i).hom.toLinearMap) (DirectSum.lof ℤ ι _ i x))
    rw [DirectSum.lmap_lof, DirectSum.lmap_lof, DirectSum.lmap_lof, DirectSum.lmap_lof]
    exact congrArg (DirectSum.lof ℤ ι _ i) (Rep.hom_comm_apply (f i) g x)⟩

@[simp]
theorem integralRepresentationSumMap_apply {A B : ι → Rep.{0} ℤ G}
    (f : ∀ i, A i ⟶ B i) (x : integralRepresentationSum A) (i : ι) :
    ((integralRepresentationSumMap f).hom x) i = (f i).hom (x i) := rfl

theorem integralRepresentationSumMap_injective {A B : ι → Rep.{0} ℤ G}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, Function.Injective (f i).hom) :
    Function.Injective (integralRepresentationSumMap f).hom :=
  (DirectSum.lmap_injective (fun i => (f i).hom.toLinearMap)).mpr hf

theorem integralRepresentationSumMap_surjective {A B : ι → Rep.{0} ℤ G}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, Function.Surjective (f i).hom) :
    Function.Surjective (integralRepresentationSumMap f).hom :=
  (DirectSum.lmap_surjective (fun i => (f i).hom.toLinearMap)).mpr hf

theorem integralRepresentationSumMap_zero (S : ι → ShortComplex (Rep.{0} ℤ G)) :
    integralRepresentationSumMap (fun i => (S i).f) ≫
      integralRepresentationSumMap (fun i => (S i).g) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro i
  exact ConcreteCategory.congr_hom (S i).zero (x i)

def integralRepresentationSumSequence (S : ι → ShortComplex (Rep.{0} ℤ G)) :
    ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (integralRepresentationSumMap (fun i => (S i).f))
    (integralRepresentationSumMap (fun i => (S i).g)) (integralRepresentationSumMap_zero S)

theorem integralRepresentationSumSequence_exact (S : ι → ShortComplex (Rep.{0} ℤ G))
    (hS : ∀ i, (S i).Exact) : (integralRepresentationSumSequence S).Exact := by
  apply (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (DirectSum.lmap (fun i => (S i).f.hom.toLinearMap)) =
    LinearMap.ker (DirectSum.lmap (fun i => (S i).g.hom.toLinearMap))
  rw [DirectSum.range_lmap, DirectSum.ker_lmap]
  have h : (fun i => LinearMap.range (S i).f.hom.toLinearMap) =
      (fun i => LinearMap.ker (S i).g.hom.toLinearMap) := by
    funext i
    exact ((hS i).map (forget₂ (Rep ℤ G) (ModuleCat ℤ))).moduleCat_range_eq_ker
  rw [h]

theorem integralRepresentationSumSequence_shortExact (S : ι → ShortComplex (Rep.{0} ℤ G))
    (hS : ∀ i, (S i).ShortExact) : (integralRepresentationSumSequence S).ShortExact where
  exact := integralRepresentationSumSequence_exact S (fun i => (hS i).exact)
  mono_f := (Rep.mono_iff_injective _).mpr (integralRepresentationSumMap_injective _
    (fun i => (Rep.mono_iff_injective _).mp (hS i).mono_f))
  epi_g := (Rep.epi_iff_surjective _).mpr (integralRepresentationSumMap_surjective _
    (fun i => (Rep.epi_iff_surjective _).mp (hS i).epi_g))

end PolycyclicRecognition

end

end OAI
