import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicFiniteness
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

namespace OAI

/-! # Integral Poincaré duality for an infinite cyclic group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (G : Type) [CommGroup G]

theorem leftRegularHomEquiv_precomp_difference (g : G) (A : Rep ℤ G)
    (f : Rep.leftRegular ℤ G ⟶ A) :
    Rep.leftRegularHomEquiv A (cyclicDifference G g ≫ f) =
      A.ρ g (Rep.leftRegularHomEquiv A f) - Rep.leftRegularHomEquiv A f := by
  simp [cyclicDifference, Rep.homEquiv, Rep.sub_hom, Rep.applyAsHom,
    Rep.hom_comp]
  simpa using Rep.hom_comm_apply f g (MonoidAlgebra.single 1 1)

def cyclicHomDifference (g : G) :
    ModuleCat.of ℤ (Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G) ⟶
      ModuleCat.of ℤ (Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G) :=
  ModuleCat.ofHom (Linear.leftComp ℤ _ (cyclicDifference G g))

def cyclicHomAugmentation :
    ModuleCat.of ℤ (Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G) ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom ((integralAugmentation G).comp
    (Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G)).toLinearMap)

theorem cyclicHomAugmentation_surjective :
    Function.Surjective (cyclicHomAugmentation G).hom := by
  intro r
  refine ⟨(Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G)).symm
    (MonoidAlgebra.single 1 r), ?_⟩
  change integralAugmentation G
    ((Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G)) _) = r
  rw [LinearEquiv.apply_symm_apply, integralAugmentation_single]

theorem cyclicHomAugmentation_exact (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Function.Exact (cyclicHomDifference G g).hom (cyclicHomAugmentation G).hom := by
  intro x
  change integralAugmentation G (Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G) x) = 0 ↔ _
  rw [← LinearMap.mem_ker, integralAugmentation_ker_of_cyclic G g hg]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G)).symm y, ?_⟩
    apply (Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G)).injective
    change Rep.leftRegularHomEquiv _ (cyclicDifference G g ≫ _) = _
    rw [leftRegularHomEquiv_precomp_difference, LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    refine ⟨Rep.leftRegularHomEquiv (Rep.leftRegular ℤ G) y, ?_⟩
    exact (leftRegularHomEquiv_precomp_difference G g _ y).symm

def infiniteCyclicCochains (g : G) (A : Rep ℤ G) : CochainComplex (ModuleCat ℤ) ℕ :=
  (infiniteCyclicComplex G g).linearYonedaObj ℤ A

theorem infiniteCyclicCochains_d_zero_one (g : G) :
    (infiniteCyclicCochains G g (Rep.leftRegular ℤ G)).d 0 1 = cyclicHomDifference G g := by
  have hd : (infiniteCyclicComplex G g).d 1 0 = cyclicDifference G g :=
    ChainComplex.of_d (infiniteCyclicObjects G) (infiniteCyclicDifferentials G g) 0
  change ModuleCat.ofHom (Linear.leftComp ℤ _ ((infiniteCyclicComplex G g).d 1 0)) = _
  rw [hd]
  rfl

theorem infiniteCyclicCochains_d_one_two (g : G) (A : Rep ℤ G) :
    (infiniteCyclicCochains G g A).d 1 2 = 0 := by
  simp [infiniteCyclicCochains, ChainComplex.linearYonedaObj_d,
    infiniteCyclicComplex, ChainComplex.of.d, infiniteCyclicDifferentials]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (0 : infiniteCyclicObjects G 2 ⟶ infiniteCyclicObjects G 1) ≫ f = 0
  exact zero_comp

variable [Infinite G]

omit [Infinite G] in
theorem infiniteCyclicCochains_isZero (g : G) (A : Rep ℤ G) (i : ℕ) (hi : 1 < i) :
    IsZero ((infiniteCyclicCochains G g A).X i) := by
  change IsZero (ModuleCat.of ℤ ((infiniteCyclicComplex G g).X i ⟶ A))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  exact ⟨fun f h => (infiniteCyclicComplex_isZero G g i hi).eq_of_src f h⟩

theorem infiniteCyclic_cohomology_zero (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    IsZero (groupCohomology (Rep.leftRegular ℤ G) 0) := by
  apply IsZero.of_iso (Y := ModuleCat.of ℤ (Representation.leftRegular ℤ G).invariants)
    _ (groupCohomology.H0Iso _)
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  have hz (x : (Representation.leftRegular ℤ G).invariants) : x = 0 := by
    apply Subtype.ext
    exact leftRegular_fixed_generator_eq_zero g hg x (x.property g)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem infiniteCyclic_cohomology_above_one (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep ℤ G) (i : ℕ) (hi : 1 < i) :
    IsZero (groupCohomology A i) := by
  apply IsZero.of_iso _ (groupCohomologyIso A i (infiniteCyclicResolution G g hg))
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂,
    infiniteCyclicResolution, infiniteCyclicCochains] using
    infiniteCyclicCochains_isZero G g A i hi

def infiniteCyclic_cohomology_one_iso (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology (Rep.leftRegular ℤ G) 1 ≅ ModuleCat.of ℤ ℤ := by
  let K := infiniteCyclicCochains G g (Rep.leftRegular ℤ G)
  let S := K.sc' 0 1 2
  have hf : S.f = cyclicHomDifference G g := infiniteCyclicCochains_d_zero_one G g
  have hz : S.g = 0 := infiniteCyclicCochains_d_one_two G g _
  have he : Function.Exact S.f.hom (cyclicHomAugmentation G).hom := by
    rw [hf]
    exact cyclicHomAugmentation_exact G g hg
  let c := CokernelCofork.ofπ (f := S.f) (cyclicHomAugmentation G)
    (by ext x; exact he.apply_apply_eq_zero x)
  let hc : IsColimit c := ModuleCat.isColimitCokernelCofork S.f
    (cyclicHomAugmentation G) he (cyclicHomAugmentation_surjective G)
  let data := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hz c hc
  exact groupCohomologyIso _ 1 (infiniteCyclicResolution G g hg) ≪≫
    K.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫ data.homologyIso

theorem poincareDuality_one_of_infinite_cyclic (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : IsIntegralPoincareDualityGroup G 1 := by
  refine ⟨finiteProjectiveResolution_of_infinite_cyclic G g hg, ?_,
    ⟨infiniteCyclic_cohomology_one_iso G g hg⟩⟩
  intro i hi
  by_cases hz : i = 0
  · subst i
    exact infiniteCyclic_cohomology_zero G g hg
  · exact infiniteCyclic_cohomology_above_one G g hg _ i (by omega)

end PolycyclicRecognition

end

end OAI
