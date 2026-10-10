import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationSumExact
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyStableMaps

namespace OAI

/-! # Complete cohomology of finite sums of vanishing coefficients -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
variable {G ι : Type} [Group G]

def integralRepresentationSumProjection (A : ι → Rep.{0} ℤ G) (i : ι) :
    integralRepresentationSum A ⟶ A i :=
  Rep.ofHom ⟨DirectSum.component ℤ ι (fun i => (A i).V) i, fun g => by
    apply LinearMap.ext
    intro x
    rfl⟩

theorem integralRepresentationSumProjection_apply (A : ι → Rep.{0} ℤ G) (i : ι)
    (x : integralRepresentationSum A) :
    (integralRepresentationSumProjection A i).hom x = x i := rfl

theorem integralRepresentationSum_total [Fintype ι] (A : ι → Rep.{0} ℤ G) :
    ∑ i, integralRepresentationSumProjection A i ≫ integralRepresentationSumInclusion A i =
      𝟙 (integralRepresentationSum A) := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simp only [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
  apply DFinsupp.ext
  intro j
  change (∑ i, (integralRepresentationSumInclusion A i).hom (x i)) j = x j
  rw [DFinsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · exact integralRepresentationSumInclusion_same A j (x j)
  · intro i _ hij
    exact integralRepresentationSumInclusion_ne A i j hij (x i)
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem finiteSum_completeCohomology [Finite ι] (A : ι → Rep.{0} ℤ G) (p : ℕ)
    (hA : ∀ i, Subsingleton (ShiftedCompletedCohomology p (A i))) :
    Subsingleton (ShiftedCompletedCohomology p (integralRepresentationSum A)) := by
  classical
  let := Fintype.ofFinite ι
  let F := shiftedCompletedCohomologyFunctor p (G := G)
  have hmap (i : ι) : F.map (integralRepresentationSumProjection A i) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change shiftedCompletedCohomologyMap p (integralRepresentationSumProjection A i) x = 0
    exact (hA i).elim _ _
  have hzero : 𝟙 (F.obj (integralRepresentationSum A)) = 0 := by
    rw [← F.map_id, ← integralRepresentationSum_total A, F.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [F.map_comp, hmap, zero_comp]
  apply subsingleton_of_forall_eq (0 : ShiftedCompletedCohomology p (integralRepresentationSum A))
  intro x
  exact ConcreteCategory.congr_hom hzero x

end PolycyclicRecognition

end

end OAI
