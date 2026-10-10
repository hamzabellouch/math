import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.StrongDegreeBudget
import OAI.Combinatorics.SharpRamsey.Geometry.PencilGeometry

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset SharpRamseyFive.PoissonScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestRadialWeights_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestRadialWeights_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

def radialWeight (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (W : RadialLine x) : ℝ≥0 := c*(radialFiber S x W).card

omit [Finite K] [FiniteDimensional K V] in
lemma radialWeight_coe (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (W : RadialLine x) :
    (radialWeight S x c W : ℝ)=strength S x c W := by
  simp only [radialWeight,strength,NNReal.coe_mul,NNReal.coe_natCast]

lemma radialWeight_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H : Projectivization K (Module.Dual K V))
    (hxH : x.submodule≤LinearMap.ker H.rep) :
    mass (radialWeight S x c) (lines x H)=
      (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule≤LinearMap.ker H.rep)).card := by
  simp only [mass,radialWeight_coe,strength]
  exact hyperplane_mass S x H hxH c

lemma radialWeight_intersection (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V))
    (hxH : x.submodule≤LinearMap.ker H.rep) (hxJ : x.submodule≤LinearMap.ker J.rep) :
    mass (radialWeight S x c) (lines x H∩lines x J)=overlap S x c H J := by
  simp only [mass,radialWeight_coe,strength,overlap]
  exact intersection_mass S x H J hxH hxJ c

omit [Finite K] [FiniteDimensional K V] in
lemma family_filter_card (A : Finset (Projectivization K (Module.Dual K V)))
    (P : Projectivization K (Module.Dual K V)→Prop) :
    (univ.filter (fun H : A => P H)).card=(A.filter P).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun H => ⟨H.1.1,mem_filter.mpr ⟨H.1.2,(mem_filter.mp H.2).2⟩⟩
    invFun := fun H => ⟨⟨H.1,(mem_filter.mp H.2).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp H.2).2⟩⟩
    left_inv := fun H => rfl
    right_inv := fun H => rfl }

lemma family_one_direction (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (W : RadialLine x) :
    (univ.filter (fun H : A => W∈lines x H)).card≤Nat.card K+1 := by
  have hh := one_direction_card (K:=K) (V:=V) hdim A x W
  refine Nat.le_trans ?_ hh
  apply Finset.card_le_card_of_injOn (fun H : A => H.val)
  · intro H hH
    exact mem_filter.mpr ⟨H.2,(mem_filter.mp hH).2⟩
  · intro H hH J hJ he
    exact Subtype.ext he

lemma family_two_directions (hdim : Module.finrank K V≤4)
    (A : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V)
    (D E : RadialLine x) (hne : D≠E) :
    (univ.filter (fun H : A => D∈lines x H ∧ E∈lines x H)).card≤1 := by
  have hh := two_directions_card (K:=K) (V:=V) hdim A x D E hne
  refine Nat.le_trans ?_ hh
  apply Finset.card_le_card_of_injOn (fun H : A => H.val)
  · intro H hH
    exact mem_filter.mpr ⟨H.2,(mem_filter.mp hH).2⟩
  · intro H hH J hJ he
    exact Subtype.ext he

lemma family_pair_card (A : Finset (Projectivization K (Module.Dual K V)))
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0) (a : ℝ)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    (univ.filter (fun z : SharpRamseyFive.WeightedPrograms.DistinctPairs A =>
      a ≤ mass (radialWeight S x c) (lines x z.1∩lines x z.2))).card=
      (largePairs S x c a A).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun z => ⟨(z.1.1.1,z.1.2.1.1),?_⟩
    invFun := fun z => ⟨⟨⟨z.1.1,?_⟩,⟨⟨z.1.2,?_⟩,?_⟩⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨z.1.1.2,z.1.2.1.2⟩,?_,?_⟩
    · intro he
      exact z.1.2.2 (Subtype.ext he.symm)
    · rw [←radialWeight_intersection S x c _ _ (hA _ z.1.1.2) (hA _ z.1.2.1.2)]
      exact (mem_filter.mp z.2).2
  · exact (mem_product.mp (mem_filter.mp z.2).1).1
  · exact (mem_product.mp (mem_filter.mp z.2).1).2
  · intro he
    exact (mem_filter.mp z.2).2.1 (congrArg Subtype.val he).symm
  · apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [radialWeight_intersection S x c _ _
      (hA _ (mem_product.mp (mem_filter.mp z.2).1).1)
      (hA _ (mem_product.mp (mem_filter.mp z.2).1).2)]
    exact (mem_filter.mp z.2).2.2
  · intro z
    rfl
  · intro z
    rfl

lemma family_neighbor_card (A : Finset (Projectivization K (Module.Dual K V)))
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0) (a : ℝ)
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) (H : A) :
    (univ.filter (fun J : {J : A // J≠H} =>
      a ≤ mass (radialWeight S x c) (lines x J∩lines x H))).card=
      (largeNeighbors S x c a A H).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun J => ⟨J.1.1.1,?_⟩
    invFun := fun J => ⟨⟨⟨J.1,?_⟩,?_⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply mem_filter.mpr
    refine ⟨J.1.1.2,?_,?_⟩
    · intro he
      exact J.1.2 (Subtype.ext he.symm)
    · rw [←radialWeight_intersection S x c _ _ (hA _ H.2) (hA _ J.1.1.2),inter_comm]
      exact (mem_filter.mp J.2).2
  · exact (mem_filter.mp J.2).1
  · intro he
    exact (mem_filter.mp J.2).2.1 (congrArg Subtype.val he).symm
  · apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [inter_comm,radialWeight_intersection S x c _ _ (hA _ H.2) (hA _ (mem_filter.mp J.2).1)]
    exact (mem_filter.mp J.2).2.2
  · intro J
    rfl
  · intro J
    rfl

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
