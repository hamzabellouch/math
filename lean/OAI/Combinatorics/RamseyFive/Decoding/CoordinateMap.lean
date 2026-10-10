import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScalarExtension
open scoped LinearAlgebra.Projectivization
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

def coordinateMap : (I → K) →ₛₗ[algebraMap K L] (I → L) where
  toFun v := algebraMap K L ∘ v
  map_add' u v := by ext i; simp
  map_smul' a v := by ext i; simp

lemma coordinateMap_injective : Function.Injective (coordinateMap (K := K) (L := L) (I := I)) := by
  intro u v h
  ext i
  exact (algebraMap K L).injective (congrFun h i)

lemma coordinateMap_ne_zero (v : I → K) (hv : v ≠ 0) :
    coordinateMap (L := L) v ≠ 0 := by
  intro h
  apply hv
  apply coordinateMap_injective (L := L)
  simpa using h

noncomputable def pointMap : ℙ K (I → K) → ℙ L (I → L) :=
  Projectivization.map coordinateMap coordinateMap_injective

lemma pointMap_mk (v : I → K) (hv : v ≠ 0) :
    pointMap (L := L) (Projectivization.mk K v hv) = Projectivization.mk L
      (coordinateMap v) (coordinateMap_ne_zero v hv) := rfl

theorem independent_pointMap [Finite I] {J : Type*} {p : J → ℙ K (I → K)}
    (hp : Projectivization.Independent p) :
    Projectivization.Independent (pointMap (L := L) ∘ p) := by
  obtain ⟨v, hv, hi⟩ := hp
  change Projectivization.Independent (fun j => Projectivization.mk L
    (coordinateMap (v j)) (coordinateMap_ne_zero (v j) (hv j)))
  apply Projectivization.Independent.mk
  exact linearIndependent_algebraMap_comp_iff.mpr hi

theorem pointMap_injective [Finite I] :
    Function.Injective (pointMap (K := K) (L := L) (I := I)) := by
  intro p r h
  by_contra hn
  have hi := independent_pointMap (L := L) ((Projectivization.independent_pair_iff_ne p r).mpr hn)
  have he : pointMap (L := L) ∘ ![p, r] = ![pointMap p, pointMap r] := by
    ext i
    fin_cases i <;> rfl
  rw [he, Projectivization.independent_pair_iff_ne] at hi
  exact hi h

end SharpRamseyFive.ScalarExtension

end OAI
