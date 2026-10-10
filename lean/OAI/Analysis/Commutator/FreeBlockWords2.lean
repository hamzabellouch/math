import Mathlib
import OAI.Analysis.Commutator.FreeBlockWords
import OAI.Analysis.Commutator.FreeWordTensor

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i ≠ j)

abbrev Letters (i j : ι) := letterSpace t S j × letterSpace t S i

def blockValue : List (Letters t S i j) → A → A
  | [], z => z
  | x::xs, z => letterValue t S j x.1 *
      (letterValue t S i x.2 * blockValue xs z)

def blockVector (xs : List (Letters t S i j)) (z : A) : t.functional.GNS :=
  (t.functional.toPreGNS (blockValue t S xs z) : t.functional.GNS)

@[simp] lemma blockVector_nil (z : A) : blockVector t S ([] : List (Letters t S i j)) z =
    (t.functional.toPreGNS z : t.functional.GNS) := rfl

lemma blockVector_cons (x : Letters t S i j) (xs : List (Letters t S i j)) (z : A) :
    blockVector t S (x::xs) z = t.functional.gnsStarAlgHom (letterValue t S j x.1)
      (t.functional.gnsStarAlgHom (letterValue t S i x.2) (blockVector t S xs z)) := by
  simp [blockVector, blockValue, PositiveLinearMap.gnsStarAlgHom]

include hij in
lemma blockVector_mem_tail (xs : List (Letters t S i j)) {z : A} (hz : z ∈ S j) :
    blockVector t S xs z ∈ tailSpace t S i := by
  induction xs with
  | nil => exact factor_vector_mem_tailSpace t S hij hz
  | cons x xs ih =>
    rw [blockVector_cons]
    apply headSpace_le_other_tailSpace t S hij.symm
    apply creation_mem_headSpace t S j x.1.property.1 x.1.property.2
    apply headSpace_le_other_tailSpace t S hij
    exact creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2 ih

include hfree hij in
lemma blockVector_cons_gram (x y : Letters t S i j)
    (xs ys : List (Letters t S i j)) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S (x::xs) z) (blockVector t S (y::ys) v) =
      (inner ℂ x.1 y.1 * inner ℂ x.2 y.2)*
        inner ℂ (blockVector t S xs z) (blockVector t S ys v) := by
  rw [blockVector_cons, blockVector_cons]
  have hx := blockVector_mem_tail t S hij xs hz
  have hy := blockVector_mem_tail t S hij ys hv
  rw [inner_mul_two_tailSpace t S hfree j (a := letterValue t S j x.1) (b := letterValue t S j y.1) x.1.property.1 y.1.property.1
      (headSpace_le_other_tailSpace t S hij
        (creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2 hx))
      (headSpace_le_other_tailSpace t S hij
        (creation_mem_headSpace t S i (a := letterValue t S i y.2) y.2.property.1 y.2.property.2 hy)),
    inner_mul_two_tailSpace t S hfree i (a := letterValue t S i x.2) (b := letterValue t S i y.2) x.2.property.1 y.2.property.1 hx hy]
  rw [inner_letter, inner_letter, mul_assoc]

include hfree hij in
lemma blockVector_cons_nil (x : Letters t S i j)
    (xs : List (Letters t S i j)) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S (x::xs) z) (blockVector t S ([] : List (Letters t S i j)) v) = 0 := by
  rw [blockVector_cons, ← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ _ ((star (t.functional.gnsStarAlgHom (letterValue t S j x.1))) _) = 0
  rw [← map_star]
  have hm : t.functional.gnsStarAlgHom (star (letterValue t S j x.1))
      (blockVector t S ([] : List (Letters t S i j)) v) =
      (t.functional.toPreGNS (star (letterValue t S j x.1)*v) : t.functional.GNS) := by
    simp [blockVector_nil, PositiveLinearMap.gnsStarAlgHom]
  rw [hm]
  have ht := factor_vector_mem_tailSpace t S hij (mul_mem (star_mem x.1.property.1) hv)
  have hh := headSpace_le_tailSpace_orthogonal t S hfree i
    (creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2
      (blockVector_mem_tail t S hij xs hz))
  exact inner_eq_zero_symm.mp (hh _ ht)

include hfree hij in
lemma blockVector_orthogonal (xs ys : List (Letters t S i j))
    (hlen : xs.length ≠ ys.length) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S xs z) (blockVector t S ys v) = 0 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact (hlen rfl).elim
    | cons y ys => exact inner_eq_zero_symm.mp (blockVector_cons_nil t S hfree hij y ys hv hz)
  | cons x xs ih =>
    cases ys with
    | nil => exact blockVector_cons_nil t S hfree hij x xs hz hv
    | cons y ys =>
      rw [blockVector_cons_gram t S hfree hij x y xs ys hz hv,
        ih ys (by simpa using hlen), mul_zero]

include hfree hij in
lemma endpoint_gram (xs ys : List (Letters t S i j)) {a b z v : A}
    (ha : a ∈ S i) (hb : b ∈ S i) (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (t.functional.gnsStarAlgHom a (blockVector t S xs z))
      (t.functional.gnsStarAlgHom b (blockVector t S ys v)) =
      t.functional (star a*b)*inner ℂ (blockVector t S xs z) (blockVector t S ys v) :=
  inner_mul_two_tailSpace t S hfree i ha hb
    (blockVector_mem_tail t S hij xs hz) (blockVector_mem_tail t S hij ys hv)

end Kadison.FreeBlocks
end

end OAI
