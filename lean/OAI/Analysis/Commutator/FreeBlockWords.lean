import Mathlib
import OAI.Analysis.Commutator.FreeCreation

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

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor UniformSpace

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma inner_mul_two_wordVector {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a b : A} (ha : a ∈ S i) (hb : b ∈ S i) :
    inner ℂ (t.functional.gnsStarAlgHom a (wordVector t S w))
      (t.functional.gnsStarAlgHom b (wordVector t S z)) =
      t.functional (star a*b)*inner ℂ (wordVector t S w) (wordVector t S z) := by
  rw [mul_wordVector, mul_wordVector, Completion.inner_coe, inner_wordVector]
  change t.functional (star (a*word w)*(b*word z))=_
  simpa only [star_mul, mul_assoc] using
    middle_factor t S hfree hw hz hiw hiz (mul_mem (star_mem ha) hb)

include hfree in
lemma inner_mul_two_tailSpan (i : ι) {a b : A} (ha : a ∈ S i) (hb : b ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpan t S i) (hy : y ∈ tailSpan t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
      t.functional (star a*b)*inner ℂ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, hiz, rfl⟩ := hy
      exact inner_mul_two_wordVector t S hfree hw hz hiw hiz ha hb
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, mul_add]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]; ring
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, mul_add]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]; ring

include hfree in
lemma inner_mul_two_tailSpace (i : ι) {a b : A} (ha : a ∈ S i) (hb : b ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpace t S i) (hy : y ∈ tailSpace t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
      t.functional (star a*b)*inner ℂ x y := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
      t.functional (star a*b)*inner ℂ x y}) ?_ ?_ hx
  · intro x hx
    apply closure_minimal (s := (tailSpan t S i : Set _))
      (t := {y | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom b y) =
        t.functional (star a*b)*inner ℂ x y}) ?_ ?_ hy
    · intro y hy
      exact inner_mul_two_tailSpan t S hfree i ha hb hx hy
    · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

lemma vacuum_mem_tailSpan (i : ι) : wordVector t S [] ∈ tailSpan t S i :=
  Submodule.subset_span ⟨[], reduced_nil, by simp [CanPrepend], rfl⟩

lemma factor_vector_mem_tailSpan {i j : ι} (hij : i≠j) {a : A} (ha : a∈S j) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ tailSpan t S i := by
  let a0 : Letter t S :=
    ⟨j, a-t.functional a • (1 : A),
      sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S j))),
      by simp [map_sub, map_smul, t.normalized]⟩
  have hc : wordVector t S [a0] ∈ tailSpan t S i :=
    Submodule.subset_span ⟨[a0], reduced_singleton _, by simpa [CanPrepend, a0] using hij, rfl⟩
  have hh := (tailSpan t S i).add_mem hc ((tailSpan t S i).smul_mem
    (t.functional a) (vacuum_mem_tailSpan t S i))
  convert hh using 1
  simp only [wordVector, word_cons, word_nil, mul_one, a0, map_sub, map_smul,
    Completion.coe_sub, Completion.coe_smul, sub_add_cancel]

lemma factor_vector_mem_tailSpace {i j : ι} (hij : i≠j) {a : A} (ha : a∈S j) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ tailSpace t S i :=
  (tailSpan t S i).le_topologicalClosure (factor_vector_mem_tailSpan t S hij ha)

end Kadison.FreeCreation
end

end OAI
