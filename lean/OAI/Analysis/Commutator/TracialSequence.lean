import Mathlib
import OAI.Analysis.Commutator.HilbertSequenceOperator
import OAI.Analysis.Commutator.ReducingRepresentation
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def vectorCLM : A →L[ℂ] τ.GNS :=
  (algebraVector τ).mkContinuous ‖vacuum τ‖ (fun a => by
    rw [algebraVector_apply,←left_vacuum]
    exact ((τ.gnsStarAlgHom a).le_opNorm _).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom a)
        (norm_nonneg _)))

@[simp] lemma vectorCLM_apply (a : A) : vectorCLM τ a=algebraVector τ a := rfl

def vectorPre (a : ℕ →ᵇ A) : Pre ω τ.GNS :=
  ⟨BoundedContinuousFunction.comp (vectorCLM τ) (vectorCLM τ).lipschitzWith a⟩

@[simp] lemma vectorPre_seq (a : ℕ →ᵇ A) (i : ℕ) :
    (vectorPre τ ω a).seq i=algebraVector τ (a i) := rfl

def vector : (ℕ →ᵇ A) →ₗ[ℂ] Space ω τ.GNS where
  toFun a := (vectorPre τ ω a : Space ω τ.GNS)
  map_add' a b := by
    rw [←Completion.coe_add]
    congr 1
    apply (equiv ω τ.GNS).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_add (algebraVector τ) _ _
  map_smul' r a := by
    rw [←Completion.coe_smul]
    congr 1
    apply (equiv ω τ.GNS).injective
    apply BoundedContinuousFunction.ext
    intro i
    exact map_smul (algebraVector τ) _ _

lemma vector_eq_zero_iff (a : ℕ →ᵇ A) : vector τ ω a=0 ↔
    Tendsto (fun i => ‖algebraVector τ (a i)‖) (ω : Filter ℕ) (𝓝 0) :=
  coe_eq_zero_iff ω τ.GNS (vectorPre τ ω a)

def boundedSubspace : Submodule ℂ (Space ω τ.GNS) := (LinearMap.range (vector τ ω)).topologicalClosure

instance : CompleteSpace (boundedSubspace τ ω) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma vector_mem (a : ℕ →ᵇ A) : vector τ ω a∈boundedSubspace τ ω :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ a)

def leftFamily (a : ℕ →ᵇ A) : ℕ →ᵇ (τ.GNS →L[ℂ] τ.GNS) :=
  BoundedContinuousFunction.mkOfDiscrete (fun i => τ.gnsStarAlgHom (a i)) (2*‖a‖)
    (fun i j => (dist_le_norm_add_norm _ _).trans (by
      have hi := (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a i)).trans (a.norm_coe_le_norm i)
      have hj := (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a j)).trans (a.norm_coe_le_norm j)
      linarith))

@[simp] lemma leftFamily_apply (a : ℕ →ᵇ A) (i : ℕ) : leftFamily τ a i=τ.gnsStarAlgHom (a i) := rfl

lemma norm_leftFamily_le (a : ℕ →ᵇ A) : ‖leftFamily τ a‖≤‖a‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg a)).mpr
  intro i
  exact (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a i)).trans (a.norm_coe_le_norm i)

def leftHom : (ℕ →ᵇ A) →⋆ₐ[ℂ] (Space ω τ.GNS →L[ℂ] Space ω τ.GNS) :=
  (actionHom ω).comp {
    toFun := leftFamily τ
    map_one' := by apply BoundedContinuousFunction.ext; intro i; exact map_one τ.gnsStarAlgHom
    map_zero' := by apply BoundedContinuousFunction.ext; intro i; exact map_zero τ.gnsStarAlgHom
    map_add' := by intro a b; apply BoundedContinuousFunction.ext; intro i; exact map_add τ.gnsStarAlgHom _ _
    map_mul' := by intro a b; apply BoundedContinuousFunction.ext; intro i; exact map_mul τ.gnsStarAlgHom _ _
    map_star' := by intro a; apply BoundedContinuousFunction.ext; intro i; exact map_star τ.gnsStarAlgHom _
    commutes' := by intro r; apply BoundedContinuousFunction.ext; intro i; exact τ.gnsStarAlgHom.commutes r }

lemma leftHom_vector (a b : ℕ →ᵇ A) : leftHom τ ω a (vector τ ω b)=vector τ ω (a*b) := by
  change act ω (leftFamily τ a) (vectorPre τ ω b : Space ω τ.GNS)=_
  rw [act_coe]
  change (actPreLinear ω (leftFamily τ a) (vectorPre τ ω b) : Space ω τ.GNS)=
    (vectorPre τ ω (a*b) : Space ω τ.GNS)
  congr 1
  apply (equiv ω τ.GNS).injective
  apply BoundedContinuousFunction.ext
  intro i
  change τ.gnsStarAlgHom (a i) (algebraVector τ (b i))=algebraVector τ (a i*b i)
  exact left_coe τ _ _

lemma leftHom_preserves (a : ℕ →ᵇ A) (x : Space ω τ.GNS) (hx : x∈boundedSubspace τ ω) :
    leftHom τ ω a x∈boundedSubspace τ ω := by
  apply (Submodule.topologicalClosure_minimal (LinearMap.range (vector τ ω))
    (t := (boundedSubspace τ ω).comap (leftHom τ ω a).toLinearMap) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage (leftHom τ ω a).continuous)) hx
  rintro _ ⟨b,rfl⟩
  change leftHom τ ω a (vector τ ω b)∈boundedSubspace τ ω
  rw [leftHom_vector]
  exact vector_mem τ ω _

def leftRestricted : (ℕ →ᵇ A) →⋆ₐ[ℂ] (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
  ReducingRepresentation.restrict (leftHom τ ω) (boundedSubspace τ ω) (leftHom_preserves τ ω)

@[simp] lemma leftRestricted_apply (a : ℕ →ᵇ A) (x : boundedSubspace τ ω) :
    (leftRestricted τ ω a x:Space ω τ.GNS)=leftHom τ ω a x := rfl

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma vector_mul_norm (a b : A) : ‖algebraVector τ (a*b)‖≤‖b‖*‖algebraVector τ a‖ := by
  change ‖(τ.toPreGNS (a*b) : τ.GNS)‖≤‖b‖*‖(τ.toPreGNS a : τ.GNS)‖
  simp only [Completion.norm_coe]
  change ‖rightMulPre τ hτ b (τ.toPreGNS a)‖≤_
  exact (rightMulPre τ hτ b).le_of_opNorm_le (norm_rightMulPre_le τ hτ b) _

include hτ in
lemma vector_mul_zero {a : ℕ →ᵇ A} (ha : vector τ ω a=0) (b : ℕ →ᵇ A) :
    vector τ ω (a*b)=0 := by
  rw [vector_eq_zero_iff] at ha ⊢
  have hlim := (tendsto_const_nhds (x := ‖b‖)).mul ha
  apply squeeze_zero (fun i => norm_nonneg _) (fun i =>
    (vector_mul_norm τ hτ (a i) (b i)).trans
      (mul_le_mul_of_nonneg_right (b.norm_coe_le_norm i) (norm_nonneg _)))
  simpa only [mul_zero] using hlim

include hτ in
lemma left_null {a : ℕ →ᵇ A} (ha : vector τ ω a=0) : leftRestricted τ ω a=0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change leftHom τ ω a (x:Space ω τ.GNS)=0
  have hclosed : IsClosed {y : Space ω τ.GNS | leftHom τ ω a y=0} :=
    isClosed_eq (leftHom τ ω a).continuous continuous_const
  apply closure_minimal (t := {y : Space ω τ.GNS | leftHom τ ω a y=0}) ?_ hclosed x.property
  rintro _ ⟨b,rfl⟩
  change leftHom τ ω a (vector τ ω b)=0
  rw [leftHom_vector]
  exact vector_mul_zero τ ω hτ ha b

end Kadison.TracialSequence

end

end
end

end OAI
