import Mathlib
import OAI.Analysis.Commutator.TracialSequence

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

def vectorIn (a : ℕ →ᵇ A) : boundedSubspace τ ω := ⟨vector τ ω a,vector_mem τ ω a⟩

@[simp] lemma vectorIn_coe (a : ℕ →ᵇ A) : (vectorIn τ ω a : Space ω τ.GNS)=vector τ ω a := rfl

lemma leftRestricted_vector (a b : ℕ →ᵇ A) :
    leftRestricted τ ω a (vectorIn τ ω b)=vectorIn τ ω (a*b) := by
  apply Subtype.ext
  exact leftHom_vector τ ω a b

lemma operator_ext (S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (h : ∀ a : ℕ →ᵇ A, S (vectorIn τ ω a)=T (vectorIn τ ω a)) : S=T := by
  apply ContinuousLinearMap.ext
  intro x
  let P := (boundedSubspace τ ω).orthogonalProjectionOnto
  have hc : IsClosed {y : Space ω τ.GNS | S (P y)=T (P y)} :=
    isClosed_eq (S.continuous.comp P.continuous) (T.continuous.comp P.continuous)
  have hm : (LinearMap.range (vector τ ω) : Set (Space ω τ.GNS))⊆
      {y | S (P y)=T (P y)} := by
    rintro _ ⟨a,rfl⟩
    have hp : P (vector τ ω a)=vectorIn τ ω a :=
      (boundedSubspace τ ω).orthogonalProjectionOnto_mem_subspace_eq_self (vectorIn τ ω a)
    simpa only [Set.mem_ofPred_eq,hp] using h a
  have hx := closure_minimal hm hc x.property
  change S (P (x:Space ω τ.GNS))=T (P (x:Space ω τ.GNS)) at hx
  simpa only [P,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hx

def sequenceVacuum : boundedSubspace τ ω := vectorIn τ ω 1

@[simp] lemma leftRestricted_vacuum (a : ℕ →ᵇ A) :
    leftRestricted τ ω a (sequenceVacuum τ ω)=vectorIn τ ω a := by
  rw [sequenceVacuum,leftRestricted_vector,mul_one]

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

def rightFamily (a : ℕ →ᵇ A) : ℕ →ᵇ (τ.GNS →L[ℂ] τ.GNS) :=
  BoundedContinuousFunction.mkOfDiscrete (fun i => rightMul τ hτ (a i)) (2*‖a‖)
    (fun i j => (dist_le_norm_add_norm _ _).trans (by
      have hi := (rightMul_opNorm_le τ hτ (a i)).trans (a.norm_coe_le_norm i)
      have hj := (rightMul_opNorm_le τ hτ (a j)).trans (a.norm_coe_le_norm j)
      linarith))

@[simp] lemma rightFamily_apply (a : ℕ →ᵇ A) (i : ℕ) :
    rightFamily τ hτ a i=rightMul τ hτ (a i) := rfl

def rightAction (a : ℕ →ᵇ A) : Space ω τ.GNS →L[ℂ] Space ω τ.GNS :=
  act ω (rightFamily τ hτ a)

lemma rightAction_vector (a b : ℕ →ᵇ A) :
    rightAction τ ω hτ a (vector τ ω b)=vector τ ω (b*a) := by
  change act ω (rightFamily τ hτ a) (vectorPre τ ω b : Space ω τ.GNS)=_
  rw [act_coe]
  change (actPreLinear ω (rightFamily τ hτ a) (vectorPre τ ω b) : Space ω τ.GNS)=
    (vectorPre τ ω (b*a) : Space ω τ.GNS)
  congr 1
  apply (equiv ω τ.GNS).injective
  apply BoundedContinuousFunction.ext
  intro i
  change rightMul τ hτ (a i) (algebraVector τ (b i))=algebraVector τ (b i*a i)
  exact rightMul_coe τ hτ (a i) (τ.toPreGNS (b i))

lemma rightAction_preserves (a : ℕ →ᵇ A) (x : Space ω τ.GNS) (hx : x∈boundedSubspace τ ω) :
    rightAction τ ω hτ a x∈boundedSubspace τ ω := by
  apply (Submodule.topologicalClosure_minimal (LinearMap.range (vector τ ω))
    (t := (boundedSubspace τ ω).comap (rightAction τ ω hτ a).toLinearMap) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage (rightAction τ ω hτ a).continuous)) hx
  rintro _ ⟨b,rfl⟩
  change rightAction τ ω hτ a (vector τ ω b)∈boundedSubspace τ ω
  rw [rightAction_vector]
  exact vector_mem τ ω _

def rightRestricted (a : ℕ →ᵇ A) : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω :=
  (rightAction τ ω hτ a).restrict (rightAction_preserves τ ω hτ a)

lemma rightRestricted_vector (a b : ℕ →ᵇ A) :
    rightRestricted τ ω hτ a (vectorIn τ ω b)=vectorIn τ ω (b*a) := by
  apply Subtype.ext
  exact rightAction_vector τ ω hτ a b

@[simp] lemma rightRestricted_vacuum (a : ℕ →ᵇ A) :
    rightRestricted τ ω hτ a (sequenceVacuum τ ω)=vectorIn τ ω a := by
  rw [sequenceVacuum,rightRestricted_vector,one_mul]

lemma left_right (a b : ℕ →ᵇ A) :
    leftRestricted τ ω a*rightRestricted τ ω hτ b=
      rightRestricted τ ω hτ b*leftRestricted τ ω a := by
  apply operator_ext τ ω
  intro c
  simp only [mul_apply_eq_comp,leftRestricted_vector,rightRestricted_vector,mul_assoc]

lemma right_mem_commutant (a : ℕ →ᵇ A) :
    rightRestricted τ ω hτ a∈Set.centralizer (Set.range (leftRestricted τ ω)) := by
  rintro _ ⟨b,rfl⟩
  exact left_right τ ω hτ b a

include hτ in
lemma bicommutant_eq_of_vacuum (S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
    (hS : S∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (h : S (sequenceVacuum τ ω)=T (sequenceVacuum τ ω)) : S=T := by
  apply operator_ext τ ω
  intro a
  have hs := congrArg (fun R : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    R (sequenceVacuum τ ω)) (hS _ (right_mem_commutant τ ω hτ a))
  have ht := congrArg (fun R : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
    R (sequenceVacuum τ ω)) (hT _ (right_mem_commutant τ ω hτ a))
  simp only [mul_apply_eq_comp,rightRestricted_vacuum] at hs ht
  rw [h] at hs
  exact hs.symm.trans ht

end Kadison.TracialSequence

end

end
end

end OAI
