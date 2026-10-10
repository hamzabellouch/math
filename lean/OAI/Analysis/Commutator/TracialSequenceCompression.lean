import Mathlib
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.ReducingCompression
import OAI.Analysis.Commutator.TracialSequence

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence ReducingRepresentation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma vector_const (a : A) : vector τ ω (BoundedContinuousFunction.const ℕ a)=
    constant ω τ.GNS (algebraVector τ a) := by
  rw [constant_apply]
  change (vectorPre τ ω _ : Space ω τ.GNS)=(constantPre ω τ.GNS _ : Space ω τ.GNS)
  congr 1

lemma constant_mem (x : τ.GNS) : constant ω τ.GNS x∈boundedSubspace τ ω := by
  refine (algebraVector_dense τ).induction_on
    (p := fun y => constant ω τ.GNS y∈boundedSubspace τ ω) x ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (constant ω τ.GNS).continuous
  · intro a
    rw [←vector_const]
    exact vector_mem τ ω _

def constantIn : τ.GNS →ₗᵢ[ℂ] boundedSubspace τ ω where
  toFun x := ⟨constant ω τ.GNS x,constant_mem τ ω x⟩
  map_add' := by intro x y; apply Subtype.ext; exact map_add (constant ω τ.GNS) x y
  map_smul' := by intro r x; apply Subtype.ext; exact map_smul (constant ω τ.GNS) r x
  norm_map' := (constant ω τ.GNS).norm_map

@[simp] lemma constantIn_coe (x : τ.GNS) : (constantIn τ ω x:Space ω τ.GNS)=constant ω τ.GNS x := rfl

def compressed (S : τ.GNS →L[ℂ] τ.GNS) : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω :=
  compression (boundedSubspace τ ω) (act ω (BoundedContinuousFunction.const ℕ S))

lemma norm_compressed_le (S : τ.GNS →L[ℂ] τ.GNS) : ‖compressed τ ω S‖≤‖S‖ := by
  exact (norm_compression_le _ _).trans (le_of_eq (norm_act_constant ω S))

lemma compressed_constant (S : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    compressed τ ω S (constantIn τ ω x)=constantIn τ ω (S x) := by
  change (boundedSubspace τ ω).orthogonalProjectionOnto
    (act ω (BoundedContinuousFunction.const ℕ S) (constant ω τ.GNS x))=_
  rw [act_constant]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (constantIn τ ω (S x))

lemma leftFamily_const (a : A) : leftFamily τ (BoundedContinuousFunction.const ℕ a)=
    BoundedContinuousFunction.const ℕ (τ.gnsStarAlgHom a) := rfl

lemma leftRestricted_constant (a : A) (x : τ.GNS) :
    leftRestricted τ ω (BoundedContinuousFunction.const ℕ a) (constantIn τ ω x)=
      constantIn τ ω (τ.gnsStarAlgHom a x) := by
  apply Subtype.ext
  change act ω (leftFamily τ (BoundedContinuousFunction.const ℕ a)) (constant ω τ.GNS x)=_
  rw [leftFamily_const,act_constant]
  rfl

lemma leftRestricted_eq_zero_iff (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (a : ℕ →ᵇ A) :
    leftRestricted τ ω a=0 ↔ vector τ ω a=0 := by
  constructor
  · intro h
    let v : boundedSubspace τ ω := ⟨vector τ ω 1,vector_mem τ ω 1⟩
    have he := congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
      (T v:Space ω τ.GNS)) h
    change leftHom τ ω a (vector τ ω 1)=0 at he
    simpa only [leftHom_vector,mul_one] using he
  · exact left_null τ ω hτ

lemma commutator_bound (S : τ.GNS →L[ℂ] τ.GNS) (a : ℕ →ᵇ A) (c : ℝ)
    (hc : ∀ i, ‖S*τ.gnsStarAlgHom (a i)-τ.gnsStarAlgHom (a i)*S‖≤c) :
    ‖compressed τ ω S*leftRestricted τ ω a-leftRestricted τ ω a*compressed τ ω S‖≤c := by
  have hc0 : 0≤c := (norm_nonneg _).trans (hc 0)
  let T : ℕ →ᵇ (τ.GNS →L[ℂ] τ.GNS) :=
    BoundedContinuousFunction.const ℕ S*leftFamily τ a-leftFamily τ a*BoundedContinuousFunction.const ℕ S
  have hT : ‖T‖≤c := (BoundedContinuousFunction.norm_le hc0).mpr hc
  have hid : act ω T=act ω (BoundedContinuousFunction.const ℕ S)*leftHom τ ω a-
      leftHom τ ω a*act ω (BoundedContinuousFunction.const ℕ S) := by
    change actionHom ω (_*_ - _*_) = _
    rw [map_sub,map_mul,map_mul]
    rfl
  calc
    _ ≤ ‖act ω (BoundedContinuousFunction.const ℕ S)*leftHom τ ω a-
        leftHom τ ω a*act ω (BoundedContinuousFunction.const ℕ S)‖ :=
      norm_commutator_compression_le (leftHom τ ω) (boundedSubspace τ ω)
        (leftHom_preserves τ ω) _ a
    _ = ‖act ω T‖ := congrArg norm hid.symm
    _ ≤ ‖T‖ := norm_act_le ω T
    _ ≤ c := hT

lemma commutator_zero (S : τ.GNS →L[ℂ] τ.GNS) (a : ℕ →ᵇ A)
    (ha : ∀ i, S*τ.gnsStarAlgHom (a i)=τ.gnsStarAlgHom (a i)*S) :
    compressed τ ω S*leftRestricted τ ω a=leftRestricted τ ω a*compressed τ ω S := by
  apply sub_eq_zero.mp
  exact (@norm_le_zero_iff (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) _ _).mp
    (commutator_bound τ ω S a 0 (fun i => by rw [ha i,sub_self,norm_zero]))

lemma norm_original_commutator_le (S : τ.GNS →L[ℂ] τ.GNS) (a : A) :
    ‖S*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*S‖≤
      ‖compressed τ ω S*leftRestricted τ ω (BoundedContinuousFunction.const ℕ a)-
        leftRestricted τ ω (BoundedContinuousFunction.const ℕ a)*compressed τ ω S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg
    (compressed τ ω S*leftRestricted τ ω (BoundedContinuousFunction.const ℕ a)-
      leftRestricted τ ω (BoundedContinuousFunction.const ℕ a)*compressed τ ω S))
  intro x
  have h := (compressed τ ω S*leftRestricted τ ω (BoundedContinuousFunction.const ℕ a)-
    leftRestricted τ ω (BoundedContinuousFunction.const ℕ a)*compressed τ ω S).le_opNorm
      (constantIn τ ω x)
  simpa only [sub_apply,mul_apply_eq_comp,leftRestricted_constant,compressed_constant,
    ←map_sub,LinearIsometry.norm_map] using h

end Kadison.TracialSequence

end

end
end

end OAI
