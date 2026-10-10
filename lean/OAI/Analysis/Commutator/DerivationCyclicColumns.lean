import Mathlib
import OAI.Analysis.Commutator.CbDerivationQuantitative
import OAI.Analysis.Commutator.CyclicDecomposition

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.DerivationColumns

open ReducingRepresentation CyclicDecomposition

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

abbrev Cyclic (ξ : H) := cyclicSubspace σ.range ξ

theorem invariant (ξ : H) : ∀ (a : A) (x : H),x∈Cyclic σ ξ → σ a x∈Cyclic σ ξ :=
  fun a => cyclicSubspace_invariant σ.range ξ (Set.mem_range_self a)

lemma cyclic_dense (ξ : H) : DenseRange (fun a : A =>
    restrict σ (Cyclic σ ξ) (invariant σ ξ) a ⟨ξ,mem_cyclicSubspace_self σ.range ξ⟩) := by
  let K := Cyclic σ ξ
  let act : A → K := fun a => ⟨σ a ξ,invariant σ ξ a ξ (mem_cyclicSubspace_self σ.range ξ)⟩
  have hi : (Subtype.val : K → H) '' Set.range act=(orbitSubmodule σ.range ξ : Set H) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨σ a,Set.mem_range_self a,rfl⟩
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨act a,⟨a,rfl⟩,rfl⟩
  intro x
  change x∈closure (Set.range act)
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hi]
  exact x.property

variable (D : A →L[ℂ] (H →L[ℂ] H))
  (hD : ∀ a b,D (a*b)=(D a).comp (σ b)+(σ a).comp (D b))

local instance {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] :
  NormedAddCommGroup (K →L[ℂ] H) := ContinuousLinearMap.toNormedAddCommGroup

local instance {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] :
  NormedSpace ℂ (K →L[ℂ] H) := ContinuousLinearMap.toNormedSpace

def restrictDerivation (ξ : H) : A →L[ℂ] (Cyclic σ ξ →L[ℂ] H) :=
  ((ContinuousLinearMap.compL ℂ (Cyclic σ ξ) H H).flip (Cyclic σ ξ).subtypeL).comp D

@[simp] lemma restrictDerivation_apply (ξ : H) (a : A) :
    restrictDerivation σ D ξ a=(D a).comp (Cyclic σ ξ).subtypeL := rfl

include hD in
lemma restrictDerivation_mul (ξ : H) (a b : A) :
    restrictDerivation σ D ξ (a*b)=(restrictDerivation σ D ξ a).comp (restrict σ (Cyclic σ ξ) (invariant σ ξ) b)+
      (σ a).comp (restrictDerivation σ D ξ b) := by
  ext x
  simp only [restrictDerivation_apply,hD,ContinuousLinearMap.comp_apply,_root_.add_apply]
  rfl

variable [PartialOrder A] [StarOrderedRing A]

include hD in
theorem exists_column (ξ : H) : ∃ V : Cyclic σ ξ →L[ℂ] H,∀ a : A,
    (D a).comp (Cyclic σ ξ).subtypeL=V.comp (restrict σ (Cyclic σ ξ) (invariant σ ξ) a)-(σ a).comp V := by
  obtain ⟨V,_,hV⟩ := CbFactor.cyclic_implementation
    (restrict σ (Cyclic σ ξ) (invariant σ ξ)) σ (restrictDerivation σ D ξ)
    (restrictDerivation_mul σ D hD ξ) ⟨ξ,mem_cyclicSubspace_self σ.range ξ⟩ (cyclic_dense σ ξ)
  exact ⟨V,hV⟩

def column (ξ : H) : Cyclic σ ξ →L[ℂ] H := (exists_column σ D hD ξ).choose

lemma column_spec (ξ : H) (a : A) :
    (D a).comp (Cyclic σ ξ).subtypeL=(column σ D hD ξ).comp (restrict σ (Cyclic σ ξ) (invariant σ ξ) a)-
      (σ a).comp (column σ D hD ξ) := (exists_column σ D hD ξ).choose_spec a

lemma column_commutator (ξ : H) (a : A) :
    extendZero (K:=Cyclic σ ξ) (column σ D hD ξ)*σ a-
      σ a*extendZero (K:=Cyclic σ ξ) (column σ D hD ξ)=D a*(Cyclic σ ξ).starProjection := by
  ext x
  have hh := congrArg (fun L : Cyclic σ ξ →L[ℂ] H => L ((Cyclic σ ξ).orthogonalProjectionOnto x))
    (column_spec σ D hD ξ a)
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at hh
  change column σ D hD ξ ((Cyclic σ ξ).orthogonalProjectionOnto (σ a x))-
    σ a (column σ D hD ξ ((Cyclic σ ξ).orthogonalProjectionOnto x))=D a ((Cyclic σ ξ).starProjection x)
  rw [project_intertwines σ (Cyclic σ ξ) (invariant σ ξ)]
  exact hh.symm

variable (Q : Decomposition σ.range)

def finiteProjection (s : Finset Q.I) : H →L[ℂ] H := ∑ i∈s,(Cyclic σ (Q.ξ i)).starProjection

def finiteImplementer (s : Finset Q.I) : H →L[ℂ] H := ∑ i∈s,extendZero (K:=Cyclic σ (Q.ξ i)) (column σ D hD (Q.ξ i))

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteProjection_projection (s : Finset Q.I) : IsStarProjection (finiteProjection σ Q s) := by
  classical
  constructor
  · change (∑ i∈s,(Cyclic σ (Q.ξ i)).starProjection)*(∑ i∈s,(Cyclic σ (Q.ξ i)).starProjection)=_
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · exact (isStarProjection_starProjection (U:=Cyclic σ (Q.ξ i))).isIdempotentElem.eq
    · intro j hj hne
      exact Q.cross i j hne.symm
  · change star (∑ i∈s,(Cyclic σ (Q.ξ i)).starProjection)=_
    rw [star_sum]
    exact Finset.sum_congr rfl (fun i hi => (isStarProjection_starProjection (U:=Cyclic σ (Q.ξ i))).isSelfAdjoint.star_eq)

omit [PartialOrder A] [StarOrderedRing A] in
lemma finiteProjection_norm_le (s : Finset Q.I) : ‖finiteProjection σ Q s‖≤1 :=
  (finiteProjection_projection σ Q s).norm_le _

lemma finite_column_identity (s : Finset Q.I) (a : A) :
    finiteImplementer σ D hD Q s*σ a-σ a*finiteImplementer σ D hD Q s=D a*finiteProjection σ Q s := by
  simp only [finiteImplementer,finiteProjection,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i hi => column_commutator σ D hD (Q.ξ i) a)

lemma finite_scalar_bound (s : Finset Q.I) (a : A) :
    ‖finiteImplementer σ D hD Q s*σ a-σ a*finiteImplementer σ D hD Q s‖≤‖D‖*‖a‖ := by
  rw [finite_column_identity]
  calc
    _≤‖D a‖*‖finiteProjection σ Q s‖ := norm_mul_le _ _
    _≤‖D a‖*1 := mul_le_mul_of_nonneg_left (finiteProjection_norm_le σ Q s) (norm_nonneg _)
    _≤‖D‖*‖a‖ := by simpa using D.le_opNorm a

end Kadison.DerivationColumns

end

end
end

end OAI
