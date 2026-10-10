import Mathlib
import OAI.Analysis.Commutator.BoundedPositiveSequence
import OAI.Analysis.Commutator.CStarContractiveLifts
import OAI.Analysis.Commutator.SpectralCutoff
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BoundedContinuousFunction ComplexOrder

namespace Kadison.ProjectionLifts

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def halfCut (a : M) : M := ⟨Polar.halfCut (a : H →L[ℂ] H),Polar.halfCut_mem M a.property⟩

lemma isProjection_halfCut (a : M) : IsStarProjection (halfCut M a) := by
  constructor
  · apply Subtype.ext
    exact (Polar.isProjection_halfCut (a : H →L[ℂ] H)).isIdempotentElem.eq
  · apply Subtype.ext
    exact (Polar.isProjection_halfCut (a : H →L[ℂ] H)).isSelfAdjoint.star_eq

lemma rounding (a : M) (h0 : 0≤a) (h1 : a≤1) :
    star (halfCut M a-a)*(halfCut M a-a)≤a-a*a :=
  Polar.halfCut_rounding h0 h1

variable {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

def roundedSequence (c : ι →ᵇ M) : ι →ᵇ M :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => halfCut M (c i)) 1
    (fun i => (isProjection_halfCut M (c i)).norm_le _)

@[simp] lemma roundedSequence_apply (c : ι →ᵇ M) (i : ι) :
    roundedSequence M c i=halfCut M (c i) := rfl

lemma roundedSequence_projection (c : ι →ᵇ M) : IsStarProjection (roundedSequence M c) := by
  constructor
  · apply BoundedContinuousFunction.ext
    intro i
    exact (isProjection_halfCut M (c i)).isIdempotentElem.eq
  · apply BoundedContinuousFunction.ext
    intro i
    exact (isProjection_halfCut M (c i)).isSelfAdjoint.star_eq

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem projection_lift (φ : (ι →ᵇ M) →⋆ₐ[ℂ] B) {p : B} (hp : IsStarProjection p)
    (hr : p∈Set.range φ) : ∃ q : ι →ᵇ M, (∀ i, IsStarProjection (q i)) ∧ φ q=p := by
  obtain ⟨b,hb,hbp⟩ := CStarContractiveLifts.contraction φ (hp.norm_le p) hr
  let c : ι →ᵇ M := star b*b
  have hc (i : ι) : 0≤c i := star_mul_self_nonneg (b i)
  have hc1 (i : ι) : c i≤1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hc i)).mp
    change ‖star (b i)*b i‖≤1
    rw [CStarRing.norm_star_mul_self]
    have hbi : ‖b i‖≤1 := (b.norm_coe_le_norm i).trans hb
    nlinarith [norm_nonneg (b i)]
  have hcp : φ c=p := by
    dsimp only [c]
    rw [map_mul,map_star,hbp,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  let q := roundedSequence M c
  let d := c-c*c-star (q-c)*(q-c)
  have hd (i : ι) : 0≤d i := by
    change 0≤c i-c i*c i-star (halfCut M (c i)-c i)*(halfCut M (c i)-c i)
    exact sub_nonneg.mpr (rounding M (c i) (hc i) (hc1 i))
  have hφd := BoundedPositiveSequence.map_nonneg φ d hd
  have hneg : star (φ q-p)*(φ q-p)≤0 := by
    dsimp only [d] at hφd
    simpa only [map_sub,map_mul,map_star,hcp,hp.isIdempotentElem.eq,sub_self,
      zero_sub,neg_nonneg] using hφd
  have he : φ q-p=0 := (CStarRing.star_mul_self_eq_zero_iff _).mp
    (le_antisymm hneg (star_mul_self_nonneg _))
  exact ⟨q,fun i => isProjection_halfCut M (c i),sub_eq_zero.mp he⟩

end Kadison.ProjectionLifts

end

end
end

end OAI
