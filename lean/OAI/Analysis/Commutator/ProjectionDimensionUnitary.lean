import Mathlib
import OAI.Analysis.Commutator.DyadicDimension
import OAI.Analysis.Commutator.ProjectionDimensionTopology

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma projection_unitary_equivalent {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H)∈M) :
    Equivalent M p ((u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H)) := by
  have hi : star ((u : H →L[ℂ] H)*p)*((u : H →L[ℂ] H)*p)=p := by
    simp only [star_mul,hp.isSelfAdjoint.star_eq,mul_assoc,
      ←mul_assoc (star (u : H →L[ℂ] H)),u.property.1,one_mul,hp.isIdempotentElem.eq]
  have hf : ((u : H →L[ℂ] H)*p)*star ((u : H →L[ℂ] H)*p)=
      (u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H) := by
    rw [star_mul,hp.isSelfAdjoint.star_eq,←mul_assoc, mul_assoc (u : H →L[ℂ] H) p p,
      hp.isIdempotentElem.eq]
  refine ⟨⟨(u : H →L[ℂ] H)*p,M.mul_mem hu hpM,?_,hi.le,hf.le⟩,hi,hf⟩
  rw [mul_assoc,hi,mul_assoc,hp.isIdempotentElem.eq]

lemma unitary_projection {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (u : unitary (H →L[ℂ] H)) :
    IsStarProjection ((u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H)) := by
  exact hp.map (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u)

lemma dimension_unitary {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H)∈M) :
    dimension M hfac hd ((u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H))=
      dimension M hfac hd p :=
  (dimension_congr_equivalent M hfac hd hp (unitary_projection hp u)
    (projection_unitary_equivalent M hpM hp u hu)).symm

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (hfin : IsFiniteAlgebra M)

include hfin in
theorem orbit_vector_uniform_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : H →L[ℂ] H,p∈M → IsStarProjection p →
      dimension M hfac hd p<δ → ∀ u : unitary (H →L[ℂ] H),
      (u : H →L[ℂ] H)∈M → ‖p ((u : H →L[ℂ] H) x)‖<ε := by
  obtain ⟨δ,hδ,h⟩ := ProjectionDimensionTopology.vector_uniform_absolute_continuity
    M hfac hd hfin x ε hε
  refine ⟨δ,hδ,?_⟩
  intro p hpM hp hdp u hu
  have hqM : ((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)*p*
      star ((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)∈M :=
    M.mul_mem (M.mul_mem (M.star_mem' hu) hpM) (by simpa using hu)
  have hq := h _ hqM (unitary_projection hp (star u)) (by
    rw [dimension_unitary M hfac hd hpM hp (star u) (M.star_mem' hu)]
    exact hdp)
  simpa only [Unitary.coe_star,star_star,mul_apply_eq_comp,
    ←Unitary.coe_star,Unitary.norm_map] using hq

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
