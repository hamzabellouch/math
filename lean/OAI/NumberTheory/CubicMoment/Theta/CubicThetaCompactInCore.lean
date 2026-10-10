import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactHeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspDisjointness

namespace OAI

/-! Every compact subset of the actual arithmetic quotient lies in
one of the constructed compact cores. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompact_subset_core {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ (S : Finset SL(2,Eisenstein)) (V : ℝ), K⊆cubicThetaQuotientCore S V := by
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_all_cusp_height_bound hK
  refine ⟨S,C+1,?_⟩
  intro q hq
  have hcover : q∈cubicThetaQuotientCore S (C+1) ∪
      ⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ (C+1) := by rw [hS]; trivial
  rcases hcover with hcore | hcusp
  · exact hcore
  · obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hcusp
    obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ⁻¹ (C+1) q).mp hqδ
    have he : cubicThetaQuotientMap (δ⁻¹ • p)∈K := hpq ▸ hq
    have hh := hbound (δ⁻¹ • p) he δ
    rw [smul_inv_smul] at hh
    linarith

end CubicFirstMoment

end

end OAI
