import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspNeighborhoodCover
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests

namespace OAI

/-! The actual forcing is supported in one compact arithmetic core,
uniformly in the spectral parameter, and defines a compact smooth section. -/
noncomputable section
open Set
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaForcingSeries_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (s : ℂ) (p : CubicThetaPoint),
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S 2 →
        cubicThetaForcingSeries p.val s=0 := by
  obtain ⟨S,hS⟩ := cubicThetaCuspTransition_core
  refine ⟨S,fun s p hp => ?_⟩
  suffices hz : ∀ r, cubicThetaForcingTerm r p.val s=0 by
    simp only [cubicThetaForcingSeries,hz,tsum_zero]
  intro r
  by_cases hh : r.height p.val<1 ∨ 2<r.height p.val
  · exact mul_eq_zero_of_right _ (cubicThetaIncomingForcing_zero s hh)
  · have hlo : 1≤r.height p.val := le_of_not_gt (fun h => hh (Or.inl h))
    have hup : r.height p.val≤2 := le_of_not_gt (fun h => hh (Or.inr h))
    have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
      change (cubicThetaBottomRow r.completion).height p.val=_
      rw [r.completion_row]
    have hq := hS 1 (r.completion • p) (by rwa [he]) (by rwa [he])
    rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
    exact False.elim (hp hq)

def cubicThetaForcingSection (s : ℂ) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaForcingSeries p.val s,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := (cubicThetaForcingSeries_contDiffOn s).contDiffAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact h.continuousAt.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaForcingSeries_automorphy g p.property s⟩

lemma cubicThetaForcingSection_compact (s : ℂ) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaForcingSection s)) := by
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_core
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S 2)
  intro q hq
  by_contra h
  have hz := hS s (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaForcingSeries (cubicThetaQuotientLift q).val s‖=0
  rw [hz,norm_zero]

def cubicThetaForcingTest (s : ℂ) : cubicThetaSmoothTests :=
  ⟨cubicThetaForcingSection s,by
    refine ⟨?_,cubicThetaForcingSection_compact s⟩
    apply (cubicThetaForcingSeries_contDiffOn s).congr
    intro y hy
    change cubicThetaForcingSeries (cubicThetaPointInclusion.symm y).val s=
      cubicThetaForcingSeries y s
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaForcingSeries p s) he
  ⟩

end CubicFirstMoment

end

end OAI
