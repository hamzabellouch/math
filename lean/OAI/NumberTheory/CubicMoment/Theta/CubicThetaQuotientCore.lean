import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientCharts
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactCoreCover

namespace OAI

/-! The proved arithmetic core/cusp cover descends to the actual quotient;
the core is compact in its Hausdorff quotient topology. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCompactCore_positive (S : Finset SL(2,Eisenstein)) (V : ℝ)
    {p : ℂ × ℝ} (hp : p∈cubicThetaCompactCore S V) : 0<p.2 := by
  obtain ⟨δ,hδ⟩ := mem_iUnion.mp hp
  obtain ⟨_,q,hq,rfl⟩ := mem_iUnion.mp hδ
  exact cubicThetaMobius_height_pos _ (cubicThetaSiegelCore_positive hq)

def cubicThetaQuotientCore (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    Set CubicThetaQuotient :=
  cubicThetaQuotientMap '' {p : CubicThetaPoint | p.val∈cubicThetaCompactCore S V}

def cubicThetaQuotientCusps (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    Set CubicThetaQuotient :=
  cubicThetaQuotientMap '' {p : CubicThetaPoint | p.val∈cubicThetaCuspCharts S V}

lemma cubicThetaQuotientCore_compact (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    IsCompact (cubicThetaQuotientCore S V) := by
  have he : {p : CubicThetaPoint | p.val∈cubicThetaCompactCore S V}=
      cubicThetaPointInclusion.symm '' cubicThetaCompactCore S V := by
    ext p
    constructor
    · intro hp
      exact ⟨p.val,hp,cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)⟩
    · rintro ⟨q,hq,hqp⟩
      have ht : q∈cubicThetaPointInclusion.target := by
        rw [cubicThetaPointInclusion_target]
        exact cubicThetaCompactCore_positive S V hq
      have hv := cubicThetaPointInclusion.right_inv ht
      rw [hqp] at hv
      change p.val=q at hv
      change p.val∈cubicThetaCompactCore S V
      rw [hv]
      exact hq
  apply IsCompact.image _ cubicThetaQuotientMap_open.continuous
  rw [he]
  exact (cubicThetaCompactCore_compact S V).image_of_continuousOn
    (cubicThetaPointInclusion.symm.continuousOn.mono (by
      intro p hp
      rw [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target]
      exact cubicThetaCompactCore_positive S V hp))

lemma cubicThetaQuotientCore_cusps_cover :
    ∃ S : Finset SL(2,Eisenstein), ∀ V : ℝ,
      cubicThetaQuotientCore S V ∪ cubicThetaQuotientCusps S V=Set.univ := by
  obtain ⟨S,hS⟩ := cubicThetaCompactCoreCuspCover
  refine ⟨S,?_⟩
  intro V
  apply Set.eq_univ_of_forall
  intro q
  let p := cubicThetaQuotientLift q
  obtain ⟨k,hk⟩ := hS V p.val p.property
  have he : cubicThetaQuotientMap (k • p)=q :=
    cubicThetaQuotient_covering.map_smul k |>.trans (cubicThetaQuotientLift_map q)
  rcases hk with hk | hk
  · left
    exact ⟨k • p,hk,he⟩
  · right
    exact ⟨k • p,hk,he⟩

end CubicFirstMoment

end

end OAI
