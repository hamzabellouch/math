import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripReduction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientCore

namespace OAI

/-! The actual finite arithmetic core/cusp cover, with each unbounded
part replaced by its exact half-open period strip. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCuspNeighborhood_cover :
    ∃ S : Finset SL(2,Eisenstein), ∀ V : ℝ,
      cubicThetaQuotientCore S V ∪ (⋃ δ∈S, cubicThetaCuspNeighborhood δ⁻¹ V)=univ := by
  obtain ⟨S,hS⟩ := cubicThetaQuotientCore_cusps_cover
  refine ⟨S,fun V => Set.eq_univ_of_forall ?_⟩
  intro q
  have hq : q∈cubicThetaQuotientCore S V ∪ cubicThetaQuotientCusps S V := by
    rw [hS V]
    trivial
  rcases hq with hq | ⟨p,hp,hpq⟩
  · exact Or.inl hq
  · obtain ⟨δ,hδ⟩ := mem_iUnion.mp hp
    obtain ⟨hδS,y,hy,hyp⟩ := mem_iUnion.mp hδ
    let r : CubicThetaPoint := ⟨y,hy.1.1⟩
    have hr : δ⁻¹ • r=p := Subtype.ext hyp
    have hn := cubicThetaCuspNeighborhood_mem_of_height δ⁻¹ r hy.2
    rw [hr,hpq] at hn
    exact Or.inr (mem_iUnion.mpr ⟨δ,mem_iUnion.mpr ⟨hδS,hn⟩⟩)

theorem cubicThetaCuspTransition_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1≤cubicThetaPointHeight p → cubicThetaPointHeight p≤2 →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S 2 := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y≤2 := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le hp₂
    apply (div_le_iff₀ (cubicThetaPointHeight_pos p)).mpr
    linarith
  have hyc : y.val∈cubicThetaSiegelCore 2 := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,?_⟩
  · change (k • q).val∈cubicThetaCompactCore S 2
    refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
    have he := congrArg cubicThetaPointCoordinates hpoint
    exact he
  · exact cubicThetaQuotient_covering.map_smul k

end CubicFirstMoment

end

end OAI
