import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspNeighborhoodCover

namespace OAI

/-! The doubled transition annulus still lies in a compact arithmetic core. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCuspWindow_core :
    ∃ S : Finset SL(2,Eisenstein), ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1≤cubicThetaPointHeight p → cubicThetaPointHeight p≤4 →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S 4 := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y≤4 := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le hp₂
    apply (div_le_iff₀ (cubicThetaPointHeight_pos p)).mpr
    linarith
  have hyc : y.val∈cubicThetaSiegelCore 4 := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,?_⟩
  · change (k • q).val∈cubicThetaCompactCore S 4
    refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
    have he := congrArg cubicThetaPointCoordinates hpoint
    exact he
  · exact cubicThetaQuotient_covering.map_smul k

end CubicFirstMoment

end

end OAI
