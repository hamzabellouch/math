import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspWindowCore

namespace OAI

/-! Every bounded height band in an integral cusp lies in a compact core. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaHeightBand_core {H : ℝ} (hH : 1≤H) :
    ∃ S : Finset SL(2,Eisenstein), ∀ (δ : SL(2,Eisenstein)) (p : CubicThetaPoint),
      1≤cubicThetaPointHeight p → cubicThetaPointHeight p≤H →
        cubicThetaQuotientMap (δ • p)∈cubicThetaQuotientCore S H := by
  obtain ⟨S,hS⟩ := cubicThetaFiniteSiegelCover
  refine ⟨S,?_⟩
  intro δ p hp₁ hp₂
  let q := δ • p
  obtain ⟨σ,hσ,k,hk⟩ := hS q.val q.property
  let y := (σ*k.val) • q
  have hy : y.val∈cubicThetaSiegelSet := hk
  have hb : cubicThetaPointHeight y≤H := by
    have he : y=(σ*k.val*δ) • p := by rw [mul_smul]
    rw [he]
    apply (cubicThetaPointHeight_full_smul_le _ p).trans
    apply max_le hp₂
    apply (div_le_iff₀ (cubicThetaPointHeight_pos p)).mpr
    nlinarith
  have hyc : y.val∈cubicThetaSiegelCore H := cubicThetaSiegelSet_mem_core hy hb
  have hpoint : σ⁻¹ • y=k • q := by
    dsimp [y]
    rw [mul_smul,inv_smul_smul]
    rfl
  refine ⟨k • q,?_,cubicThetaQuotient_covering.map_smul k⟩
  change (k • q).val∈cubicThetaCompactCore S H
  refine mem_iUnion.mpr ⟨σ,mem_iUnion.mpr ⟨hσ,y.val,hyc,?_⟩⟩
  exact congrArg cubicThetaPointCoordinates hpoint

end CubicFirstMoment

end

end OAI
