import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactCuspCutoff
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactHeight

namespace OAI

/-! Scalar cusp cutoffs vanish uniformly on each compact quotient
set once their height scale is large enough. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaScalarCuspQuotient_compact_zero {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ N : ℝ, C<N → ∀ δ : SL(2,Eisenstein), ∀ q∈K,
      cubicThetaScalarCuspQuotient δ N q=0 := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaCompact_all_cusp_height_bound hK
  refine ⟨C,hC,fun N hN δ q hq => ?_⟩
  let x := cubicThetaQuotientLift q
  let y := δ⁻¹ • x
  have hzero (r : CubicThetaBottomRow) : cubicThetaScalarCuspTerm N r y.val=0 := by
    have hx : cubicThetaQuotientMap x∈K := by rwa [cubicThetaQuotientLift_map]
    have hr := hbound x hx (r.completion.val*δ⁻¹)
    rw [mul_smul] at hr
    change (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) y.val).2≤C at hr
    rw [← cubicThetaBottomRow_height,r.completion_row] at hr
    exact cubicThetaScalarCuspTerm_zero N (lt_of_le_of_lt hC hN) r (hr.trans hN.le)
  change (∑' r, cubicThetaScalarCuspTerm N r y.val)=0
  simp only [hzero,tsum_zero]

lemma cubicThetaCompactCuspCutoff_compact_one (T : Finset SL(2,Eisenstein))
    {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ N : ℝ, C<N → ∀ q∈K, cubicThetaCompactCuspCutoff T N q=1 := by
  obtain ⟨C,hC,hzero⟩ := cubicThetaScalarCuspQuotient_compact_zero hK
  refine ⟨C,hC,fun N hN q hq => ?_⟩
  simp only [cubicThetaCompactCuspCutoff,hzero N hN _ q hq,Finset.sum_const_zero,sub_zero]

lemma cubicThetaCompactCuspCutoff_local_one (T : Finset SL(2,Eisenstein))
    (q : CubicThetaQuotient) :
    ∃ C≥0, ∀ N : ℝ, C<N → cubicThetaCompactCuspCutoff T N=ᶠ[𝓝 q] (fun _ => (1:ℂ)) := by
  obtain ⟨K,hK,hKq⟩ := exists_compact_mem_nhds q
  obtain ⟨C,hC,h⟩ := cubicThetaCompactCuspCutoff_compact_one T hK
  exact ⟨C,hC,fun N hN => Filter.mem_of_superset hKq (fun x hx => h N hN x hx)⟩

end CubicFirstMoment

end

end OAI
