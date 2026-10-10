import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCorePartition

namespace OAI

/-! A finite family of genuine compactly supported smooth chart cutoffs
controls the actual arithmetic core. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups Manifold ContDiff BigOperators
namespace CubicFirstMoment

def cubicThetaCoreBump (q : CubicThetaQuotient) :
    SmoothBumpFunction (𝓘(ℝ,ℂ × ℝ)) q := Classical.choice inferInstance

lemma cubicThetaCoreBump_finite_cover (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      ∃ c∈A, cubicThetaCoreBump c q=1 := by
  classical
  obtain ⟨A,_,hA⟩ := (cubicThetaQuotientCore_compact S V).elim_nhds_subcover
    (fun c => interior {q | cubicThetaCoreBump c q=1}) (fun c _ => by
      have h : {q | cubicThetaCoreBump c q=1}∈𝓝 c := (cubicThetaCoreBump c).eventuallyEq_one
      exact interior_mem_nhds.mpr h)
  refine ⟨A,fun q hq => ?_⟩
  obtain ⟨c,hc,hqc⟩ := mem_iUnion₂.mp (hA hq)
  have he : q∈{q | cubicThetaCoreBump c q=1} := interior_subset hqc
  exact ⟨c,hc,he⟩

lemma cubicThetaCoreBump_sum_sq (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      1 ≤ ∑ c∈A, (cubicThetaCoreBump c q)^2 := by
  obtain ⟨A,hA⟩ := cubicThetaCoreBump_finite_cover S V
  refine ⟨A,fun q hq => ?_⟩
  obtain ⟨c,hc,hqc⟩ := hA q hq
  have h := Finset.single_le_sum (fun d (_ : d∈A) => sq_nonneg (cubicThetaCoreBump d q)) hc
  simpa only [hqc,one_pow] using h

lemma cubicThetaCoreBump_compact (c : CubicThetaQuotient) :
    HasCompactSupport (cubicThetaCoreBump c) := (cubicThetaCoreBump c).hasCompactSupport

end CubicFirstMoment

end

end OAI
