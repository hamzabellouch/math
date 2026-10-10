import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.NormLower
import OAI.Analysis.BiholderTransport.LinearAlgebra.InverseProfile
import OAI.Analysis.BiholderTransport.Regularity.FixedJoinUpper
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactCrossing
import OAI.Analysis.BiholderTransport.Calculus.DerivativeNegLowerCrossing

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingFixedJoinMiddle_strict_crossing {a : M} {b p : Model n} {h : ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hh : 0 < h) (hh1 : h < 1)
    (hleft : h • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hright : (1-h) • (sprayFlow h
      (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h
        (⟨((extChartAt 𝓘(ℝ,Model n) a).symm b),
          (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
            ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) (v : Model n) (hv : ‖v‖=1) :
    0 < -(fderiv ℝ (movingFixedJoinMiddle a h) (1,(b,p)) (1,0) v v) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have hx : x∈(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).baseSet := by
    change x∈(chartAt (Model n) a).source
    simpa only [x,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  have hv0 : v≠0 := by intro h; simp only [h,norm_zero] at hv; norm_num at hv
  have hLv : L v≠0 := by
    intro Hz
    have H := congrArg ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x) Hz
    have HL := Trivialization.continuousLinearMapAt_symmL (R := ℝ)
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a) hx v
    exact hv0 (by simpa only [L,HL,map_zero] using H)
  have hLVpos : 0 < ‖L v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hLv)
  have hM := movingFixedJoinMiddle_contDiffAt
    (movingFixedJoinAction_contDiffAt hb hh1.ne' hleft hright)
  have hD := bilinear_time_hasDerivAt (hM.differentiableAt (by simp)) v
  obtain ⟨c,hc,HC⟩ := exists_fixedJoinMiddle_lower_crossing hh hh1 hleft hright
  apply derivative_neg_of_lower_crossing hD hh1 (mul_pos hc hLVpos)
  filter_upwards [HC] with T hT
  intro hhT hT1
  have HB1 := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HBT := (fixedJoinAction_shortened_contDiffAt hh1 hhT hT1 hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [movingFixedJoinMiddle_eq hb h T p v v HBT,movingFixedJoinMiddle_eq hb h 1 p v v HB1]
  have H := hT hhT hT1 (L v)
  nlinarith only [H]

end WeakMTWTransport

end

end OAI
