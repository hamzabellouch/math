import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianMixedOperator
import OAI.Analysis.BiholderTransport.Coordinates.MovingNormalEndpointJoin

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
local instance tangentFiniteTrivBound (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance endpointProductNormedGroupTriv (x y : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedAddCommGroup
local instance endpointProductNormedSpaceTriv (x y : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedSpace
local instance endpointDualNormedGroupTriv (x y : M) :
    NormedAddCommGroup ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
local instance endpointDualNormedSpaceTriv (x y : M) :
    NormedSpace ℝ ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance

lemma normalEndpointMixedOperator_norm_trivialization_le {a c x y : M} {h B D : ℝ}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hB : 0≤B) (hD : 0≤D)
    (hAx : ‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x‖≤B)
    (hAy : ‖(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).continuousLinearMapAt ℝ y‖≤D)
    (p : TangentSpace 𝓘(ℝ,Model n) x)
    (hF : ContDiffAt ℝ 2
      (movingNormalEndpointJoinAction a c
        (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y)))
      (0,(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)) :
    ‖normalEndpointMixedOperator x y h p‖≤
      ‖fderiv ℝ (fderiv ℝ (movingNormalEndpointJoinAction a c
        (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y))))
        (0,(trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)‖*D*B := by
  let Ax := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x
  let Ay := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) c).continuousLinearMapAt ℝ y
  let L := Ay.prodMap Ax
  let F := movingNormalEndpointJoinAction a c
    (h,((extChartAt 𝓘(ℝ,Model n) a) x,(extChartAt 𝓘(ℝ,Model n) c) y))
  let J := fderiv ℝ (fderiv ℝ F) (0,Ax p)
  have he : normalEndpointJoinAction x y h=fun z => F (L z) := by
    funext z
    exact (movingNormalEndpointJoinAction_trivialization hx hy h z.1 z.2).symm
  change ‖mixedOperator _‖≤‖J‖*D*B
  apply mixedOperator_norm_le _ (by positivity)
  intro v w
  rw [negativeMixedForm_apply,abs_neg,he]
  have H := second_fderiv_comp_affine (f := F) L 0 (0,p)
    (by simpa only [zero_add,L,ContinuousLinearMap.coe_prodMap',Prod.map_apply,map_zero] using hF) (v,0) (0,w)
  have H' : fderiv ℝ (fderiv ℝ (fun z => F (L z))) (0,p) (v,0) (0,w)=
      J (Ay v,0) (0,Ax w) := by
    simpa only [zero_add,L,ContinuousLinearMap.coe_prodMap',Prod.map_apply,map_zero,J] using H
  rw [H',←Real.norm_eq_abs]
  have hv : ‖Ay v‖≤D*‖v‖ := (Ay.le_opNorm v).trans (mul_le_mul_of_nonneg_right hAy (norm_nonneg _))
  have hw : ‖Ax w‖≤B*‖w‖ := (Ax.le_opNorm w).trans (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))
  calc
    ‖J (Ay v,0) (0,Ax w)‖≤‖J (Ay v,0)‖*‖((0:Model n),Ax w)‖ := (J _).le_opNorm _
    _≤(‖J‖*‖(Ay v,(0:Model n))‖)*‖((0:Model n),Ax w)‖ := by gcongr; exact J.le_opNorm _
    _=(‖J‖*‖Ay v‖)*‖Ax w‖ := by simp
    _≤(‖J‖*(D*‖v‖))*(B*‖w‖) := by gcongr
    _=(‖J‖*D*B)*‖v‖*‖w‖ := by ring

end WeakMTWTransport

end

end OAI
