import Mathlib
import OAI.Analysis.BiholderTransport.Volume.UpperJacobianBarrier
import OAI.Analysis.BiholderTransport.Regularity.ActiveDifference
import OAI.Analysis.BiholderTransport.LinearAlgebra.ChartFirstMatrix

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FirstRank
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma ChartFixedPrefixLimit.positive_rank_direction
    {a:M} {v G:M → ℝ} {t:ℝ}
    {q:ℕ → subgradientGraph (n := n) (cTransform v)}
    {q₀:subgradientGraph (n := n) (cTransform v)}
    (J:ChartFixedPrefixLimit a v G t q q₀)
    (hbase:q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let b:=graphBaseCoordinate a q₀.1
    let p:=graphVelocityCoordinate a q₀.1
    let E:=TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
    let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0<J.w₀ i}
    let pj:κ → E:=fun i=>chartFiberInverse a b (J.pj₀ i)
    let P:E:=chartFiberInverse a b p
    let S:=Submodule.span ℝ (range (fun i=>pj i-P))
    ∀ (A C:ℝ),0<A →
    (∀d:Model n,A*‖chartFiberInverse a b d‖^2+
      C*(inner ℝ P (chartFiberInverse a b d))^2≤J.H d d) →
    ∀ (level:E → ℝ) (Bc Bo:ℝ → ℝ),
    Bc (level P)≤Bo (level P) →
    0<Bc (level P)-∑ i,J.w₀ i*Bo (level (chartFiberInverse a b (J.pj₀ i))) →
    ∃ e∈S,‖e‖=1 ∧ 0 < inner ℝ P e ∧ S=Submodule.span ℝ {e} ∧ A≤(-C)*(inner ℝ P e)^2 := by
  dsimp only
  let b:=graphBaseCoordinate a q₀.1
  let p:=graphVelocityCoordinate a q₀.1
  let x:=(extChartAt 𝓘(ℝ,Model n) a).symm b
  let E:=TangentSpace 𝓘(ℝ,Model n) x
  let T:=trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let U:=chartFiberInverse a b
  let V:=T.continuousLinearMapAt ℝ x
  let κ:Type:={i:Fin (Module.finrank ℝ (Model n)+1) // 0<J.w₀ i}
  let pj:κ → E:=fun i=>U (J.pj₀ i)
  let P:E:=U p
  let S:=Submodule.span ℝ (range (fun i=>pj i-P))
  have hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source hbase
  have hx : x∈T.baseSet := by
    simpa only [x,T,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  have hUV (d:E):U (V d)=d := T.symmL_continuousLinearMapAt (R := ℝ) hx d
  have hVU (d:Model n):V (U d)=d := T.continuousLinearMapAt_symmL (R := ℝ) hx d
  intro A C hA hbound level Bc Bo hprofiles hparameter
  have hres:=positive_barycentric_restriction (fun i=>U (J.pj₀ i)) J.w₀ J.nonnegLimit J.totalLimit
  let : Nonempty κ:=hres.1
  have hparam:0<Bc (level P)-∑ i:κ,J.w₀ i*Bo (level (pj i)) := by
    rwa [hres.2.2.2 (fun i=>Bo (level (U (J.pj₀ i))))]
  classical
  have hS:S≠⊥:=active_difference_ne_bot hres.2.1 hprofiles hparam
  let L:E →L[ℝ] E →L[ℝ] ℝ:=J.L.bilinearComp V V
  have hk:S≤LinearMap.ker L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change L (pj i-P)=0
    ext d
    change J.L (V (U (J.pj₀ i)-U p)) (V d)=0
    rw [map_sub,hVU,hVU]
    exact J.kernel i (V d)
  apply unit_positive_direction_of_rank_one_semibound S hA hS
  intro d hd
  have hl:L d=0 := hk hd
  have hzero:J.L (V d) (V d)=0 := congrArg (fun f:E →L[ℝ] ℝ=>f d) hl
  have HH:=hbound (V d)
  rw [hUV] at HH
  have HU:=J.upper (V d)
  rw [hzero] at HU
  linarith only [HH,HU]

end FirstRank
end WeakMTWTransport

end
end

end OAI
