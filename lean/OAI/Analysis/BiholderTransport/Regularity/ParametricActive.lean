import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingChartParameters
import OAI.Analysis.BiholderTransport.Regularity.ActiveGraphLimit
import OAI.Analysis.BiholderTransport.Regularity.ActualParameter

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ParametricActive
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma activeLogs_iff_minimum {v:M → ℝ} (hv:Continuous v) {x:M}
    {p:TangentSpace 𝓘(ℝ,Model n) x} : p∈activeLogs v x ↔
    p∈minimizingVectors x ∧ ∀ y:M,v (riemannianExp x p)+cost x (riemannianExp x p) ≤ v y+cost x y := by
  constructor
  · rintro ⟨hm,hcontact⟩
    refine ⟨hm,fun y=>?_⟩
    have H:=cTransform_gap_nonneg hv x y
    dsimp only [contactGap] at *
    linarith only [H,hcontact]
  · rintro ⟨hm,hmin⟩
    refine ⟨hm,?_⟩
    obtain ⟨y,hy⟩:=cTransform_gap_zero hv x
    have H:=cTransform_gap_nonneg hv x (riemannianExp x p)
    have HH:=hmin y
    dsimp only [contactGap] at *
    linarith only [H,HH,hy]

omit [CompactSpace M] [Nonempty M] in
lemma continuous_joint_modifiedDatum {v:M → ℝ} (hv:Continuous v)
    (α D:ℝ) {B:ℝ → ℝ} (hB:Continuous B) :
    Continuous (fun q:ℝ×M=>modifiedDatum v α D q.1 B q.2) := by
  exact (hv.comp continuous_snd).add
    (continuous_fst.mul (hB.comp (((hv.comp continuous_snd).sub continuous_const).div_const D)))

lemma modified_active_bundle_limit {v:M → ℝ} (hv:Continuous v)
    {α D:ℝ} {B:ℝ → ℝ} (hB:Continuous B)
    {bk:ℕ → ℝ} {β:ℝ} (hb:Tendsto bk atTop (𝓝 β))
    {Qk:ℕ → TangentBundle 𝓘(ℝ,Model n) M} {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ:Tendsto Qk atTop (𝓝 Q))
    (ha:∀ᶠ k in atTop,(Qk k).2∈activeLogs (modifiedDatum v α D (bk k) B) (Qk k).1) :
    Q.2∈activeLogs (modifiedDatum v α D β B) Q.1 := by
  let : T2Space (TangentBundle 𝓘(ℝ,Model n) M) := bundle_totalSpace_t2
  have hx: Tendsto (fun k=>(Qk k).1) atTop (𝓝 Q.1) :=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).tendsto Q |>.comp hQ
  have hy:=contMDiff_riemannianExp.continuous.tendsto Q |>.comp hQ
  have hm:Q.2∈minimizingVectors Q.1 :=
    (isCompact_total_minimizingVectors (n := n) (M := M)).isClosed.mem_of_tendsto hQ (ha.mono (fun _ h=>h.1))
  apply (activeLogs_iff_minimum (continuous_modifiedDatum hv α D β hB)).mpr
  refine ⟨hm,fun y=>?_⟩
  have hφ:=continuous_joint_modifiedDatum hv α D hB
  have hleft:= (hφ.tendsto (β,riemannianExp Q.1 Q.2) |>.comp (hb.prodMk_nhds hy)).add
    ((hx.dist hy).pow 2 |>.div_const 2)
  have hright:= (hφ.tendsto (β,y) |>.comp (hb.prodMk_nhds tendsto_const_nhds)).add
    ((hx.dist (show Tendsto (fun _:ℕ=>y) atTop (𝓝 y) from tendsto_const_nhds)).pow 2 |>.div_const 2)
  exact le_of_tendsto_of_tendsto hleft hright (ha.mono (fun k hk=>
    ((activeLogs_iff_minimum (continuous_modifiedDatum hv α D (bk k) hB)).mp hk).2 y))

lemma modified_active_coordinates_limit {v:M → ℝ} (hv:Continuous v)
    {α D:ℝ} {B:ℝ → ℝ} (hB:Continuous B)
    {bk:ℕ → ℝ} {β:ℝ} (hb:Tendsto bk atTop (𝓝 β))
    {a:M} {xk pk:ℕ → Model n} {p:Model n}
    (hx:Tendsto xk atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto pk atTop (𝓝 p))
    (hxt:∀ᶠ k in atTop,xk k∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (ha:∀ᶠ k in atTop,chartFiberInverse a (xk k) (pk k)∈
      activeLogs (modifiedDatum v α D (bk k) B) ((extChartAt 𝓘(ℝ,Model n) a).symm (xk k))) :
    (show TangentSpace 𝓘(ℝ,Model n) a from p)∈activeLogs (modifiedDatum v α D β B) a := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have ht:(extChartAt 𝓘(ℝ,Model n) a a,p)∈χ.target :=
    (tangent_chart_target_iff _ _).mpr (mem_extChartAt_target a)
  have H:= (continuousAt_extChartAt_symm'' ht).tendsto.comp (hx.prodMk_nhds hp)
  have hcenter:χ.symm (extChartAt 𝓘(ℝ,Model n) a a,p)=
      (⟨a,p⟩:TangentBundle 𝓘(ℝ,Model n) M) := by
    rw [tangent_chart_symm_trivialization (mem_extChartAt_target a),chartFiberInverse_at_center]
    congr 1
    exact (extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)
  rw [hcenter] at H
  apply modified_active_bundle_limit hv hB hb H
  filter_upwards [hxt,ha] with k hk hka
  simp only [Function.comp_apply]
  rwa [tangent_chart_symm_trivialization hk]

end ParametricActive
end WeakMTWTransport

end
end

end OAI
