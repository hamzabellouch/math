import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ParametricShortLowerJets

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

lemma exists_parametric_short_lower_sequence {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} (L : ℝ≥0)
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) (hψ : ContDiffAt ℝ ∞ ψ (p,x))
    {pj : ℕ → P} {xj : ℕ → Model n} {tj : ℕ → ℝ} {f : ℕ → M → ℝ}
    (hp : Tendsto pj atTop (𝓝 p)) (hxx : Tendsto xj atTop (𝓝 x))
    (ht : Tendsto tj atTop (𝓝 0)) (htpos : ∀ᶠ i in atTop,0<tj i)
    (hlip : ∀ᶠ i in atTop,LipschitzWith L (f i))
    (hbelow : ∀ᶠ i in atTop,∀ w,ψ (pj i,w)≤f i ((extChartAt 𝓘(ℝ,Model n) a).symm w))
    (htouch : ∀ᶠ i in atTop,f i ((extChartAt 𝓘(ℝ,Model n) a).symm (xj i))=ψ (pj i,xj i)) :
    let z := fun i=>parametricShortForward a ψ ((pj i,tj i),xj i)
    ∃ U : ℕ → Model n → ℝ,
      (∀ᶠ i in atTop,ContDiffAt ℝ 2 (U i) (z i) ∧
        U i (z i)=hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm (z i)) ∧
        ∀ᶠ w in 𝓝 (z i),U i w≤hopfLax (tj i) (f i) ((extChartAt 𝓘(ℝ,Model n) a).symm w)) ∧
      Tendsto (fun i=>fderiv ℝ (U i) (z i)) atTop
        (𝓝 (fderiv ℝ (fun w=>ψ (p,w)) x)) ∧
      Tendsto (fun i=>fderiv ℝ (fderiv ℝ (U i)) (z i)) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ (fun w=>ψ (p,w))) x)) := by
  dsimp only
  let z := fun i=>parametricShortForward a ψ ((pj i,tj i),xj i)
  have hQ := (hp.prodMk_nhds ht).prodMk_nhds hxx
  have hzero : parametricShortForward a ψ ((p,0),x)=x := shortForward_zero hx
  have hz : Tendsto z atTop (𝓝 x) := by
    have H := (parametricShortForward_contDiffAt hx hψ).continuousAt.tendsto.comp hQ
    rwa [hzero] at H
  have hQz := (hp.prodMk_nhds ht).prodMk_nhds hz
  obtain ⟨r,hr,B,U,hB,hU,hBx,hBZ,hZB,hlo,hD,hH⟩ :=
    exists_parametric_short_lower_jets L hx hψ
  obtain ⟨V,hV,hVo,hV0⟩ := mem_nhds_iff.mp hlo
  have hVB := hQz.eventually (hVo.mem_nhds hV0)
  have hBK : ∀ᶠ i in atTop,B ((pj i,tj i),z i)=xj i := hQ.eventually hZB
  have hUC : ∀ᶠ i in atTop,ContDiffAt ℝ 2 U ((pj i,tj i),z i) :=
    hQz.eventually ((hU.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by norm_num))
  refine ⟨fun i w=>U ((pj i,tj i),w),?_,hD.comp hQz,hH.comp hQz⟩
  filter_upwards [hVB,hBK,hUC,htpos,hlip,hbelow,htouch] with i hVi hBi hUi hti hfi hbei hti'
  have htU := hUi.comp (z i) (contDiffAt_const.prodMk contDiffAt_id)
  have H := hV hVi hti (f i) hfi (fun w _=>hbei w)
  have Heq : f i ((extChartAt 𝓘(ℝ,Model n) a).symm (B ((pj i,tj i),z i)))=
      ψ (pj i,B ((pj i,tj i),z i)) := by rw [hBi]; exact hti'
  refine ⟨htU,H.2 Heq,?_⟩
  have hc : ContinuousAt (fun w:Model n=>((pj i,tj i),w)) (z i) :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards [hc.eventually (hVo.mem_nhds hVi)] with w hw
  exact (hV hw hti (f i) hfi (fun w _=>hbei w)).1

end WeakMTWTransport

end

end OAI
