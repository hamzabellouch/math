import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ShortSelectorNonsingularity
import OAI.Analysis.BiholderTransport.Regularity.MaximumDiagonal

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.good_centers {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (hBc:Continuous Bc)
    (hx:Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hz:Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    {C:ℝ} (hG:∀ᶠ k in atTop,∀d,
      fderiv ℝ (fderiv ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k))) d d ≤ C*‖d‖^2) :
    ∀ᶠ k in atTop,J.sampleCenter k (S.ν k)∉N := by
  let χ:=extChartAt 𝓘(ℝ,Model n) c
  obtain ⟨m,hm,H⟩:=actual_short_selector_injective_near (χ.map_source (mem_extChartAt_source c))
  have hτ:Tendsto (fun k=>(1-F.t k)*C) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,zero_mul] using ((tendsto_const_nhds (x := (1:ℝ))).sub F.time).mul_const C
  filter_upwards [hG,(hx.prodMk_nhds hz).eventually H,hτ.eventually (gt_mem_nhds hm)]
    with k hGk hnear hsmall
  let j:=J.sampleIndex k (S.ν k)
  let T:=J.sample k
  obtain ⟨hy,_,_,_,hY,_,hnot,_,_,_,_⟩:=T.samples j
  have hcontact:∀ᶠ z in 𝓝 (T.z j),
      chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c z=
      modifiedDatum v α D (F.b k) Bc (χ.symm (χ (T.Y z)))+
        chartCost c (χ.symm (χ (T.Y z))) z/(1-F.t k) := by
    filter_upwards [T.openRegion.mem_nhds (T.sampleInRegion j)] with z hz
    have he:χ.symm (χ (T.Y z))=T.Y z:=χ.left_inv (T.actual z hz).1
    rw [he]
    simpa only [chartCost,cost_symm] using ((T.actual z hz).2.2.1 (T.Y z)).mpr rfl
  have hd:∀ᶠ z in 𝓝 (T.z j),
      DifferentiableAt ℝ (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c) z := by
    filter_upwards [T.openRegion.mem_nhds (T.sampleInRegion j)] with z hz
    exact T.centerDifferentiable z hz
  have hinj:Function.Injective (fderiv ℝ (fun z=>χ (T.Y z)) (T.z j)) :=
    hnear (1-F.t k) (by linarith [(F.prefixTime k).2])
      (modifiedDatum v α D (F.b k) Bc) (continuous_modifiedDatum hv α D (F.b k) hBc)
      (fun z=>χ (T.Y z)) _ rfl hY hcontact hd C hsmall hGk
  apply hnot
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hinj)

end WeakMTWTransport

end

end OAI
