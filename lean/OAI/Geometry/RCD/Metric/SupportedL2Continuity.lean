import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # L2 continuity of bounded families with a common finite support -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X I : Type*} [MeasurableSpace X] (μ : Measure X)

theorem supported_L2_tendsto {l : Filter I} [l.IsCountablyGenerated]
    {s : Set X} (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    (u : I → Lp ℝ 2 μ) (v : Lp ℝ 2 μ) (F : I → X → ℝ) (f : X → ℝ)
    (hu : ∀ i, u i =ᵐ[μ] F i) (hv : v =ᵐ[μ] f)
    {A : ℝ} (hA : 0 ≤ A) (hF : ∀ i x, |F i x| ≤ A) (hf : ∀ x, |f x| ≤ A)
    (hF0 : ∀ i x, x ∉ s → F i x = 0) (hf0 : ∀ x, x ∉ s → f x = 0)
    (hc : ∀ x ∈ s, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto u l (𝓝 v) := by
  let B := s.indicator (fun _ : X => (2*A)^2)
  have hB : Integrable B μ := (integrable_indicator_iff hs).mpr (integrableOn_const hfin)
  have hFm (i : I) : MemLp (F i) 2 μ := (memLp_congr_ae (hu i)).mp (Lp.memLp (u i))
  have hfm : MemLp f 2 μ := (memLp_congr_ae hv).mp (Lp.memLp v)
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, (F i x-f x)^2 ≤ B x := by
    exact Eventually.of_forall fun i => Eventually.of_forall fun x => by
      by_cases hxs : x ∈ s
      · dsimp only [B]
        rw [indicator_of_mem hxs]
        have hh := (abs_sub (F i x) (f x)).trans (add_le_add (hF i x) (hf x))
        nlinarith [sq_abs (F i x-f x),abs_nonneg (F i x-f x)]
      · simp only [B,indicator_of_notMem hxs,hF0 i x hxs,hf0 x hxs,sub_self,
          zero_pow (by norm_num : 2 ≠ 0),le_refl]
  have ht : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x)) := by
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ s
      · exact hc x hx
      · simp only [hF0 _ x hx,hf0 x hx]
        exact tendsto_const_nhds
  have hleft (i : I) : (hFm i).toLp (F i) = u i :=
    Lp.ext ((hFm i).coeFn_toLp.trans (hu i).symm)
  have hright : hfm.toLp f = v := Lp.ext (hfm.coeFn_toLp.trans hv.symm)
  simpa only [hleft,hright] using
    L2Differentiation.toLp_tendsto_of_dominated μ hFm hfm B hB hb ht

end RegularPointCoordinates

end

end OAI
