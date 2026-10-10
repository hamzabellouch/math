import OAI.Analysis.LipschitzHilbert.Fourier.LineLpDerivative

namespace OAI

/-! The strong product rule needed for the sampling conjugation. A
uniform operator bound replaces differentiability in operator norm. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem hasDerivAt_strong_operator_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ℝ → E →L[ℝ] E) (f : ℝ → E) (t : ℝ) (f' d : E) (B : ℝ)
    (hb : ∀ᶠ s in 𝓝 t, ‖C s‖≤B)
    (hf : HasDerivAt f f' t)
    (hcont : ContinuousAt (fun s => C s f') t)
    (hfixed : HasDerivAt (fun s => C s (f t)) d t) :
    HasDerivAt (fun s => C s (f s)) (d+C t f') t := by
  have hzero : Tendsto (fun s => C s (slope f t s-f')) (𝓝[≠] t) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun s => (C s).le_opNorm (slope f t s-f'))
    have hz : Tendsto (fun s => ‖slope f t s-f'‖) (𝓝[≠] t) (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hf.tendsto_slope.sub_const f').norm
    apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (hb.filter_mono nhdsWithin_le_nhds |>.mono fun s hs =>
        mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    simpa only [mul_zero] using hz.const_mul B
  have hsum := (hzero.add (hcont.tendsto.mono_left nhdsWithin_le_nhds)).add hfixed.tendsto_slope
  apply hasDerivAt_iff_tendsto_slope.mpr
  have heq (s : ℝ) : slope (fun r => C r (f r)) t s=
      C s (slope f t s-f')+C s f'+slope (fun r => C r (f t)) t s := by
    simp only [slope_def_module,map_sub,map_smul,smul_sub]
    abel
  simpa only [←heq,zero_add,add_comm (C t f') d] using hsum

end LipschitzHilbert.PacketRepresentation

end

end OAI
