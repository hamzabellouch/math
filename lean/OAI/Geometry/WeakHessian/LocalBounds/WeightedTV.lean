import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile53
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma weighted_absolute_tendsto {ι : Type*} {l : Filter ι} {V W : X → ℝ}
    (hW : MemLp (fun x => W x*Real.exp (-V x)) 2 m) (o : X)
    (hcut : ∀ n,MemLp (fun x => W x*radialCutoff o n x) 2 m)
    {fs : ι → Lp ℝ 2 m} {f : Lp ℝ 2 m} (hlim : Tendsto fs l (𝓝 f))
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hfs : ∀ i,MemLp (fun x => fs i x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ᶠ i in l,‖(hfs i).toLp _‖ ≤ B) :
    Tendsto (fun i => ∫ x,|fs i x-f x| *W x ∂m) l (𝓝 0) := by
  let gs (i : ι) : Lp ℝ 2 m := (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).compLp norm_zero (fs i-f)
  have he (i : ι) : gs i =ᵐ[m] fun x => |fs i x-f x| := by
    filter_upwards [(lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).coeFn_compLp norm_zero (fs i-f),Lp.coeFn_sub (fs i) f] with x hx hy
    simpa only [gs,Function.comp_apply,hy,Pi.sub_apply,Real.norm_eq_abs] using hx
  have hg : Tendsto gs l (𝓝 (0:Lp ℝ 2 m)) := by
    have H := ((lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).continuous_compLp (p := (2:ℝ≥0∞)) (μ := m) norm_zero).continuousAt.tendsto.comp (hlim.sub (tendsto_const_nhds (x := f)))
    simpa only [gs,Function.comp_def,sub_self,LipschitzWith.compLp_zero] using H
  have hgw (i : ι) : MemLp (fun x => gs i x*Real.exp (V x)) 2 m := by
    apply MemLp.ae_eq (hf_Lp := ((hfs i).sub hf).norm)
    filter_upwards [he i] with x hx
    simp only [Pi.sub_apply,Real.norm_eq_abs,hx]
    rw [← sub_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hn (i : ι) : ‖(hgw i).toLp _‖ ≤ ‖(hfs i).toLp _‖+‖hf.toLp _‖ := by
    have hid : ‖(hgw i).toLp _‖ ≤ ‖(hfs i).toLp _-hf.toLp _‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hgw i).coeFn_toLp,(hfs i).coeFn_toLp,hf.coeFn_toLp,he i,Lp.coeFn_sub ((hfs i).toLp _) (hf.toLp _)] with x ha hb hc hd he'
      simp only [ha,he',Pi.sub_apply,hb,hc,hd,Real.norm_eq_abs,← sub_mul,abs_mul,abs_abs,abs_of_pos (Real.exp_pos _),le_refl]
    exact hid.trans (norm_sub_le _ _)
  have hz : MemLp (fun x => (0:Lp ℝ 2 m) x*Real.exp (V x)) 2 m := by
    exact MemLp.ae_eq (hf_Lp := MemLp.zero) (by filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx; simp only [Pi.zero_apply,hx,zero_mul])
  have H := weighted_pairing_tendsto hW o hcut hg hz hgw (B := B+‖hf.toLp _‖)
    (hB.mono fun i hi => (hn i).trans (add_le_add hi le_rfl))
  have hzi : (∫ x,(0:Lp ℝ 2 m) x*W x ∂m) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
    simp only [hx,Pi.zero_apply,zero_mul]
  rw [hzi] at H
  exact H.congr (fun i => integral_congr_ae ((he i).mono fun x hx => by rw [hx]))
end WeakHessian

end
end InlinedFile53

end OAI
