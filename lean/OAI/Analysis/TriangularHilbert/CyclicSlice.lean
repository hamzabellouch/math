import OAI.Analysis.TriangularHilbert.SampledOutput

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
noncomputable section

def CubicSliceGood (B C : ℝ×ℝ → ℂ) (z : ℝ×ℝ) : Prop :=
  AEStronglyMeasurable (fun c => B (z.2,c)) volume ∧
  AEStronglyMeasurable (fun c => C (c,z.1)) volume ∧
  Integrable (fun c : ℝ => ‖B (z.2,c)‖^3) ∧
  Integrable (fun c : ℝ => ‖C (c,z.1)‖^3)

lemma ae_cubicSliceGood (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    ∀ᵐ z : ℝ×ℝ, CubicSliceGood B C z := by
  have hb := hB.aestronglyMeasurable.prodMk_left
  have hc := hC.aestronglyMeasurable.prodMk_right
  have hbi := (hB.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).prod_right_ae
  have hci := (hC.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).prod_left_ae
  filter_upwards [quasiMeasurePreserving_snd.ae hb,quasiMeasurePreserving_fst.ae hc,
    quasiMeasurePreserving_snd.ae hbi,quasiMeasurePreserving_fst.ae hci] with z hzB hzC hiB hiC
  exact ⟨hzB,hzC,hiB,hiC⟩

lemma hardKernel_shift_support {r R : ℝ} (hr : r ≤ R) (a c : ℝ)
    (hc : c ∉ Set.Icc (-(R+|a|)) (R+|a|)) : hardKernel r R (a+c) = 0 := by
  have hR : R < |a+c| := by
    by_contra hR
    apply hc
    apply abs_le.mp
    have hh : |c| ≤ |a+c|+|a| := by
      calc
        |c| = |(a+c)-a| := by congr 1; ring
        _ ≤ |a+c|+|a| := abs_sub _ _
    linarith [le_of_not_gt hR]
  simp only [hardKernel,hr.trans_lt hR,hR,ite_true,sub_self,zero_div]

lemma CubicSliceGood.integrable_hard {B C : ℝ×ℝ → ℂ} {z : ℝ×ℝ} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    Integrable (fun c : ℝ => B (z.2,c)*C (c,z.1)*(hardKernel r R (z.1+z.2+c):ℂ)) := by
  apply integrable_product_bounded_kernel _ _ _ hz.1 hz.2.1
    ((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)) hz.2.2.1 hz.2.2.2
    (Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)) measurableSet_Icc isCompact_Icc.measure_ne_top
    (show 0 ≤ 1/r by positivity) (fun c => abs_hardKernel_le hr hR _)
  exact hardKernel_shift_support hR (z.1+z.2)

lemma tendsto_cyclicKernelOutput_of_cubic_dom (B C : ℝ×ℝ → ℂ) (F G : ℕ → ℝ×ℝ → ℂ)
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n))
    {D E : ℝ×ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖F n z‖^3 ≤ D z) ∧ Tendsto (fun n => F n z) atTop (𝓝 (B z)))
    (hc : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖G n z‖^3 ≤ E z) ∧ Tendsto (fun n => G n z) atTop (𝓝 (C z))) :
    ∀ᵐ z : ℝ×ℝ, ∀ r R : ℝ, 0 < r → r ≤ R →
      Tendsto (fun n => cyclicKernelOutput (F n) (G n) (hardKernel r R) z) atTop
        (𝓝 (cyclicKernelOutput B C (hardKernel r R) z)) := by
  have hb' := ae_ae_of_ae_prod hb
  have hc' := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hc)
  filter_upwards [quasiMeasurePreserving_snd.ae hb',quasiMeasurePreserving_fst.ae hc',
    quasiMeasurePreserving_snd.ae hD.prod_right_ae,quasiMeasurePreserving_fst.ae hE.prod_left_ae]
    with z hzb hzc hzD hzE
  intro r R hr hR
  apply tendsto_integral_product_bounded_kernel _ _ _ _ _
    (s := Set.Icc (-(R+|z.1+z.2|)) (R+|z.1+z.2|)) (L := 1/r)
    (fun n => ((hF n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun n => ((hG n).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    ((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)) hzD hzE
  · filter_upwards [hzb,hzc] with c hb hc
    exact fun n => ⟨hb.1 n,hc.1 n⟩
  · filter_upwards [hzb,hzc] with c hb hc
    exact ⟨hb.2,hc.2⟩
  · exact measurableSet_Icc
  · exact isCompact_Icc.measure_ne_top
  · exact show 0 ≤ 1/r by positivity
  · exact fun c => abs_hardKernel_le hr hR _
  · exact hardKernel_shift_support hR (z.1+z.2)
end
end TriangularHilbert.Heat
end

end OAI
