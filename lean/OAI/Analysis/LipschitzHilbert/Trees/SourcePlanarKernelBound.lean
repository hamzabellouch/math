import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridPlane
import OAI.Analysis.LipschitzHilbert.Trees.SourceKernelIntegral

namespace OAI

/-! Product reproducing-kernel majorants are controlled by the actual
strong maximal construction on the plane. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
open DyadicLineGrid

def normalizedLineEnvelope (c r x : ℝ) : ℝ := r⁻¹*lineEnvelope c r 1 x

theorem normalizedLineEnvelope_measurable (c r : ℝ) :
    Measurable (normalizedLineEnvelope c r) := by unfold normalizedLineEnvelope lineEnvelope; fun_prop

theorem normalizedLineEnvelope_nonneg (c r x : ℝ) (hr : 0<r) :
    0≤normalizedLineEnvelope c r x :=
  mul_nonneg (inv_nonneg.mpr hr.le) (lineEnvelope_nonneg _ _ _ _)

theorem normalizedLineEnvelope_integrable (c r : ℝ) (hr : 0<r) :
    Integrable (normalizedLineEnvelope c r) :=
  (integrable_lineEnvelope_one c r hr).const_mul _

def verticalKernelAverage (U : ℝ×ℝ → ℝ) (c r x : ℝ) : ℝ :=
  ∫ y, normalizedLineEnvelope c r y*U (x,y)

theorem verticalKernelAverage_measurable {U : ℝ×ℝ → ℝ} (hU : Measurable U) (c r : ℝ) :
    Measurable (verticalKernelAverage U c r) :=
  (((normalizedLineEnvelope_measurable c r).comp measurable_snd).mul hU).stronglyMeasurable.integral_prod_right'.measurable

theorem verticalKernelAverage_le_maximal {U : ℝ×ℝ → ℝ}
    (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hU0 : ∀ z, 0≤U z) (hUb : ∀ z, ‖U z‖≤B)
    (c r : ℝ) (hr : 0<r) :
    ∀ᵐ z ∂volume.prod volume, |z.2-c|≤r →
      verticalKernelAverage U c r z.1≤96*threeVerticalMaximal U z := by
  have hP : MeasurableSet {z : ℝ×ℝ | |z.2-c|≤r →
      verticalKernelAverage U c r z.1≤96*threeVerticalMaximal U z} := by
    simp only [imp_iff_not_or]
    change MeasurableSet ({z : ℝ×ℝ | |z.2-c|≤r}ᶜ ∪
      {z | verticalKernelAverage U c r z.1≤96*threeVerticalMaximal U z})
    exact (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-c|) by fun_prop)
      measurable_const).compl.union
      (measurableSet_le ((verticalKernelAverage_measurable hUm c r).comp measurable_fst)
        ((threeVerticalMaximal_measurable hUm).const_mul 96))
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  filter_upwards [hU2.integrable_sq.prod_right_ae] with x hx
  have hxm : Measurable (fun y => U (x,y)) := hUm.comp (measurable_const.prodMk measurable_id)
  have hx2 : MemLp (fun y => U (x,y)) 2 volume :=
    (memLp_two_iff_integrable_sq hxm.aestronglyMeasurable).mpr hx
  filter_upwards [kernel_integral_le_threeGridMaximal (fun y => U (x,y)) hxm hx2 B
    (fun y => hU0 (x,y)) (fun y => hUb (x,y))] with y hy
  intro hyc
  exact hy c r hr hyc

/-- The product kernel is bounded on its central rectangle by one
strong maximal function, with constants independent of both scales. -/
theorem planar_kernel_le_strongMaximal {U : ℝ×ℝ → ℝ}
    (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ z, 0≤U z) (hUb : ∀ z, ‖U z‖≤B)
    (cx cy rx ry : ℝ) (hrx : 0<rx) (hry : 0<ry) :
    ∀ᵐ z ∂volume.prod volume, |z.1-cx|≤rx ∧ |z.2-cy|≤ry →
      (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume)≤9216*threeStrongMaximal U z := by
  let V := threeVerticalMaximal U
  have hVm : Measurable V := threeVerticalMaximal_measurable hUm
  have hV2 : MemLp V 2 (volume.prod volume) := (threeVerticalMaximal_energy hUm hU2).1
  have hV0 (z) : 0≤V z := threeVerticalMaximal_nonneg U z
  have hVb (z) : ‖V z‖≤3*B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hV0 z)]
    exact threeVerticalMaximal_bound U B hB (fun z => by simpa only [Real.norm_eq_abs] using hUb z) z
  have hki : Integrable (fun p : ℝ×ℝ =>
      normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p)
      (volume.prod volume) :=
    ((normalizedLineEnvelope_integrable cx rx hrx).mul_prod
      (normalizedLineEnvelope_integrable cy ry hry)).mul_bdd
      hUm.aestronglyMeasurable (Filter.Eventually.of_forall hUb)
  have houter : Integrable (fun x => normalizedLineEnvelope cx rx x*verticalKernelAverage U cy ry x) := by
    have h := hki.integral_prod_left
    simpa only [verticalKernelAverage,Prod.fst,Prod.snd,mul_assoc,integral_const_mul] using h
  have heq : (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
      ∂volume.prod volume)=∫ x, normalizedLineEnvelope cx rx x*verticalKernelAverage U cy ry x := by
    rw [integral_prod _ hki]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [verticalKernelAverage,←integral_const_mul,mul_assoc])
  have hvertical := verticalKernelAverage_le_maximal hUm hU2 B hU0 hUb cy ry hry
  have hPv : MeasurableSet {z : ℝ×ℝ | |z.2-cy|≤ry →
      verticalKernelAverage U cy ry z.1≤96*V z} := by
    simp only [imp_iff_not_or]
    change MeasurableSet ({z : ℝ×ℝ | |z.2-cy|≤ry}ᶜ ∪
      {z | verticalKernelAverage U cy ry z.1≤96*V z})
    exact (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-cy|) by fun_prop)
      measurable_const).compl.union
      (measurableSet_le ((verticalKernelAverage_measurable hUm cy ry).comp measurable_fst)
        (hVm.const_mul 96))
  have hvertical' : ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
      |y-cy|≤ry → verticalKernelAverage U cy ry x≤96*V (x,y) :=
    (Measure.ae_ae_comm hPv).mp (Measure.ae_ae_of_ae_prod hvertical)
  have hP : MeasurableSet {z : ℝ×ℝ | |z.1-cx|≤rx ∧ |z.2-cy|≤ry →
      (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume)≤9216*threeStrongMaximal U z} := by
    simp only [imp_iff_not_or]
    change MeasurableSet (({z : ℝ×ℝ | |z.1-cx|≤rx} ∩ {z | |z.2-cy|≤ry})ᶜ ∪
      {z | (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume)≤9216*threeStrongMaximal U z})
    exact ((measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.1-cx|) by fun_prop)
      measurable_const).inter
      (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-cy|) by fun_prop)
        measurable_const)).compl.union
        (measurableSet_le measurable_const ((threeStrongMaximal_measurable hUm).const_mul 9216))
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  apply (Measure.ae_ae_comm hP).mpr
  filter_upwards [hvertical',hV2.integrable_sq.prod_left_ae] with y hy hy2
  have hym : Measurable (fun x => V (x,y)) := hVm.comp (measurable_id.prodMk measurable_const)
  have hyLp : MemLp (fun x => V (x,y)) 2 volume :=
    (memLp_two_iff_integrable_sq hym.aestronglyMeasurable).mpr hy2
  filter_upwards [kernel_integral_le_threeGridMaximal (fun x => V (x,y)) hym hyLp (3*B)
    (fun x => hV0 (x,y)) (fun x => hVb (x,y))] with x hx
  rintro ⟨hxc,hyc⟩
  have hVK : Integrable (fun s => normalizedLineEnvelope cx rx s*V (s,y)) :=
    (normalizedLineEnvelope_integrable cx rx hrx).mul_bdd hym.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => hVb (s,y)))
  calc
    _ = ∫ s, normalizedLineEnvelope cx rx s*verticalKernelAverage U cy ry s := heq
    _ ≤ 96*∫ s, normalizedLineEnvelope cx rx s*V (s,y) := by
      rw [←integral_const_mul]
      apply integral_mono_ae houter (hVK.const_mul 96)
      filter_upwards [hy] with s hs
      have h := mul_le_mul_of_nonneg_left (hs hyc) (normalizedLineEnvelope_nonneg cx rx s hrx)
      nlinarith only [h]
    _ ≤ 96*(96*threeGridMaximal (fun s => V (s,y)) x) :=
      mul_le_mul_of_nonneg_left (hx cx rx hrx hxc) (by norm_num)
    _ = _ := by change _ = 9216*threeHorizontalMaximal V (x,y); rw [threeHorizontalMaximal_eq_line]; ring

end LipschitzHilbert

end

end OAI
