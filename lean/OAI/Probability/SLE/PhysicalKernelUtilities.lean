import Mathlib
import OAI.Probability.SLE.ChartMeasurability
import OAI.Probability.SLE.InteriorDiskProof
import OAI.Probability.SLE.PhysicalTransport

namespace OAI

/-! Physical Kernel Utilities for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance physicalDiskKernelTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance physicalDiskKernelTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
local instance physicalDiskKernelChartMeasurableSpace : MeasurableSpace C(upperHalfPlane,ℂ) := borel _
local instance physicalDiskKernelChartBorelSpace : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩

def sourcePhysicalDiskKernel (p : SourceDiskParameter × C(ℝ≥0,ℂ)) : ℝ :=
  if ∃ t : ℝ≥0, p.1.1.2 ∈ survivingDomain p.2 t ∧
    ∃ h : p.2 t ∈ upperHalfPlane, p.1.2.2 < ‖p.1.1.1 ⟨p.2 t,h⟩-p.1.2.1‖ then 1 else 0

lemma sourcePhysicalDiskKernel_measurable : Measurable sourcePhysicalDiskKernel :=
  Measurable.ite source_physical_disk_kernel_open.measurableSet measurable_const measurable_const

lemma sourcePhysicalDiskKernel_norm_le (p : SourceDiskParameter × C(ℝ≥0,ℂ)) :
    ‖sourcePhysicalDiskKernel p‖ ≤ 1 := by
  unfold sourcePhysicalDiskKernel
  split_ifs <;> norm_num

lemma source_physical_exit_open (z : ℂ) (R : ℝ) :
    IsOpen {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R < dist (p.1 (p.2+t)) z} := by
  have ht (t : ℝ≥0) : IsOpen {p : C(ℝ≥0,ℂ) × ℝ≥0 |
      z ∈ survivingDomain p.1 (p.2+t) ∧ R < dist (p.1 (p.2+t)) z} := by
    have hc : Continuous (fun p : C(ℝ≥0,ℂ) × ℝ≥0 => (p.1,p.2+t)) :=
      continuous_fst.prodMk (continuous_snd.add continuous_const)
    exact (source_survival_open.preimage (hc.prodMk continuous_const)).inter
      (isOpen_lt continuous_const ((continuous_eval.comp hc).dist continuous_const))
  simpa only [ofPred_exists] using isOpen_iUnion ht

lemma source_restarted_interior_dense
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgm : Measurable (sourceTracePath γ (fun ω => (hw ω).1)))
    (β : Ω → C(ℝ≥0,ℂ)) (hβm : Measurable β)
    (hlaw : P.map β = P.map (sourceTracePath γ (fun ω => (hw ω).1))) :
    ∀ᵐ ω ∂P, SourcePathInteriorDense (β ω) := by
  apply (ae_map_iff hβm.aemeasurable source_path_interior_dense_measurable).mp
  rw [hlaw]
  apply (ae_map_iff hgm.aemeasurable source_path_interior_dense_measurable).mpr
  exact Eventually.of_forall fun ω => sourceInteriorTraceDensity_proved
    (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)
    (continuous_const.mul (hc ω)) (hw ω)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_firsthit_inverse_access
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hUc : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (s τ : ℝ≥0) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : Metric.closedBall z r ⊆ survivingDomain γ s) (hsτ : s ≤ τ)
    (hhit : dist (γ τ) z = r)
    (hfirst : ∀ t ∈ Ico s τ, dist (γ t) z ≠ r)
    (hz : z ∈ survivingDomain γ τ) :
    ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 1) ∧ η 0 = 0 ∧
      η 1 = G τ z - (U τ : ℂ) ∧
      (∀ v ∈ Ioc 0 1, 0 < (η v).im) ∧
      (∀ v ∈ Ioc 0 1, ‖F τ (η v + (U τ : ℂ))-z‖ ≤ r) := by
  let α : ℝ → ℂ := fun v => (1-v) • γ τ + v • z
  let f : ℝ → ℂ := fun v => G τ (α v) - (U τ : ℂ)
  let η := Function.update f 0 0
  have hα : Continuous α := by dsimp [α]; fun_prop
  have hαD := (sourceFirstHitPhysicalAccess γ h.1 s τ z r hr hfree hsτ hhit hfirst hz).2.2
  have hf : ContinuousOn f (Icc 0 1 \ {0}) := by
    refine ((h.2.2.2.1 τ).continuousOn.comp hα.continuousOn ?_).sub continuousOn_const
    intro v hv
    exact hαD v ⟨lt_of_le_of_ne hv.1.1 (Ne.symm hv.2),hv.1.2⟩
  have hη : ContinuousOn η (Icc 0 1) := by
    apply continuousOn_update_iff.mpr
    refine ⟨hf,fun _ => ?_⟩
    apply (sourceFirstHitChartAccess_proved U γ G F hUc h s τ z r hr hfree hsτ hhit hfirst hz).mono_left
    apply nhdsWithin_mono
    intro v hv
    exact lt_of_le_of_ne hv.1.1 (Ne.symm hv.2)
  have hηv (v : ℝ) (hv : v ∈ Ioc 0 1) : η v = f v :=
    Function.update_of_ne (ne_of_gt hv.1) _ _
  refine ⟨η,hη,by simp [η],?_,?_,?_⟩
  · rw [hηv 1 (by norm_num)]
    simp [f,α]
  · intro v hv
    rw [hηv v hv]
    simpa only [f,α,upperHalfPlane,Set.mem_ofPred_eq,sub_im,ofReal_im,sub_zero] using h.2.2.2.2.2.1 τ (hαD v hv)
  · intro v hv
    rw [hηv v hv]
    simp only [f,sub_add_cancel,h.2.2.2.2.2.2.2.1 τ (α v) (hαD v hv)]
    simpa only [dist_eq_norm] using
      (show dist (α v) z < r from radialAccess_mem_ball (γ τ) z r hr hhit v hv).le

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma source_physical_exit_interior_inclusion
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (β : C(ℝ≥0,ℂ))
    (hdense : SourcePathInteriorDense β)
    (hid : ∀ t : ℝ≥0, β t ∈ upperHalfPlane → γ (T+t) = F T (β t+(U T:ℂ)))
    (z : ℂ) (R : ℝ) (hR : dist (γ T) z ≤ R) :
    (∃ t : ℝ≥0, z ∈ survivingDomain γ (T+t) ∧ R < dist (γ (T+t)) z) →
    ∃ t : ℝ≥0, G T z-(U T:ℂ) ∈ survivingDomain β t ∧
      ∃ _ht : β t ∈ upperHalfPlane, R < ‖F T (β t+(U T:ℂ))-z‖ := by
  rintro ⟨t,hl,he⟩
  have ht : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := le_antisymm (not_lt.mp hn) bot_le
    simp only [ht0,add_zero] at he
    exact (not_lt_of_ge hR) he
  have hc : Continuous (fun u : ℝ≥0 => dist (γ (T+u)) z) :=
    (h.1.comp (continuous_const.add continuous_id)).dist continuous_const
  have hevent : {u : ℝ≥0 | R < dist (γ (T+u)) z} ∈ 𝓝 t :=
    (isOpen_lt continuous_const hc).mem_nhds he
  obtain ⟨b,hbt,hb⟩ := exists_Ioc_subset_of_mem_nhds hevent ⟨0,ht⟩
  obtain ⟨u,hu,hupos⟩ := hdense b t hbt
  have hlu : z ∈ survivingDomain γ (T+u) :=
    survivingDomain_antitone γ (by simpa only [add_comm] using add_le_add_left hu.2.le T) hl
  refine ⟨u,source_stopped_live_transfer h T u β (fun v _ => hid v) z hlu,hupos,?_⟩
  rw [← hid u hupos,← dist_eq_norm]
  exact hb ⟨hu.1,hu.2.le⟩
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance finitePhysicalDiskTargetTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance finitePhysicalDiskTargetTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
local instance finitePhysicalDiskTargetDriverMeasurableSpace : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance finitePhysicalDiskTargetDriverBorelSpace : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance finitePhysicalDiskTargetChartMeasurableSpace : MeasurableSpace C(upperHalfPlane,ℂ) := borel _
local instance finitePhysicalDiskTargetChartBorelSpace : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩
 

def SourceFinitePhysicalDiskTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_m : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (_hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (_hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (z : ℂ) (r : ℝ), 0 < r →
  ∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
    (∀ ω ∈ A, ∃ s : ℝ≥0, s ≤ τ ω ∧
      Metric.closedBall z r ⊆ survivingDomain (γ ω) s ∧
      dist (γ ω (τ ω)) z = r ∧
      (∀ t ∈ Ico s (τ ω), dist (γ ω t) z ≠ r) ∧
      z ∈ survivingDomain (γ ω) (τ ω)) →
  ∀ L : ℝ, 1 ≤ L →
    ∀ᵐ ω ∂P, ω ∈ A →
      P[(fun ω => if ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) (τ ω+t) ∧
        L*r < dist (γ ω (τ ω+t)) z then (1 : ℝ) else 0) | hτ.measurableSpace] ω ≤ C*L^(-c)

lemma source_physical_kernel_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgm : Measurable gp)
    (Y : SourceDiskParameter) (Ψ : ℂ → ℂ)
    (hΨ : ∀ w : upperHalfPlane, Y.1.1 w = Ψ w)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : P {v | ∃ t : ℝ≥0, Y.1.2 ∈ survivingDomain (gp v) t ∧
      0 < (gp v t).im ∧ Y.2.2 < ‖Ψ (gp v t)-Y.2.1‖} ≤ ENNReal.ofReal b) :
    (∫ p, sourcePhysicalDiskKernel (Y,p) ∂P.map gp) ≤ b := by
  let S : Set Ω := {v | ∃ t : ℝ≥0, Y.1.2 ∈ survivingDomain (gp v) t ∧
      0 < (gp v t).im ∧ Y.2.2 < ‖Ψ (gp v t)-Y.2.1‖}
  have he (v : Ω) : sourcePhysicalDiskKernel (Y,gp v) = S.indicator (fun _ => (1:ℝ)) v := by
    unfold sourcePhysicalDiskKernel
    have hi : (∃ t : ℝ≥0, Y.1.2 ∈ survivingDomain (gp v) t ∧
        ∃ ht : gp v t ∈ upperHalfPlane,
          Y.2.2 < ‖Y.1.1 ⟨gp v t,ht⟩-Y.2.1‖) ↔ v ∈ S := by
      constructor
      · rintro ⟨t,ht,hi,hf⟩
        exact ⟨t,ht,hi,by simpa only [hΨ] using hf⟩
      · rintro ⟨t,ht,hi,hf⟩
        exact ⟨t,ht,hi,by simpa only [hΨ] using hf⟩
    simp only [hi,Set.indicator_apply]
  have hfun : Measurable (fun p : C(ℝ≥0,ℂ) => sourcePhysicalDiskKernel (Y,p)) :=
    sourcePhysicalDiskKernel_measurable.comp (measurable_const.prodMk measurable_id)
  have hS : MeasurableSet S := by
    have hh := measurableSet_lt (measurable_const (a := (0:ℝ))) (hfun.comp hgm)
    convert hh using 1
    ext v
    change v ∈ S ↔ 0 < sourcePhysicalDiskKernel (Y,gp v)
    rw [he]
    by_cases hv : v ∈ S <;> simp [hv]
  have hKi : (∫ p, sourcePhysicalDiskKernel (Y,p) ∂P.map gp) = (P S).toReal := by
    rw [integral_map hgm.aemeasurable hfun.aestronglyMeasurable]
    simp_rw [he]
    simp only [integral_indicator_const _ hS,smul_eq_mul,mul_one,measureReal_def]
  rw [hKi]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbound |>.trans
    (le_of_eq (ENNReal.toReal_ofReal hb))

lemma source_firsthit_kernel_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgm : Measurable gp)
    (U : ℝ≥0 → ℝ) (hU : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ) (hw : IsCapacityTwoWitness U γ G F)
    (s T : ℝ≥0) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hs : s ≤ T) (hfree : Metric.closedBall z r ⊆ survivingDomain γ s)
    (hhit : dist (γ T) z = r)
    (hfirst : ∀ t ∈ Ico s T, dist (γ t) z ≠ r) (hz : z ∈ survivingDomain γ T)
    (ψ : C(upperHalfPlane,ℂ)) (hψ : ∀ w, ψ w = F T (w+(U T:ℂ)))
    (L b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ upperHalfPlane → InjOn Ψ upperHalfPlane →
      ∀ η : ℝ → ℂ, ContinuousOn η (Icc 0 1) → η 0 = 0 → Ψ (η 1) = z →
      (∀ v ∈ Ioc 0 1, 0 < (η v).im) → (∀ v ∈ Ioc 0 1, ‖Ψ (η v)-z‖ ≤ r) →
      P {v | ∃ t : ℝ≥0, η 1 ∈ survivingDomain (gp v) t ∧
        0 < (gp v t).im ∧ L*r < ‖Ψ (gp v t)-z‖} ≤ ENNReal.ofReal b) :
    (∫ p, sourcePhysicalDiskKernel (((ψ,G T z-(U T:ℂ)),(z,L*r)),p) ∂P.map gp) ≤ b := by
  let Ψ : ℂ → ℂ := fun w => F T (w+(U T:ℂ))
  have hmap : MapsTo (fun w : ℂ => w+(U T:ℂ)) upperHalfPlane upperHalfPlane := by
    intro w hw
    simpa [upperHalfPlane] using hw
  have hΨd : DifferentiableOn ℂ Ψ upperHalfPlane :=
    (hw.2.2.2.2.1 T).comp (differentiable_id.add_const _).differentiableOn hmap
  have hΨi : InjOn Ψ upperHalfPlane := by
    intro a ha b hb he
    have ha' := hw.2.2.2.2.2.2.2.2.1 T (a+(U T:ℂ)) (hmap ha)
    have hb' := hw.2.2.2.2.2.2.2.2.1 T (b+(U T:ℂ)) (hmap hb)
    have hh := congrArg (G T) he
    dsimp only [Ψ] at hh
    rw [ha',hb'] at hh
    exact add_right_cancel hh
  obtain ⟨η,hη,hη0,hη1,hηup,hηpath⟩ := source_firsthit_inverse_access
    hU hw s T z r hr hfree hs hhit hfirst hz
  have hq : Ψ (η 1) = z := by
    rw [hη1]
    simp only [Ψ,sub_add_cancel,hw.2.2.2.2.2.2.2.1 T z hz]
  have hprob := hbound Ψ hΨd hΨi η hη hη0 hq hηup hηpath
  apply source_physical_kernel_mean_le gp hgm _ Ψ hψ b hb
  simpa only [hη1] using hprob

lemma source_physical_exit_measurable {Ω : Type*} [MeasurableSpace Ω]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgp : Measurable gp)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (z : ℂ) (R : ℝ) :
    MeasurableSet {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (gp ω) (τ ω+t) ∧
      R < dist (gp ω (τ ω+t)) z} := by
  have hp : Measurable (fun ω => (gp ω,τ ω)) := hgp.prodMk hτ
  have he : MeasurableSet {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R < dist (p.1 (p.2+t)) z} :=
    (source_physical_exit_open z R).measurableSet
  have hh := he.preimage hp
  simpa only [Set.preimage_ofPred_eq] using hh

theorem sourceFinitePhysicalDisk_proved : SourceFinitePhysicalDiskTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,hC,hc,hbound⟩ := source_interior_disk_unnormalized κ hκ hκ8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω m P hP B hB hm hBc γ G F hw τ hτ z r hr A hA hgeom L hL
  let : IsProbabilityMeasure P := hP
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  obtain ⟨Φ,hΦm,hΦeq,hΦ⟩ := sourceStoppedTraceLaw κ (by linarith) hκ8 B hB hm hBc γ G F hw
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hBc ω) := funext fun ω => (hΦeq ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable _ hm)
  let ν := P.map gp
  let : IsProbabilityMeasure ν := inferInstance
  have hγsle : IsOrdinaryChordalSLE κ γ P :=
    ⟨fun t => (continuous_eval_const t).measurable.comp hgm,
      B,hB,Eventually.of_forall fun ω => ⟨G ω,F ω,hw ω⟩⟩
  obtain ⟨hlaw,hid⟩ := hΦ τ hτ
  let rp := sourceRestartDriverPath B hBc τ
  let β (ω : Ω) := Φ (rp ω)
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hBc (stopping_time_measurable_nnreal hτ)))
  have hβm : Measurable β := hΦm.comp hrm
  have hβlaw : P.map β = ν := by simpa only [Measure.restrict_univ,measure_univ,one_smul] using hlaw univ MeasurableSet.univ
  have hdense : ∀ᵐ ω ∂P, SourcePathInteriorDense (β ω) :=
    source_restarted_interior_dense B hBc κ γ G F hw hgm β hβm hβlaw
  let ξ (ω : Ω) :=
    (if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0) -
      (Real.sqrt κ * B (τ ω) ω : ℝ)
  let Y (ω : Ω) : SourceDiskParameter :=
    ((sourceStoppedInversePath B κ γ G F hw τ ω,ξ ω),(z,L*r))
  have hξm : Measurable[hτ.measurableSpace] ξ := by
    have hGm := source_killedChart_stopped_measurable hm hBc κ γ G F hw z τ hτ
    have hBm := measurable_stoppedValue
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hBc) hτ
    exact hGm.sub (Complex.measurable_ofReal.comp (measurable_const.mul hBm))
  have hYm : Measurable[hτ.measurableSpace] Y :=
    ((source_stopped_inversePath_measurable B hm hBc κ γ G F hw τ hτ).prodMk hξm).prodMk measurable_const
  let H (ω : Ω) := sourcePhysicalDiskKernel (Y ω,β ω)
  let K (ω : Ω) := ∫ p, sourcePhysicalDiskKernel (Y ω,p) ∂ν
  have hHm : Measurable H := sourcePhysicalDiskKernel_measurable.comp
    ((hYm.mono hτ.measurableSpace_le le_rfl).prodMk hβm)
  have hHi : Integrable H P :=
    (integrable_const (1:ℝ)).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun ω => sourcePhysicalDiskKernel_norm_le (Y ω,β ω))
  have hcond : P[H | hτ.measurableSpace] =ᵐ[P] K :=
    source_parameter_condExp hτ.measurableSpace_le hβm hYm hlaw sourcePhysicalDiskKernel
      sourcePhysicalDiskKernel_measurable sourcePhysicalDiskKernel_norm_le
  have hmean (ω : Ω) (hω : ω ∈ A) : K ω ≤ C*L^(-c) := by
    obtain ⟨s,hs,hfree,hhit,hfirst,hz⟩ := hgeom ω hω
    dsimp only [K,Y,ξ]
    rw [ite_eq_left hz]
    apply source_firsthit_kernel_mean_le gp hgm (fun t => Real.sqrt κ*B t ω)
      (continuous_const.mul (hBc ω)) (γ ω) (G ω) (F ω) (hw ω)
      s (τ ω) z r hr hs hfree hhit hfirst hz _ (fun _ => rfl)
      L (C*L^(-c)) (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
    intro Ψ hΨd hΨi η hη hη0 hq hηup hηpath
    exact hbound Ω m P hP γ hγsle Ψ hΨd hΨi z r hr η 1 (by norm_num)
      hη hη0 hq hηup hηpath L hL
  let E : Set Ω := {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) (τ ω+t) ∧
      L*r < dist (γ ω (τ ω+t)) z}
  let f : Ω → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E :=
    source_physical_exit_measurable gp hgm τ (stopping_time_measurable_nnreal hτ) z (L*r)
  have hfi : Integrable f P := (integrable_const (1:ℝ)).indicator hE
  have hAi : Integrable (A.indicator f) P := hfi.indicator (hτ.measurableSpace_le _ hA)
  have hAH : Integrable (A.indicator H) P := hHi.indicator (hτ.measurableSpace_le _ hA)
  have hdom : A.indicator f ≤ᵐ[P] A.indicator H := by
    filter_upwards [hid,hdense] with ω hωid hωdense
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      by_cases he : ω ∈ E
      · obtain ⟨s,hs,hfree,hhit,hfirst,hz⟩ := hgeom ω hω
        have hR : dist (γ ω (τ ω)) z ≤ L*r := by rw [hhit]; nlinarith
        obtain ⟨t,ht,htH,hfar⟩ := source_physical_exit_interior_inclusion (hw ω) (τ ω) (β ω)
          hωdense hωid z (L*r) hR he
        have hkernel : H ω = 1 := by
          apply ite_eq_left
          refine ⟨t,?_,htH,?_⟩
          · simpa only [Y,ξ,ite_eq_left hz] using ht
          · exact hfar
        simp only [f,Set.indicator_of_mem he,hkernel,le_refl]
      · simp only [f,Set.indicator_of_notMem he]
        dsimp [H,sourcePhysicalDiskKernel]
        split_ifs <;> norm_num
    · simp only [Set.indicator_of_notMem hω,le_refl]
  have hmono := condExp_mono (m := hτ.measurableSpace) hAi hAH hdom
  filter_upwards [hmono,condExp_indicator hfi hA,condExp_indicator hHi hA,hcond] with ω hm hf hH hK
  intro hω
  rw [hf,hH,Set.indicator_of_mem hω,Set.indicator_of_mem hω,hK] at hm
  exact hm.trans (hmean ω hω)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 
noncomputable def sourceStopTruncate {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ≥0 := (min (τ ω) t).untopD 0

lemma sourceStopTruncate_coe {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    (sourceStopTruncate τ t ω : WithTop ℝ≥0) = min (τ ω) t := by
  have hn : min (τ ω) (t : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
  change (((min (τ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = _
  rw [← hv, WithTop.untopD_coe]

lemma sourceStopTruncate_stopping {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (sourceStopTruncate τ t ω : WithTop ℝ≥0)) := by
  simpa only [sourceStopTruncate_coe] using hτ.min_const t

lemma sourceStop_indicator_tendsto (τ : WithTop ℝ≥0) (v : ℝ)
    (hzero : τ = ⊤ → v = 0) :
    Tendsto (fun n : ℕ => if τ ≤ (n : ℝ≥0) then v else 0) atTop (𝓝 v) := by
  by_cases ht : τ = ⊤
  · simp only [ht, hzero ht, ite_self]
    exact tendsto_const_nhds
  obtain ⟨t, rfl⟩ := WithTop.ne_top_iff_exists.mp ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (⌈(t : ℝ)⌉₊)] with n hn
  have htn : t ≤ (n : ℝ≥0) := by exact_mod_cast (Nat.le_of_ceil_le hn)
  simp only [WithTop.coe_le_coe, ite_eq_left htn]

lemma source_unbounded_setIntegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hz : ∀ ω, τ ω = ⊤ → f ω = 0 ∧ g ω = 0)
    (hloc : ∀ (n : ℕ) (A : Set Ω),
      MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace] A →
      (∀ ω ∈ A, τ ω = (sourceStopTruncate τ n ω : WithTop ℝ≥0)) →
      (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ)
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ := by
  have hAm (n : ℕ) : MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace]
      (A ∩ {ω | τ ω ≤ (n : ℝ≥0)}) := by
    have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ (n : ℝ≥0)) A hA
    convert hh using 1
    congr 1
    funext ω
    exact sourceStopTruncate_coe τ n ω
  have hset (n : ℕ) :
      (∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, f ω ∂μ) ≤
        ∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, g ω ∂μ := by
    apply hloc n _ (hAm n)
    intro ω hω
    rw [sourceStopTruncate_coe, min_eq_left hω.2]
  have hlim (v : Ω → ℝ) (hv : Integrable v μ) (hzero : ∀ ω, τ ω = ⊤ → v ω = 0) :
      Tendsto (fun n : ℕ => ∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, v ω ∂μ) atTop
        (𝓝 (∫ ω in A, v ω ∂μ)) := by
    have he (n : ℕ) : (∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, v ω ∂μ) =
        ∫ ω in A, {ω | τ ω ≤ (n : ℝ≥0)}.indicator v ω ∂μ :=
      (setIntegral_indicator (μ := μ) (s := A) (f := v)
        ((ℱ.le (n : ℝ≥0)) _ (hτ n))).symm
    simp_rw [he]
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖v ω‖)
      (fun n => (hv.indicator ((ℱ.le (n : ℝ≥0)) _ (hτ n))).integrableOn.aestronglyMeasurable)
      hv.norm.integrableOn
    · intro n
      exact Eventually.of_forall fun ω => norm_indicator_le_norm_self _ _
    · apply Eventually.of_forall
      intro ω
      apply (sourceStop_indicator_tendsto (τ ω) (v ω) (hzero ω)).congr'
      apply Eventually.of_forall
      intro n
      by_cases hn : τ ω ≤ (n : WithTop ℝ≥0) <;> simp [Set.indicator, hn]
  exact le_of_tendsto_of_tendsto' (hlim f hf (fun ω ht => (hz ω ht).1))
    (hlim g hg (fun ω ht => (hz ω ht).2)) hset

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
namespace SLEExactGauge

lemma source_condExp_le_of_setIntegral_le
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : StronglyMeasurable[m] g)
    (h : ∀ A : Set Ω, MeasurableSet[m] A → (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ) :
    μ[f | m] ≤ᵐ[μ] g := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le
    (Integrable.trim hm integrable_condExp stronglyMeasurable_condExp)
    (Integrable.trim hm hg hgm)
  intro A hA _
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hA,
    ← setIntegral_trim hm hgm hA, setIntegral_condExp hm hf hA]
  exact h A hA

end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal NNReal
namespace SLEExactGauge
lemma source_unbounded_conditional_bound_on
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAfin : ∀ ω ∈ A, τ ω ≠ ⊤)
    (f : Ω → ℝ) (hf : Integrable f μ) (b : ℝ)
    (hloc : ∀ (n : ℕ) (E : Set Ω),
      MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace] E →
      E ⊆ A ∩ {ω | τ ω ≤ (n : ℝ≥0)} →
      (∫ ω in E, f ω ∂μ) ≤ ∫ _ in E, b ∂μ) :
    ∀ᵐ ω ∂μ, ω ∈ A → μ[f | hτ.measurableSpace] ω ≤ b := by
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hfi : Integrable (A.indicator f) μ := hf.indicator hAm
  have hbi : Integrable (A.indicator (fun _ => b)) μ := (integrable_const _).indicator hAm
  have hbound : μ[A.indicator f | hτ.measurableSpace] ≤ᵐ[μ] A.indicator (fun _ => b) := by
    apply source_condExp_le_of_setIntegral_le hτ.measurableSpace_le hfi hbi
      (stronglyMeasurable_const.indicator hA)
    intro S hS
    apply source_unbounded_setIntegral_le ℱ hτ _ _ hfi hbi ?_ ?_ S hS
    · intro ω ht
      have hnot : ω ∉ A := fun hω => hAfin ω hω ht
      simp only [Set.indicator_of_notMem hnot, and_self]
    · intro n E hE hτE
      have hen (ω : Ω) (hω : ω ∈ E) : τ ω ≤ (n : ℝ≥0) := by
        rw [hτE ω hω,sourceStopTruncate_coe]
        exact min_le_right _ _
      have hAn : MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace]
          (A ∩ {ω | τ ω ≤ (n : ℝ≥0)}) := by
        have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ (n : ℝ≥0)) A hA
        convert hh using 1
        congr 1
        funext ω
        exact sourceStopTruncate_coe τ n ω
      have heq : E ∩ A = E ∩ (A ∩ {ω | τ ω ≤ (n : ℝ≥0)}) := by
        ext ω
        exact ⟨fun h => ⟨h.1,h.2,hen ω h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩
      have hEA : MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace] (E ∩ A) := by
        rw [heq]
        exact hE.inter hAn
      rw [setIntegral_indicator hAm,setIntegral_indicator hAm]
      exact hloc n (E ∩ A) hEA (fun ω hω => ⟨hω.2,hen ω hω.1⟩)
  filter_upwards [hbound,condExp_indicator hf hA] with ω hb he
  intro hω
  rw [he,Set.indicator_of_mem hω,Set.indicator_of_mem hω] at hb
  exact hb
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance physicalClosedPrefixTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance physicalClosedPrefixTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

lemma source_physical_closed_prefix_isClosed (z : ℂ) (R : ℝ) (v : ℝ≥0) :
    IsClosed {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t ∈ Icc (0 : ℝ≥0) v,
      R ≤ dist (p.1 (p.2+t)) z} := by
  let E := {p : (C(ℝ≥0,ℂ) × ℝ≥0) × Icc (0 : ℝ≥0) v |
    R ≤ dist (p.1.1 (p.1.2+p.2)) z}
  have he : IsClosed E := by
    apply isClosed_le continuous_const
    exact (continuous_eval.comp ((continuous_fst.fst).prodMk
      (continuous_fst.snd.add (continuous_subtype_val.comp continuous_snd)))).dist continuous_const
  have hc := isClosedMap_fst_of_compactSpace E he
  convert hc using 1
  ext p
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨(p,⟨t,ht⟩),he,rfl⟩
  · rintro ⟨⟨p',t⟩,ht,rfl⟩
    exact ⟨t,t.2,ht⟩

lemma source_physical_closed_exit_measurableSet (z : ℂ) (R : ℝ) :
    MeasurableSet {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R ≤ dist (p.1 (p.2+t)) z} := by
  have heq : {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R ≤ dist (p.1 (p.2+t)) z} =
      {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ q : ℚ,
        z ∈ survivingDomain p.1 (p.2+(q:ℝ).toNNReal) ∧
        ∃ t ∈ Icc (0 : ℝ≥0) (q:ℝ).toNNReal, R ≤ dist (p.1 (p.2+t)) z} := by
    ext p
    constructor
    · rintro ⟨t,hl,he⟩
      have ho : IsOpen {u : ℝ≥0 | z ∈ survivingDomain p.1 (p.2+u)} :=
        source_survival_open.preimage
          ((continuous_const.prodMk (continuous_const.add continuous_id)).prodMk continuous_const)
      obtain ⟨b,htb,hb⟩ := exists_Ico_subset_of_mem_nhds (ho.mem_nhds hl) ⟨t+1,by simp⟩
      obtain ⟨q,htq,hqb⟩ := exists_rat_btwn (show (t:ℝ) < b from htb)
      have hqn : 0 ≤ (q:ℝ) := le_trans t.coe_nonneg htq.le
      have htu : t ≤ (q:ℝ).toNNReal := by
        change (t:ℝ) ≤ ((q:ℝ).toNNReal:ℝ)
        rw [Real.coe_toNNReal _ hqn]
        exact htq.le
      have hub : (q:ℝ).toNNReal < b := by
        change ((q:ℝ).toNNReal:ℝ) < (b:ℝ)
        rw [Real.coe_toNNReal _ hqn]
        exact hqb
      exact ⟨q,hb ⟨htu,hub⟩,t,⟨bot_le,htu⟩,he⟩
    · rintro ⟨q,hl,t,ht,he⟩
      refine ⟨t,?_,he⟩
      exact survivingDomain_antitone p.1 (by simpa only [add_comm] using add_le_add_left ht.2 p.2) hl
  rw [heq]
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  have ho : IsOpen {p : C(ℝ≥0,ℂ) × ℝ≥0 |
      z ∈ survivingDomain p.1 (p.2+(q:ℝ).toNNReal)} :=
    source_survival_open.preimage
      ((continuous_fst.prodMk (continuous_snd.add continuous_const)).prodMk continuous_const)
  exact ho.measurableSet.inter (source_physical_closed_prefix_isClosed z R (q:ℝ).toNNReal).measurableSet

lemma source_physical_closed_exit_measurable {Ω : Type*} [MeasurableSpace Ω]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgp : Measurable gp)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (z : ℂ) (R : ℝ) :
    MeasurableSet {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (gp ω) (τ ω+t) ∧
      R ≤ dist (gp ω (τ ω+t)) z} := by
  have hp : Measurable (fun ω => (gp ω,τ ω)) := hgp.prodMk hτ
  have hh := (source_physical_closed_exit_measurableSet z R).preimage hp
  simpa only [Set.preimage_ofPred_eq] using hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SLEExactGauge
lemma source_physical_slack_large (C c L : ℝ) (_hC : 0 ≤ C) (hL : 0 < L) :
    C * (L/2)^(-c) ≤ ((C+1)*2^c)*L^(-c) := by
  have he : (L/2)^(-c) = 2^c*L^(-c) := by
    rw [Real.div_rpow hL.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    simp only [div_inv_eq_mul,mul_comm]
  rw [he]
  have hh := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) c
  have hh' := Real.rpow_nonneg hL.le (-c)
  nlinarith [mul_nonneg hh hh']

lemma source_physical_slack_small (C c L : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hL : 0 < L) (hL2 : L ≤ 2) :
    1 ≤ ((C+1)*2^c)*L^(-c) := by
  have h2 : (0:ℝ) < 2^c := Real.rpow_pos_of_pos (by norm_num) _
  have hrec : 2^(-c) ≤ L^(-c) := Real.rpow_le_rpow_of_nonpos hL hL2 (by linarith)
  have he : (2:ℝ)^c * 2^(-c) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    simp
  have hh := mul_le_mul_of_nonneg_left hrec h2.le
  rw [he] at hh
  have hp : 0 ≤ 2^c * L^(-c) := le_trans (by norm_num) hh
  nlinarith [mul_nonneg hC hp]
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance physicalDiskTargetTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance physicalDiskTargetTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
local instance physicalDiskTargetDriverMeasurableSpace : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance physicalDiskTargetDriverBorelSpace : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
 

def SourcePhysicalDiskTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_m : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (_hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (_hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) τ)
    (z : ℂ) (r : ℝ), 0 < r →
  ∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
    (∀ ω ∈ A, ∃ T s : ℝ≥0, τ ω = T ∧ s ≤ T ∧
      Metric.closedBall z r ⊆ survivingDomain (γ ω) s ∧
      dist (γ ω T) z = r ∧
      (∀ t ∈ Ico s T, dist (γ ω t) z ≠ r) ∧
      z ∈ survivingDomain (γ ω) T) →
  ∀ L : ℝ, 1 ≤ L →
    ∀ᵐ ω ∂P, ω ∈ A →
      P[(fun ω => if τ ω ≠ ⊤ ∧ ∃ t : ℝ≥0,
        z ∈ survivingDomain (γ ω) ((τ ω).untopD 0+t) ∧
        L*r ≤ dist (γ ω ((τ ω).untopD 0+t)) z
        then (1 : ℝ) else 0) | hτ.measurableSpace] ω ≤ C*L^(-c)

theorem sourcePhysicalDisk_proved : SourcePhysicalDiskTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,hC,hc,hbound⟩ := sourceFinitePhysicalDisk_proved κ hκ hκ8
  refine ⟨(C+1)*2^c,c,mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _),hc,?_⟩
  intro Ω m P hP B hB hm hBc γ G F hw τ hτ z r hr A hA hgeom L hL
  let : IsProbabilityMeasure P := hP
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  obtain ⟨Φ,hΦm,hΦeq,hΦ⟩ := sourceStoppedTraceLaw κ (by linarith) hκ8 B hB hm hBc γ G F hw
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hBc ω) := funext fun ω => (hΦeq ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable _ hm)
  let H := {ω | τ ω ≠ ⊤ ∧ ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) ((τ ω).untopD 0+t) ∧
    L*r ≤ dist (γ ω ((τ ω).untopD 0+t)) z}
  let f : Ω → ℝ := H.indicator (fun _ => 1)
  have hH : MeasurableSet H := by
    have hfin : MeasurableSet {ω | τ ω ≠ ⊤} := (measurableSet_eq_fun hτ.measurable' measurable_const).compl
    have he := source_physical_closed_exit_measurable gp hgm (fun ω => (τ ω).untopD 0)
      (hτ.measurable'.untopD 0) z (L*r)
    exact hfin.inter he
  have hf : Integrable f P := (integrable_const (1:ℝ)).indicator hH
  have hfeq : f = (fun ω => if ω ∈ H then (1:ℝ) else 0) := by
    funext ω
    exact Set.indicator_apply _ _ _
  suffices hh : ∀ᵐ ω ∂P, ω ∈ A → P[f | hτ.measurableSpace] ω ≤ ((C+1)*2^c)*L^(-c) by
    simpa only [hfeq,H,Set.mem_ofPred_eq] using hh
  by_cases hL2 : L ≤ 2
  · have hfle : f ≤ᵐ[P] fun _ => (1:ℝ) := Eventually.of_forall fun ω => by
      dsimp [f,Set.indicator]; split_ifs <;> norm_num
    have hmono := condExp_mono (m := hτ.measurableSpace) hf (integrable_const (1:ℝ)) hfle
    have he := condExp_const (μ := P) hτ.measurableSpace_le (1:ℝ)
    filter_upwards [hmono] with ω hω
    intro _
    rw [he] at hω
    exact hω.trans (source_physical_slack_small C c L hC.le hc (by linarith) hL2)
  have hAfin : ∀ ω ∈ A, τ ω ≠ ⊤ := by
    intro ω hω
    obtain ⟨T,s,hT,_⟩ := hgeom ω hω
    rw [hT]
    exact WithTop.coe_ne_top
  apply source_unbounded_conditional_bound_on ℱ hτ A hA hAfin f hf _
  intro n E hE hEA
  let ρ := sourceStopTruncate τ n
  have hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0)) := sourceStopTruncate_stopping ℱ hτ n
  have heq (ω : Ω) (hω : ω ∈ E) : τ ω = (ρ ω : WithTop ℝ≥0) := by
    rw [sourceStopTruncate_coe,min_eq_left (hEA hω).2]
  have hgeomE : ∀ ω ∈ E, ∃ s : ℝ≥0, s ≤ ρ ω ∧
      Metric.closedBall z r ⊆ survivingDomain (γ ω) s ∧ dist (γ ω (ρ ω)) z = r ∧
      (∀ t ∈ Ico s (ρ ω), dist (γ ω t) z ≠ r) ∧ z ∈ survivingDomain (γ ω) (ρ ω) := by
    intro ω hω
    obtain ⟨T,s,hT,hs,hfree,hhit,hfirst,hz⟩ := hgeom ω (hEA hω).1
    have hTr : T = ρ ω := WithTop.coe_injective (hT.symm.trans (heq ω hω))
    exact ⟨s,hTr ▸ hs,hfree,hTr ▸ hhit,hTr ▸ hfirst,hTr ▸ hz⟩
  have hLhalf : 1 ≤ L/2 := by linarith
  have hlocal := hbound Ω m P hP B hB hm hBc γ G F hw ρ hρ z r hr E hE hgeomE (L/2) hLhalf
  let K := {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) (ρ ω+t) ∧
    (L/2)*r < dist (γ ω (ρ ω+t)) z}
  let g : Ω → ℝ := K.indicator (fun _ => 1)
  have hK : MeasurableSet K := source_physical_exit_measurable gp hgm ρ
    (stopping_time_measurable_nnreal hρ) z ((L/2)*r)
  have hg : Integrable g P := (integrable_const (1:ℝ)).indicator hK
  have hgeq : g = (fun ω => if ω ∈ K then (1:ℝ) else 0) := by
    funext ω
    exact Set.indicator_apply _ _ _
  have hfg : ∀ ω ∈ E, f ω ≤ g ω := by
    intro ω hω
    by_cases hh : ω ∈ H
    · obtain ⟨hfin,t,ht,hd⟩ := (show τ ω ≠ ⊤ ∧ ∃ t : ℝ≥0,
        z ∈ survivingDomain (γ ω) ((τ ω).untopD 0+t) ∧
        L*r ≤ dist (γ ω ((τ ω).untopD 0+t)) z from hh)
      have hτr : (τ ω).untopD 0 = ρ ω := by rw [heq ω hω,WithTop.untopD_coe]
      have hk : ω ∈ K := ⟨t,by rwa [hτr] at ht,by rw [hτr] at hd; nlinarith⟩
      simp only [f,g,Set.indicator_of_mem hh,Set.indicator_of_mem hk,le_refl]
    · simp only [f,Set.indicator_of_notMem hh]
      dsimp [g,Set.indicator]; split_ifs <;> norm_num
  have hEm : MeasurableSet E := hρ.measurableSpace_le _ hE
  have hi1 : (∫ ω in E, f ω ∂P) ≤ ∫ ω in E, g ω ∂P :=
    setIntegral_mono_on hf.integrableOn hg.integrableOn hEm hfg
  have hi2 : (∫ ω in E, g ω ∂P) ≤ ∫ ω in E, C*(L/2)^(-c) ∂P := by
    rw [← setIntegral_condExp hρ.measurableSpace_le hg hE]
    apply setIntegral_mono_on_ae integrable_condExp.integrableOn (integrable_const _).integrableOn hEm
    filter_upwards [hlocal] with ω hω
    simpa only [hgeq,K,Set.mem_ofPred_eq] using hω
  have hi3 : (∫ ω in E, C*(L/2)^(-c) ∂P) ≤ ∫ ω in E, ((C+1)*2^c)*L^(-c) ∂P := by
    exact setIntegral_mono_on (integrable_const _).integrableOn (integrable_const _).integrableOn hEm
      (fun _ _ => source_physical_slack_large C c L hC.le (by linarith))
  exact hi1.trans (hi2.trans hi3)

end
end SLEExactGauge
end

end OAI
