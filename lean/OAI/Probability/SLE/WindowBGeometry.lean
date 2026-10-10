import Mathlib
import OAI.Probability.SLE.WindowTails

namespace OAI

/-! Window BGeometry for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_witness_initial_domain
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) : survivingDomain γ 0 = upperHalfPlane := by
  apply Set.Subset.antisymm (fun _ hz => hz.1.1)
  intro z hz
  have hf : F 0 z ∈ survivingDomain γ 0 := h.2.2.2.2.2.2.1 0 hz
  have he : F 0 z = z := (h.initial_value (F 0 z) hf.1.1).symm.trans (h.2.2.2.2.2.2.2.2.1 0 z hz)
  rwa [he] at hf

lemma source_window_initial_ball
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r < z.im) (ω : a.samples) : closedBall z r ⊆ survivingDomain (γ ω) 0 := by
  rw [source_witness_initial_domain (a.witness ω)]
  intro w hw
  have hi := (le_abs_self (z.im-w.im)).trans (Complex.abs_im_le_norm (z-w))
  have hd : ‖z-w‖ ≤ r := by simpa only [mem_closedBall,dist_comm,dist_eq_norm] using hw
  change 0 < w.im
  linarith

lemma source_window_first_geometry
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r < z.im) (ω : a.samples) (hfin : liveSpatialHitTime (γ ω) z r ≠ ⊤) :
    ∃ T s : ℝ≥0, liveSpatialHitTime (γ ω) z r = T ∧ s ≤ T ∧
      closedBall z r ⊆ survivingDomain (γ ω) s ∧ dist (γ ω T) z = r ∧
      (∀ t ∈ Ico s T, dist (γ ω t) z ≠ r) ∧ z ∈ survivingDomain (γ ω) T := by
  obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hmem := source_liveHit_mem (a.trace_continuous ω) z r
    (source_window_origin_bound a z r hy.le ω) T hT.symm
  have he := source_liveTime_eq_sphere_of_finite (a.trace_continuous ω) z r
    (source_window_origin_bound a z r hy.le ω) hfin
  refine ⟨T,0,hT.symm,bot_le,source_window_initial_ball a z r hy ω,hmem.2,?_,hmem.1⟩
  intro t ht hd
  have hh := (spatialHitTime_le_iff (a.trace_continuous ω) z r t).mpr ⟨t,⟨bot_le,le_rfl⟩,hd⟩
  rw [← he,← hT] at hh
  exact ht.2.not_ge (WithTop.coe_le_coe.mp hh)

lemma source_windowB_le_disk
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r ε R : ℝ)
    (her : ε ≤ r) (hrR : r < R) (hy : r ≤ z.im) (ω : a.samples) :
    sourceSpatialWindowB (γ ω) z r ε R ≤
      (if liveSpatialHitTime (γ ω) z r ≠ ⊤ ∧ ∃ t : ℝ≥0,
        z ∈ survivingDomain (γ ω) ((liveSpatialHitTime (γ ω) z r).untopD 0+t) ∧
        R ≤ dist (γ ω ((liveSpatialHitTime (γ ω) z r).untopD 0+t)) z then (1:ℝ) else 0) := by
  rcases (source_windowHB_range (γ ω) z r ε R).2 with h|h
  · rw [h]; split_ifs <;> norm_num
  obtain ⟨T,hσ,hz,hd,_⟩ := source_windowB_before (a.trace_continuous ω) z r ε R her hrR
    (source_window_origin_bound a z r hy ω) h
  have hn := ne_top_of_le_ne_top WithTop.coe_ne_top hσ
  obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hn
  have hst : s ≤ T := WithTop.coe_le_coe.mp (by simpa only [← hs] using hσ)
  have he : (liveSpatialHitTime (γ ω) z r).untopD 0 + (T-s) = T := by
    rw [← hs,WithTop.untopD_coe,add_tsub_cancel_of_le hst]
  rw [h,ite_eq_left ⟨hn,T-s,by rwa [he],by rwa [he]⟩]

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
local instance windowBGeometryPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance windowBGeometryPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

lemma source_condExp_bound_supported
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {f g : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet[m] A)
    (hf : Integrable f μ) (hg : Integrable g μ) (hgf : g ≤ᵐ[μ] f)
    (hg0 : ∀ ω ∉ A, g ω = 0) (K : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ω ∈ A → μ[f | m] ω ≤ K) :
    μ[g | m] ≤ᵐ[μ] (fun ω => K*(if ω ∈ A then 1 else 0)) := by
  have heq : A.indicator g = g := by
    funext ω
    by_cases hω : ω ∈ A
    · exact Set.indicator_of_mem hω _
    · rw [Set.indicator_of_notMem hω,hg0 ω hω]
  have he := condExp_indicator hg hA
  rw [heq] at he
  filter_upwards [he,condExp_mono (m := m) hg hf hgf,hbound] with ω he hh hb
  by_cases hω : ω ∈ A
  · simpa only [ite_eq_left hω,mul_one] using hh.trans (hb hω)
  · rw [he,Set.indicator_of_notMem hω,ite_eq_right hω,mul_zero]

lemma source_windowB_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r ε R : ℝ)
    (hy : r ≤ z.im) :
    Integrable (fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε R) (P.comap Subtype.val) := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hτ := source_window_stopping a z r ε R hy
  have hm := (source_windowHB_stopped_measurable a z r ε R hτ).2.mono hτ.measurableSpace_le le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rcases (source_windowHB_range (γ ω) z r ε R).2 with h|h <;> simp only [h,norm_zero,norm_one,zero_le_one,le_refl]

lemma source_windowB_mean :
    ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (z : ℂ) (ε r L : ℝ), 0 < r → ε ≤ r → r < z.im → 1 < L →
    ∀ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
      (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)) | hσ.measurableSpace]
        ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => C*L^(-c)*
          (if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1)) := by
  intro κ hk hk8
  obtain ⟨C,c,hC,hc,hdisk⟩ := sourcePhysicalDisk_proved κ hk hk8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω m P hP γ a z ε r L hr her hy hL hσ
  let : IsProbabilityMeasure P := hP
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let σ := fun ω : a.samples => liveSpatialHitTime (γ ω) z r
  let A := {ω : a.samples | σ ω ≠ ⊤}
  have hA : MeasurableSet[hσ.measurableSpace] A :=
    (measurableSet_eq_fun hσ.measurable measurable_const).compl
  let E := {ω : a.samples | σ ω ≠ ⊤ ∧ ∃ t : ℝ≥0,
    z ∈ survivingDomain (γ ω) ((σ ω).untopD 0+t) ∧
    L*r ≤ dist (γ ω ((σ ω).untopD 0+t)) z}
  let f := E.indicator (fun _ => (1:ℝ))
  have hEm : MeasurableSet E := by
    apply (hσ.measurableSpace_le _ hA).inter
    exact source_physical_closed_exit_measurable
      (fun ω : a.samples => ⟨γ ω,a.trace_continuous ω⟩) (source_tracePath_measurable a)
      (fun ω => (σ ω).untopD 0) (hσ.measurable'.untopD 0) z (L*r)
  have hf : Integrable f μ := (integrable_const (1:ℝ)).indicator hEm
  have hf_def : f = (fun ω : a.samples => if ω ∈ E then 1 else 0) := by
    funext ω; exact Set.indicator_apply _ _ _
  have hgeom : ∀ ω ∈ A, ∃ T s : ℝ≥0, σ ω = T ∧ s ≤ T ∧
      closedBall z r ⊆ survivingDomain (γ ω) s ∧ dist (γ ω T) z = r ∧
      (∀ t ∈ Ico s T, dist (γ ω t) z ≠ r) ∧ z ∈ survivingDomain (γ ω) T :=
    fun ω hω => source_window_first_geometry a z r hy ω hω
  have hd := hdisk a.samples inferInstance μ inferInstance a.B a.brownian a.measurable_B
    a.continuous_B (fun ω : a.samples => γ ω) a.G a.F a.witness σ hσ z r hr A hA hgeom L hL.le
  have hb : ∀ᵐ ω ∂μ, ω ∈ A → μ[f | hσ.measurableSpace] ω ≤ C*L^(-c) := by
    rw [hf_def]
    convert hd using 1
    rfl
  have hi := source_windowB_integrable a z r ε (L*r) hy.le
  have hgf : (fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)) ≤ᵐ[μ] f := by
    rw [hf_def]
    exact Eventually.of_forall fun ω => source_windowB_le_disk a z r ε (L*r) her
      (by nlinarith) hy.le ω
  have hh := source_condExp_bound_supported hA hf hi hgf
    (fun ω hω => (source_windowHB_zero (a.trace_continuous ω) z r ε (L*r) (by
      simpa only [A,σ,Set.mem_ofPred_eq,ne_eq,not_not] using hω)).2) (C*L^(-c)) hb
  filter_upwards [hh] with ω hω
  by_cases htop : liveSpatialHitTime (γ ω) z r = ⊤ <;>
    simpa [A, σ, htop] using hω

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceSpatialWindowMeansTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ C Cbad c q : ℝ, 0 < C ∧ 0 < Cbad ∧ 0 < c ∧ 0 < q ∧ q < 1 ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε r L : ℝ), 0 < ε → ε ≤ q*r → r < z.im → 1 < L →
  ∃ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
    let μ := P.comap (Subtype.val : a.samples → Ω)
    let W := fun v (ω : a.samples) => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z v
    let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε (L*r)
    let B := fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)
    μ[H | hσ.measurableSpace] ≤ᵐ[μ] (fun ω => C*ε^codimension κ*W r ω) ∧
    μ[(fun ω => r^codimension κ*W ε ω*H ω) | hσ.measurableSpace] ≤ᵐ[μ]
      (fun ω => r^codimension κ*W r ω) ∧
    μ[B | hσ.measurableSpace] ≤ᵐ[μ]
      (fun ω => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1))

theorem sourceSpatialWindowMeans_proved : SourceSpatialWindowMeansTarget := by
  intro κ hk hk8
  have hk0 : 0 < κ := by linarith
  obtain ⟨C,q,hC,hq,hq1,hHV⟩ := source_window_HV_mean κ hk0 hk8
  obtain ⟨Cbad,c,hCb,hc,hB⟩ := source_windowB_mean κ hk hk8
  refine ⟨C,Cbad,c,q,hC,hCb,hc,hq,hq1,?_⟩
  intro Ω m P hP γ a z ε r L he heq hy hL
  have hr : 0 < r := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hq.le hn
    linarith
  have her : ε ≤ r := heq.trans (by nlinarith)
  obtain ⟨hs,hH,hV⟩ := hHV Ω m P hP γ a z ε r (L*r) he heq hy.le
  exact ⟨hs,hH,hV,hB Ω m P hP γ a z ε r L hr her hy hL hs⟩
end
end SLEExactGauge
end

end OAI
