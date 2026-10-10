import Mathlib
import OAI.Probability.SLE.WindowAssembly
import OAI.Probability.SLE.WindowTails

namespace OAI

/-! Physical Mesh Window Core for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

 

structure SourceWindowCore {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (D : Set ℂ) (r R : ℝ)
    (γ : ℝ≥0 → Ω → ℂ) (σ τ : ℂ → Ω → WithTop ℝ≥0) : Prop where
  measurable_D : MeasurableSet D
  bounded_D : D ⊆ ball 0 1
  radius_pos : 0 < r
  radius_le : r ≤ R
  radius_small : 3*R ≤ 1
  continuous_trace : ∀ ω, Continuous (fun t => γ t ω)
  adapted_trace : ∀ t, Measurable[ℱ t] (γ t)
  start : ∀ z, IsStoppingTime ℱ (σ z)
  finish : ∀ z, IsStoppingTime ℱ (τ z)
  time_le : ∀ z ω, σ z ω ≤ τ z ω
  contact : ∀ z ω, σ z ω ≠ ⊤ → dist (γ ((σ z ω).untopD 0) ω) z = r
  confined : ∀ z ω (t : ℝ≥0), σ z ω ≤ (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) < τ z ω →
    dist (γ t ω) z < R
  outside : ∀ z, z ∉ D → ∀ ω, σ z ω = ⊤

lemma SourceWindowCore.attach {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {D : Set ℂ} {r R K : ℝ}
    {γ : ℝ≥0 → Ω → ℂ} {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceWindowCore ℱ D r R γ σ τ) (hK : 0 ≤ K)
    (hYm : ∀ z, Measurable[(h.finish z).measurableSpace] (Y z))
    (hμm : ∀ z, Measurable[(h.start z).measurableSpace] (μ z))
    (hY : ∀ z ω, 0 ≤ Y z ω ∧ Y z ω ≤ K)
    (hμ : ∀ z ω, 0 ≤ μ z ω) (hμb : ∃ M : ℝ, ∀ z ω, μ z ω ≤ M)
    (hmean : ∀ z, ∀ᵐ ω ∂P, σ z ω ≠ ⊤ → P[Y z | (h.start z).measurableSpace] ω ≤ μ z ω)
    (hns : ∀ z ω, σ z ω = ⊤ → Y z ω = 0 ∧ μ z ω = 0)
    (hne : ∀ z ω, τ z ω = ⊤ → Y z ω = 0)
    (hYj : Measurable (fun p : ℂ × Ω => Y p.1 p.2))
    (hμj : Measurable (fun p : ℂ × Ω => μ p.1 p.2)) :
    SourceDisjointWindows P ℱ D r R K γ σ τ Y μ :=
  ⟨h.measurable_D,h.bounded_D,h.radius_pos,h.radius_le,h.radius_small,hK,
    h.continuous_trace,h.adapted_trace,h.start,h.finish,h.time_le,h.contact,h.confined,
    hYm,hμm,hY,hμ,hμb,hmean,hns,hne,
    fun z hz ω => ⟨h.outside z hz ω,hns z ω (h.outside z hz ω)⟩,hYj,hμj⟩

lemma source_mesh_window_core
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (c : ℂ) (hDc : D ⊆ ball c 1)
    (ε r R : ℝ) (hr : 0 < r) (hrR : r < R) (hR : 3*R ≤ 1)
    (hy : ∀ z ∈ D, r ≤ z.im) :
    SourceWindowCore a.filtration ((fun z : ℂ => z+c) ⁻¹' D) r R
      (fun t (ω : a.samples) => γ ω t-c)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c) r ε R) := by
  have hd (x z : ℂ) : dist (x-c) z = dist x (z+c) := by
    simp only [dist_eq_norm]; congr 1; ring
  refine ⟨hD.preimage (measurable_id.add_const c),?_,hr,hrR.le,hR,
    fun ω => (a.trace_continuous ω).sub continuous_const,
    fun t => (a.trace_adapted t).sub_const c,
    fun z => source_collarStart_stopping a D r hy (z+c),
    fun z => source_collarFinish_stopping a D r ε R hy (z+c),?_,?_,?_,?_⟩
  · intro z hz
    have hh := hDc hz
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hh
  · intro z ω
    by_cases hz : z+c ∈ D
    · simpa only [sourceCollarStart,sourceCollarFinish,ite_eq_left hz] using
        source_window_start_le (a.trace_continuous ω) (z+c) r ε R
    · simp only [sourceCollarStart,sourceCollarFinish,ite_eq_right hz,le_refl]
  · intro z ω hn
    have hz : z+c ∈ D := by
      by_contra hh
      exact hn (by simp only [sourceCollarStart,ite_eq_right hh])
    simp only [sourceCollarStart,ite_eq_left hz] at hn ⊢
    obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hn
    rw [← hT,WithTop.untopD_coe,hd]
    exact (source_liveHit_mem (a.trace_continuous ω) (z+c) r
      (source_window_origin_bound a (z+c) r (hy (z+c) hz) ω) T hT.symm).2
  · intro z ω t hst htt
    have hz : z+c ∈ D := by
      by_contra hh
      simp only [sourceCollarStart,ite_eq_right hh] at hst
      exact (WithTop.not_top_le_coe t) hst
    simp only [sourceCollarStart,sourceCollarFinish,ite_eq_left hz] at hst htt
    rw [hd]
    exact (source_before_window (γ ω) (z+c) r ε R t hst htt).2.2
  · intro z hz ω
    exact ite_eq_right hz

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_if_bound {p : Prop} [Decidable p] {x K : ℝ}
    (hK : 0 ≤ K) (hx : p → 0 ≤ x ∧ x ≤ K) :
    0 ≤ (if p then x else 0) ∧ (if p then x else 0) ≤ K := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using hx hp
  · simp only [ite_eq_right hp,le_refl,true_and]; exact hK

lemma source_collar_HB_bounds (D : Set ℂ) (γ : ℝ≥0 → ℂ)
    (z : ℂ) (r ε R : ℝ) :
    (0 ≤ sourceCollarH D γ z r ε R ∧ sourceCollarH D γ z r ε R ≤ 1) ∧
    (0 ≤ sourceCollarB D γ z r ε R ∧ sourceCollarB D γ z r ε R ≤ 1) := by
  constructor
  · apply source_if_bound zero_le_one
    intro _; rcases (source_windowHB_range γ z r ε R).1 with h|h <;> simp [h]
  · apply source_if_bound zero_le_one
    intro _; rcases (source_windowHB_range γ z r ε R).2 with h|h <;> simp [h]

lemma source_collar_end_zero (D : Set ℂ) (γ : ℝ≥0 → ℂ)
    (z : ℂ) (r ε R : ℝ)
    (ht : sourceCollarFinish D γ z r ε R = ⊤) :
    sourceCollarH D γ z r ε R = 0 ∧ sourceCollarB D γ z r ε R = 0 := by
  by_cases hz : z ∈ D
  · simp only [sourceCollarFinish,ite_eq_left hz] at ht
    simp only [sourceCollarH,sourceCollarB,ite_eq_left hz,sourceSpatialWindowH,sourceSpatialWindowB,
      ht,ne_eq,not_true_eq_false,false_and,ite_false,and_self]
  · simp only [sourceCollarH,sourceCollarB,ite_eq_right hz,and_self]

lemma source_collar_start_zero (D : Set ℂ) {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ)
    (ht : sourceCollarStart D γ z r = ⊤) :
    sourceCollarH D γ z r ε R = 0 ∧ sourceCollarB D γ z r ε R = 0 := by
  apply source_collar_end_zero
  by_cases hz : z ∈ D
  · simp only [sourceCollarStart,ite_eq_left hz] at ht
    simp only [sourceCollarFinish,ite_eq_left hz]
    exact top_le_iff.mp (by simpa only [ht] using source_window_start_le hc z r ε R)
  · exact ite_eq_right hz

lemma source_collar_weight_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (D : Set ℂ) (r : ℝ) (hr : 0 < r)
    (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples) :
    0 ≤ (if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z r else 0) ∧
    (if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z r else 0) ≤ r^(-codimension κ) := by
  apply source_if_bound (Real.rpow_nonneg hr.le _)
  exact fun hz => (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _)
    hκ hκ8 hr z (hy z hz)

lemma source_collar_weight_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples)
    (hn : sourceCollarStart D (γ ω) z r = ⊤) :
    (if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z r else 0) = 0 := by
  by_cases hz : z ∈ D
  · simp only [sourceCollarStart,ite_eq_left hz] at hn
    rw [ite_eq_left hz]
    exact source_window_weight_zero a z r (hy z hz) ω hn
  · exact ite_eq_right hz

lemma source_collar_weight_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (r : ℝ) :
    Measurable (fun p : ℂ × a.samples =>
      if p.1 ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t p.2)
        (γ p.2) (a.G p.2) p.1 r else 0) :=
  Measurable.ite (hD.preimage measurable_fst) (a.spatialGreenWeight_measurable r) measurable_const

lemma source_collar_mean_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im)
    (f g : ℂ → a.samples → ℝ)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[f z | (source_liveHit_stopping a z r (hy z hz)).measurableSpace]
        ≤ᵐ[P.comap Subtype.val] g z) (z : ℂ) :
    (P.comap Subtype.val)[(fun ω => if z ∈ D then f z ω else 0) |
      (source_collarStart_stopping a D r hy z).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω => if z ∈ D then g z ω else 0) := by
  by_cases hz : z ∈ D
  · simp only [ite_eq_left hz]
    have hs := source_stop_space_congr (source_collarStart_stopping a D r hy z)
      (source_liveHit_stopping a z r (hy z hz))
      (funext fun ω => by simp only [sourceCollarStart,ite_eq_left hz])
    rw [hs]
    exact hmean z hz
  · simp only [ite_eq_right hz]
    change (P.comap Subtype.val)[(0 : a.samples → ℝ) |
      (source_collarStart_stopping a D r hy z).measurableSpace] ≤ᵐ[P.comap Subtype.val] 0
    rw [condExp_zero]

lemma source_window_scaled_bound {p q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    r^p * (q*r)^(-p) = q^(-p) := by
  rw [Real.mul_rpow hq.le hr.le]
  calc
    r^p * (q^(-p)*r^(-p)) = q^(-p)*(r^p*r^(-p)) := by ring
    _ = q^(-p) := by rw [← Real.rpow_add hr,add_neg_cancel,Real.rpow_zero,mul_one]

lemma source_collar_V_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (D : Set ℂ) (q r R : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples) :
    0 ≤ r^codimension κ * spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z (q*r) * sourceCollarH D (γ ω) z r (q*r) R ∧
    r^codimension κ * spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z (q*r) * sourceCollarH D (γ ω) z r (q*r) R ≤ q^(-codimension κ) := by
  by_cases hz : z ∈ D
  · have hw := (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _)
      hκ hκ8 (mul_pos hq hr) z ((show q*r ≤ r by nlinarith).trans (hy z hz))
    have hH := (source_collar_HB_bounds D (γ ω) z r (q*r) R).1
    have hnon := mul_nonneg (Real.rpow_nonneg hr.le (codimension κ)) hw.1
    refine ⟨mul_nonneg hnon hH.1,?_⟩
    calc
      _ ≤ r^codimension κ * (q*r)^(-codimension κ) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw.2 (Real.rpow_nonneg hr.le _)) hH.2 hH.1
          (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (mul_pos hq hr).le _))
      _ = _ := by rw [mul_one,source_window_scaled_bound hq hr]
  · simp only [sourceCollarH,ite_eq_right hz,mul_zero,le_refl,true_and]
    exact Real.rpow_nonneg hq.le _

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_H_window
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L C : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1) (hC : 0 ≤ C)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowH (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => C*(q*r)^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) :
    SourceDisjointWindows (P.comap Subtype.val) a.filtration
      ((fun z : ℂ => z+c₀) ⁻¹' D) r (L*r) 1
      (fun t (ω : a.samples) => γ ω t-c₀)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c₀) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => sourceCollarH D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => C*(q*r)^codimension κ*
        (if z+c₀ ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
          (γ ω) (a.G ω) (z+c₀) r else 0)) := by
  let core := source_mesh_window_core a D hD c₀ hDc (q*r) r (L*r) hr (by nlinarith) hR hy
  have hs : q*r ≤ r := by nlinarith
  have hfac : 0 ≤ C*(q*r)^codimension κ := mul_nonneg hC (Real.rpow_nonneg (mul_pos hq hr).le _)
  apply core.attach zero_le_one
  · intro z
    exact (source_collarHBV_stopped a D r (q*r) (L*r) hs hy (z+c₀)).1
  · intro z
    exact (source_collarWeight_stopped a D r hy (z+c₀)).const_mul _
  · intro z ω
    exact (source_collar_HB_bounds D (γ ω) (z+c₀) r (q*r) (L*r)).1
  · intro z ω
    exact mul_nonneg hfac (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).1
  · refine ⟨C*(q*r)^codimension κ*r^(-codimension κ),?_⟩
    intro z ω
    exact mul_le_mul_of_nonneg_left (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).2 hfac
  · intro z
    have hh := source_collar_mean_transfer a D r hy
      (fun z (ω : a.samples) => sourceSpatialWindowH (γ ω) z r (q*r) (L*r))
      (fun z (ω : a.samples) => C*(q*r)^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r) hmean (z+c₀)
    have hg : (fun ω : a.samples => if z+c₀ ∈ D then C*(q*r)^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (z+c₀) r else 0) =
        (fun ω : a.samples => C*(q*r)^codimension κ*(if z+c₀ ∈ D then spatialGreenWeight κ
          (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (z+c₀) r else 0)) := by
      funext ω; rw [mul_ite,mul_zero]
    rw [hg] at hh
    exact hh.mono (fun _ h _ => h)
  · intro z ω hn
    exact ⟨(source_collar_start_zero D (a.trace_continuous ω) (z+c₀) r (q*r) (L*r) hn).1,
      by rw [source_collar_weight_zero a D r hy (z+c₀) ω hn,mul_zero]⟩
  · intro z ω hn
    exact (source_collar_end_zero D (γ ω) (z+c₀) r (q*r) (L*r) hn).1
  · exact (source_collarHB_joint a D hD r (q*r) (L*r) hy).1.comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)
  · exact ((source_collar_weight_joint a D hD r).const_mul (C*(q*r)^codimension κ)).comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_collar_V_mean
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (q r L : ℝ) (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*
        sourceSpatialWindowH (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) (z : ℂ) :
    (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceCollarH D (γ ω) z r (q*r) (L*r)) |
      (source_collarStart_stopping a D r hy z).measurableSpace] ≤ᵐ[P.comap Subtype.val]
    (fun ω : a.samples => r^codimension κ*(if z ∈ D then spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0)) := by
  have hh := source_collar_mean_transfer a D r hy
    (fun z (ω : a.samples) => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceSpatialWindowH (γ ω) z r (q*r) (L*r))
    (fun z (ω : a.samples) => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r) hmean z
  have hf : (fun ω : a.samples => if z ∈ D then r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceSpatialWindowH (γ ω) z r (q*r) (L*r) else 0) =
      (fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceCollarH D (γ ω) z r (q*r) (L*r)) := by
    funext ω; simp only [sourceCollarH,mul_ite,mul_zero]
  have hg : (fun ω : a.samples => if z ∈ D then r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0) =
      (fun ω : a.samples => r^codimension κ*(if z ∈ D then spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0)) := by
    funext ω; rw [mul_ite,mul_zero]
  rw [hf,hg] at hh
  exact hh.mono (fun _ h => h)

lemma source_collar_V_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (q r L : ℝ)
    (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t p.2) (γ p.2) (a.G p.2) (p.1+c₀) (q*r)*
        sourceCollarH D (γ p.2) (p.1+c₀) r (q*r) (L*r)) := by
  have hj := (((a.spatialGreenWeight_measurable (q*r)).const_mul (r^codimension κ)).mul
      (source_collarHB_joint a D hD r (q*r) (L*r) hy).1)
  have ht : Measurable (fun p : ℂ × a.samples => (p.1+c₀,p.2)) :=
    (measurable_fst.add_const c₀).prodMk measurable_snd
  have hh := hj.comp ht
  dsimp only [Function.comp_def] at hh
  exact hh

lemma source_mesh_V_window
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*
        sourceSpatialWindowH (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) :
    SourceDisjointWindows (P.comap Subtype.val) a.filtration
      ((fun z : ℂ => z+c₀) ⁻¹' D) r (L*r) (q^(-codimension κ))
      (fun t (ω : a.samples) => γ ω t-c₀)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c₀) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (z+c₀) (q*r)*
        sourceCollarH D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => r^codimension κ*
        (if z+c₀ ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
          (γ ω) (a.G ω) (z+c₀) r else 0)) := by
  let core := source_mesh_window_core a D hD c₀ hDc (q*r) r (L*r) hr (by nlinarith) hR hy
  have hs : q*r ≤ r := by nlinarith
  have hfac : 0 ≤ r^codimension κ := Real.rpow_nonneg hr.le _
  apply core.attach (Real.rpow_nonneg hq.le _)
  · intro z
    simpa only [mul_assoc] using (source_collarHBV_stopped a D r (q*r) (L*r) hs hy (z+c₀)).2.2.const_mul (r^codimension κ)
  · intro z
    exact (source_collarWeight_stopped a D r hy (z+c₀)).const_mul _
  · intro z ω
    exact source_collar_V_bounds a hκ hκ8 D q r (L*r) hq hq1 hr hy (z+c₀) ω
  · intro z ω
    exact mul_nonneg hfac (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).1
  · refine ⟨r^codimension κ*r^(-codimension κ),?_⟩
    intro z ω
    exact mul_le_mul_of_nonneg_left (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).2 hfac
  · intro z
    exact (source_collar_V_mean a D q r L hy hmean (z+c₀)).mono (fun _ h _ => h)
  · intro z ω hn
    refine ⟨?_,?_⟩
    · rw [(source_collar_start_zero D (a.trace_continuous ω) (z+c₀) r (q*r) (L*r) hn).1,mul_zero]
    · rw [source_collar_weight_zero a D r hy (z+c₀) ω hn,mul_zero]
  · intro z ω hn
    rw [(source_collar_end_zero D (γ ω) (z+c₀) r (q*r) (L*r) hn).1,mul_zero]
  · exact source_collar_V_joint a D hD c₀ q r L hy
  · exact ((source_collar_weight_joint a D hD r).const_mul (r^codimension κ)).comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_B_window
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L Cbad c : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1) (hCb : 0 ≤ Cbad)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowB (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1))) :
    SourceDisjointWindows (P.comap Subtype.val) a.filtration
      ((fun z : ℂ => z+c₀) ⁻¹' D) r (L*r) 1
      (fun t (ω : a.samples) => γ ω t-c₀)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c₀) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => sourceCollarB D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => Cbad*L^(-c)*
        (if sourceCollarStart D (γ ω) (z+c₀) r = ⊤ then 0 else 1)) := by
  let core := source_mesh_window_core a D hD c₀ hDc (q*r) r (L*r) hr (by nlinarith) hR hy
  have hs : q*r ≤ r := by nlinarith
  have hfac : 0 ≤ Cbad*L^(-c) := mul_nonneg hCb (Real.rpow_nonneg (by linarith) _)
  apply core.attach zero_le_one
  · intro z
    exact (source_collarHBV_stopped a D r (q*r) (L*r) hs hy (z+c₀)).2.1
  · intro z
    exact (Measurable.ite (measurableSet_eq_fun
      (source_collarStart_stopping a D r hy (z+c₀)).measurable measurable_const)
      measurable_const measurable_const).const_mul _
  · intro z ω
    exact (source_collar_HB_bounds D (γ ω) (z+c₀) r (q*r) (L*r)).2
  · intro z ω
    exact mul_nonneg hfac (by split_ifs <;> norm_num)
  · refine ⟨Cbad*L^(-c),?_⟩
    intro z ω
    exact (mul_le_mul_of_nonneg_left (show (if sourceCollarStart D (γ ω) (z+c₀) r = ⊤ then (0:ℝ) else 1) ≤ 1 by split_ifs <;> norm_num) hfac).trans_eq (mul_one _)
  · intro z
    have hh := source_collar_mean_transfer a D r hy
      (fun z (ω : a.samples) => sourceSpatialWindowB (γ ω) z r (q*r) (L*r))
      (fun z (ω : a.samples) => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1)) hmean (z+c₀)
    have hg : (fun ω : a.samples => if z+c₀ ∈ D then Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) (z+c₀) r = ⊤ then 0 else 1) else 0) =
        (fun ω : a.samples => Cbad*L^(-c)*(if sourceCollarStart D (γ ω) (z+c₀) r = ⊤ then 0 else 1)) := by
      funext ω; by_cases hz : z+c₀ ∈ D <;> simp [sourceCollarStart,hz]
    rw [hg] at hh
    exact hh.mono (fun _ h _ => h)
  · intro z ω hn
    exact ⟨(source_collar_start_zero D (a.trace_continuous ω) (z+c₀) r (q*r) (L*r) hn).2,
      by rw [ite_eq_left hn,mul_zero]⟩
  · intro z ω hn
    exact (source_collar_end_zero D (γ ω) (z+c₀) r (q*r) (L*r) hn).2
  · exact (source_collarHB_joint a D hD r (q*r) (L*r) hy).2.comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)
  · exact ((Measurable.ite (measurableSet_eq_fun
      (source_collarStart_joint a D hD r hy) measurable_const)
      measurable_const measurable_const).const_mul (Cbad*L^(-c))).comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma window_finite_mgf_at_starts {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {σ τ : ι → Ω → WithTop ℝ≥0}
    (hs : ∀ i, IsStoppingTime ℱ (σ i)) (ht : ∀ i, IsStoppingTime ℱ (τ i))
    (horder : ∀ i j ω, windowBefore σ j i ω → τ j ω ≤ σ i ω)
    {X : ι → Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : ∀ i, Measurable[(ht i).measurableSpace] (X i))
    (hXb : ∀ i ω, |X i ω| ≤ K)
    (hmean : ∀ i, P[X i|(hs i).measurableSpace] ≤ᵐ[P] 0)
    {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWstart : ∀ i, Measurable[(hs i).measurableSpace] W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * Real.exp (θ*∑ i, X i ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (Fintype.card ι * (θ*K)^2/2) := by
  classical
  let q := (θ*K)^2/2
  let g (i : ι) (ω : Ω) := Real.exp (θ*X i ω-q)
  let pre (i : ι) (ω : Ω) := ∏ j, if windowBefore σ j i ω then g j ω else 1
  have hg (i : ι) : Measurable[(ht i).measurableSpace] (g i) :=
    (((hX i).const_mul θ).sub_const q).exp
  have hga (i : ι) : Measurable[mΩ] (g i) := (hg i).mono (ht i).measurableSpace_le le_rfl
  have hg0 (i : ι) (ω : Ω) : 0 ≤ g i ω := (Real.exp_pos _).le
  have hgB (i : ι) (ω : Ω) : g i ω ≤ Real.exp (θ*K) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hXb i ω)) hθ
    dsimp [q]
    nlinarith [sq_nonneg (θ*K)]
  have hp (i : ι) : Measurable[(hs i).measurableSpace] (pre i) := by
    apply Finset.measurable_prod
    intro j hj
    exact window_measurable_on_event (hs i) (ht j) (hg j)
      (window_before_measurable hs i j) (fun ω hω => horder i j ω hω) 1
  have hp0 (i : ι) (ω : Ω) : 0 ≤ pre i ω := by
    apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> positivity
  have hpB (i : ι) (ω : Ω) : pre i ω ≤ Real.exp (θ*K)^Fintype.card ι := by
    calc
      _ ≤ ∏ _j : ι, Real.exp (θ*K) := by
        apply Finset.prod_le_prod₀
        · intro j hj; split_ifs <;> positivity
        · intro j hj; split_ifs
          · exact hgB j ω
          · exact Real.one_le_exp (mul_nonneg hθ hK.le)
      _ = _ := by simp
  obtain ⟨M,hM⟩ := hWb
  have hWi : Integrable W P := window_integrable_nonneg hWa hW0 hM
  have hHi (i : ι) : Integrable (fun ω => W ω*pre i ω*(g i ω-1)) P := by
    apply window_integrable_bounded (C := (M*Real.exp (θ*K)^Fintype.card ι)*(Real.exp (θ*K)+1)) (((hWa.mul ((hp i).mono (hs i).measurableSpace_le le_rfl))).mul
      ((hga i).sub_const 1))
    intro ω
    change ‖W ω*pre i ω*(g i ω-1)‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω),
      Real.norm_eq_abs, abs_of_nonneg (hp0 i ω)]
    apply mul_le_mul
    · exact mul_le_mul (hM ω) (hpB i ω) (hp0 i ω) ((hW0 ω).trans (hM ω))
    · calc
        _ ≤ ‖g i ω‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ = g i ω + 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 i ω), norm_one]
        _ ≤ _ := add_le_add (hgB i ω) le_rfl
    · exact norm_nonneg _
    · exact mul_nonneg ((hW0 ω).trans (hM ω)) (by positivity)
  have hHi0 (i : ι) : (∫ ω, W ω*pre i ω*(g i ω-1) ∂P) ≤ 0 := by
    exact window_weighted_normalized (hs i).measurableSpace_le hK hθ
      ((hX i).mono (ht i).measurableSpace_le le_rfl) (hXb i) (hmean i)
      ((hWstart i).mul (hp i)) (fun ω => mul_nonneg (hW0 ω) (hp0 i ω))
      ⟨M*Real.exp (θ*K)^Fintype.card ι, fun ω =>
        mul_le_mul (hM ω) (hpB i ω) (hp0 i ω) ((hW0 ω).trans (hM ω))⟩
  have hnorm : (∫ ω, W ω * ∏ i, g i ω ∂P) ≤ ∫ ω, W ω ∂P := by
    have hid (ω : Ω) := window_prod_before σ ω (fun i => g i ω)
    simp_rw [hid, mul_add, mul_one, Finset.mul_sum]
    change (∫ ω, W ω + ∑ i, W ω*((g i ω-1)*pre i ω) ∂P) ≤ _
    simp_rw [show ∀ i ω, W ω*((g i ω-1)*pre i ω) = W ω*pre i ω*(g i ω-1)
      from fun _ _ => by ring]
    rw [integral_add hWi (integrable_finsetSum _ (fun i hi => hHi i)), integral_finsetSum]
    · exact add_le_of_nonpos_right (Finset.sum_nonpos fun i hi => hHi0 i)
    · exact fun i hi => hHi i
  have hprod (ω : Ω) : (∏ i, g i ω) =
      Real.exp (θ*∑ i, X i ω) / Real.exp (Fintype.card ι * q) := by
    change (∏ i, Real.exp (θ*X i ω-q)) = _
    rw [← Real.exp_sum]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    exact Real.exp_sub _ _
  simp only [hprod, ← mul_div_assoc] at hnorm
  rw [integral_div] at hnorm
  simpa only [q, mul_div_assoc] using (div_le_iff₀ (Real.exp_pos _)).mp hnorm

 

lemma window_source_finite_mgf_at_starts {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {z : ι → ℂ} (hz : ∀ i j, i ≠ j → 2*R < dist (z i) (z j))
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWs : ∀ i, Measurable[(h.start (z i)).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∑ i, (Y (z i) ω-μ (z i) ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (Fintype.card ι * (θ*K)^2/2) := by
  let X (i : ι) (ω : Ω) := Y (z i) ω-min (μ (z i) ω) K
  have hYa (i : ι) : Measurable[mΩ] (Y (z i)) :=
    (h.output_measurable (z i)).mono (h.finish (z i)).measurableSpace_le le_rfl
  have hμa (i : ι) : Measurable[mΩ] (μ (z i)) :=
    (h.mean_measurable (z i)).mono (h.start (z i)).measurableSpace_le le_rfl
  have hX (i : ι) : Measurable[(h.finish (z i)).measurableSpace] (X i) :=
    (h.output_measurable (z i)).sub (((h.mean_measurable (z i)).mono
      ((h.start (z i)).measurableSpace_mono (h.finish (z i)) (h.time_le (z i))) le_rfl).min measurable_const)
  have hXb (i : ι) (ω : Ω) : |X i ω| ≤ K := by
    rw [abs_le]
    have := h.output_bound (z i) ω
    have := le_min (h.mean_nonneg (z i) ω) hK.le
    have := min_le_right (μ (z i) ω) K
    dsimp [X]
    constructor <;> linarith
  have hm (i : ι) : P[X i|(h.start (z i)).measurableSpace] ≤ᵐ[P] 0 :=
    window_capped_cond_mean (h.start (z i)).measurableSpace_le hK.le (hYa i)
      (h.output_bound (z i)) (h.mean_measurable (z i)) (h.mean_nonneg (z i))
      (window_cond_mean_at_infinity (h.start (z i))
        (window_integrable_nonneg (hYa i) (fun ω => (h.output_bound (z i) ω).1)
          (fun ω => (h.output_bound (z i) ω).2)) (h.upper_mean (z i)) (h.no_start (z i)))
  have ht := window_finite_mgf_at_starts (fun i => h.start (z i)) (fun i => h.finish (z i))
    (window_geometric_order h hz) hK hθ hX hXb hm hWa hWs hW0 hWb
  apply le_trans _ ht
  obtain ⟨M,hM⟩ := hWb
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hib (f : ι → Ω → ℝ) (hf : ∀ i, Measurable[mΩ] (f i))
      (hb : ∀ i ω, f i ω ≤ K) : Integrable (fun ω => W ω*Real.exp (θ*∑ i, f i ω)) P :=
    window_integrable_nonneg (C := M*Real.exp (θ*(Fintype.card ι*K))) (hWa.mul ((Finset.measurable_sum _ (fun i _ => hf i)).const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (fun ω => mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum fun i hi => hb i ω).trans_eq (by simp)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  apply integral_mono
  · exact hib (fun i ω => Y (z i) ω-μ (z i) ω) (fun i => (hYa i).sub (hμa i))
      (fun i ω => sub_le_self _ (h.mean_nonneg (z i) ω) |>.trans (h.output_bound (z i) ω).2)
  · exact hib X (fun i => (hX i).mono (h.finish (z i)).measurableSpace_le le_rfl)
      (fun i ω => le_abs_self _ |>.trans (hXb i ω))
  · intro ω
    apply mul_le_mul_of_nonneg_left _ (hW0 ω)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ
    exact Finset.sum_le_sum fun i hi => sub_le_sub_left (min_le_left _ _) _

lemma window_source_mgf_pos_at_starts {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWs : ∀ z, Measurable[(h.start z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∫ z in D, (Y z ω-μ z ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
  obtain ⟨n,a,ha,han,hsep,haR⟩ := window_choose_grid (h.radius_pos.trans_le h.radius_le) h.radius_small
  let : LinearOrder (Fin n × Fin n) := LinearOrder.lift' toLex toLex.injective
  let F (ξ : ℝ × ℝ) (ω : Ω) := a^2 * ∑ i : Fin n × Fin n,
    (Y (windowCenter a ξ i) ω - μ (windowCenter a ξ i) ω)
  have hcenter (i : Fin n × Fin n) : Measurable (fun ξ => windowCenter a ξ i) :=
    Complex.measurableEquivRealProd.symm.measurable.comp
      (((measurable_fst.add_const _).sub_const _).prodMk ((measurable_snd.add_const _).sub_const _))
  have hmeas : Measurable (Function.uncurry F) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (h.joint_output.sub h.joint_mean).comp
      (((hcenter i).comp measurable_fst).prodMk measurable_snd)
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hnorm (z : ℂ) (ω : Ω) : ‖Y z ω-μ z ω‖ ≤ K+L := by
    calc
      _ ≤ ‖Y z ω‖+‖μ z ω‖ := norm_sub_le _ _
      _ = Y z ω+μ z ω := by rw [Real.norm_eq_abs, abs_of_nonneg (h.output_bound z ω).1,
        Real.norm_eq_abs, abs_of_nonneg (h.mean_nonneg z ω)]
      _ ≤ _ := add_le_add (h.output_bound z ω).2 (hL z ω)
  have hFb (ξ : ℝ × ℝ) (ω : Ω) : ‖F ξ ω‖ ≤ a^2*((n:ℝ)^2*(K+L)) := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => hnorm _ ω).trans_eq (by simp [sq]; ring))
  have havg (ω : Ω) : (∫ ξ, F ξ ω ∂windowShiftLaw a) = ∫ z in D, (Y z ω-μ z ω) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      obtain ⟨_,hy,hμ⟩ := h.outside z hz ω
      simp only [hy,hμ,sub_self])]
    exact window_grid_average ((h.joint_output.sub h.joint_mean).comp
      (measurable_id.prodMk measurable_const)) (fun z => hnorm z ω) ha han
      (fun z hz => by
        obtain ⟨_,hy,hμ⟩ := h.outside z (fun hzD => hz (h.bounded_D hzD)) ω
        change Y z ω-μ z ω=0
        simp only [hy,hμ,sub_self])
  let : IsProbabilityMeasure (windowShiftLaw a) := windowShiftLaw_probability ha
  have hfinite (ξ : ℝ × ℝ) :
      (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
    have ht := window_source_finite_mgf_at_starts h (window_centers_separated (n := n) hsep ha.le ξ)
      (mul_nonneg hθ (sq_nonneg a)) hWa (fun i => hWs _) hW0 hWb hK
    have he : (Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2 ≤ 128*K^2*θ^2*R^2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      have hs : a^2 ≤ 16*R^2 := by nlinarith [h.radius_pos.trans_le h.radius_le]
      calc
        _ = (a*n)^2*a^2*θ^2*K^2/2 := by ring
        _ = 8*a^2*θ^2*K^2 := by rw [han]; ring
        _ ≤ 8*(16*R^2)*θ^2*K^2 := by gcongr
        _ = _ := by ring
    have ht' : (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
        (∫ ω, W ω ∂P) * Real.exp ((Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2) := by
      simpa only [F, mul_assoc] using ht
    exact ht'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (integral_nonneg hW0))
  have ht := window_jensen_mgf (Q := windowShiftLaw a) hmeas hFb hθ hWa hW0 hWb hfinite
  simpa only [havg] using ht

lemma window_source_weighted_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    (hK : 0 < K) {b : ℝ} (hb : 0 < b)
    {W : Ω → ℝ} (hWa : Measurable[mΩ] W)
    (hWs : ∀ z, Measurable[(h.start z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω*(if b < ∫ z in D, (Y z ω-μ z ω) then (1:ℝ) else 0) ∂P) ≤
      (∫ ω, W ω ∂P)*Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2)) := by
  classical
  let X (ω : Ω) := ∫ z in D, (Y z ω-μ z ω)
  let θ := b/(256*K^2*R^2)
  have hR : 0 < R := h.radius_pos.trans_le h.radius_le
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hXm : Measurable X := window_source_integral_measurable h
  obtain ⟨M,hM⟩ := hWb
  obtain ⟨B,hB⟩ := window_source_integral_bounded h
  have hEi : Integrable (fun ω => W ω*Real.exp (θ*X ω)) P :=
    window_integrable_nonneg (hWa.mul (hXm.const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (fun ω => mul_le_mul (hM ω) (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hB ω)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  have hIi : Integrable (fun ω => W ω*(if b<X ω then (1:ℝ) else 0)) P :=
    window_integrable_nonneg (hWa.mul (Measurable.ite (measurableSet_lt measurable_const hXm)
      measurable_const measurable_const))
      (fun ω => mul_nonneg (hW0 ω) (by split_ifs <;> norm_num))
      (fun ω => by split_ifs <;> simp only [mul_one,mul_zero]; exact hM ω; exact (hW0 ω).trans (hM ω))
  have hpoint (ω : Ω) : W ω*(if b<X ω then (1:ℝ) else 0) ≤
      Real.exp (-θ*b)*(W ω*Real.exp (θ*X ω)) := by
    rw [mul_left_comm,← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (hW0 ω)
    by_cases hh : b<X ω
    · rw [ite_eq_left hh]
      apply Real.one_le_exp
      nlinarith [mul_nonneg hθ (sub_nonneg.mpr hh.le)]
    · rw [ite_eq_right hh]
      exact (Real.exp_pos _).le
  have hmgf := window_source_mgf_pos_at_starts h hθ hWa hWs hW0 ⟨M,hM⟩ hK
  calc
    _ ≤ ∫ ω, Real.exp (-θ*b)*(W ω*Real.exp (θ*X ω)) ∂P :=
      integral_mono hIi (hEi.const_mul _) hpoint
    _ = Real.exp (-θ*b)*(∫ ω, W ω*Real.exp (θ*X ω) ∂P) := integral_const_mul _ _
    _ ≤ Real.exp (-θ*b)*((∫ ω, W ω ∂P)*Real.exp (128*K^2*θ^2*R^2)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      dsimp [θ]
      field_simp
      ring

end
end SLEExactGauge
end

end OAI
