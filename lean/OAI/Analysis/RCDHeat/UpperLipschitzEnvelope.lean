import Mathlib
import OAI.Analysis.RCDHeat.HeatFisher

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: UpperLipschitzEnvelope, CompactMajorant, ProperTransportDuality. -/



section
open Set Metric Filter
open scoped Topology NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]
noncomputable def upperLipschitzEnvelope (f : X → ℝ) (L : ℝ≥0) (x : X) : ℝ :=
  sSup (Set.range (fun y => f y-(L:ℝ)*dist x y))
 theorem upperLipschitzEnvelope_bdd {f : X → ℝ} (hf : ∀x, f x ≤ 0) (L : ℝ≥0) (x : X) :
    BddAbove (Set.range (fun y => f y-(L:ℝ)*dist x y)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨y,rfl⟩
  exact sub_nonpos.mpr ((hf y).trans (mul_nonneg L.coe_nonneg dist_nonneg))
 theorem le_upperLipschitzEnvelope {f : X → ℝ} (hf : ∀x, f x ≤ 0) (L : ℝ≥0) (x : X) :
    f x ≤ upperLipschitzEnvelope f L x := by
  have h := le_csSup (upperLipschitzEnvelope_bdd hf L x) (mem_range_self x)
  simpa only [upperLipschitzEnvelope,dist_self,mul_zero,sub_zero] using h
 theorem upperLipschitzEnvelope_nonpos {f : X → ℝ} (hf : ∀x, f x ≤ 0) (L : ℝ≥0) (x : X) :
    upperLipschitzEnvelope f L x ≤ 0 := by
  apply csSup_le ⟨_,mem_range_self x⟩
  rintro _ ⟨y,rfl⟩
  exact sub_nonpos.mpr ((hf y).trans (mul_nonneg L.coe_nonneg dist_nonneg))
 theorem upperLipschitzEnvelope_lipschitz {f : X → ℝ} (hf : ∀x, f x ≤ 0) (L : ℝ≥0) :
    LipschitzWith L (upperLipschitzEnvelope f L) := by
  have hu (x z : X) : upperLipschitzEnvelope f L x ≤
      upperLipschitzEnvelope f L z+(L:ℝ)*dist x z := by
    apply csSup_le ⟨_,mem_range_self x⟩
    rintro _ ⟨y,rfl⟩
    have hy := le_csSup (upperLipschitzEnvelope_bdd hf L z) (mem_range_self y)
    change f y-(L:ℝ)*dist z y ≤ upperLipschitzEnvelope f L z at hy
    have hd := mul_le_mul_of_nonneg_left (dist_triangle z x y) L.coe_nonneg
    rw [dist_comm z x] at hd
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,abs_le]
  constructor
  · have hh := hu z x
    rw [dist_comm z x] at hh
    linarith
  · linarith [hu x z]
 theorem upperLipschitzEnvelope_tendsto {f : X → ℝ} (hf : ∀x, f x ≤ 0) {x : X}
    (hfc : ContinuousAt f x) :
    Tendsto (fun n : ℕ => upperLipschitzEnvelope f (n:ℝ≥0) x) atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hfc (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := exists_nat_gt ((-f x)/δ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (-f x)/δ < (n:ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hlarge : -f x < (n:ℝ)*δ := (div_lt_iff₀ hδ).mp hn'
  have hu : upperLipschitzEnvelope f (n:ℝ≥0) x ≤ f x+ε/2 := by
    apply csSup_le ⟨_,mem_range_self x⟩
    rintro _ ⟨y,rfl⟩
    by_cases hxy : dist y x < δ
    · have hh := hclose hxy
      rw [Real.dist_eq] at hh
      have hd := (abs_lt.mp hh).2
      have hmul : 0 ≤ (n:ℝ)*dist x y := mul_nonneg (Nat.cast_nonneg _) dist_nonneg
      change f y-(n:ℝ)*dist x y ≤ f x+ε/2
      linarith
    · have hd : δ ≤ dist x y := by simpa only [dist_comm] using le_of_not_gt hxy
      have hm := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      change f y-(n:ℝ)*dist x y ≤ f x+ε/2
      linarith [hf y]
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (le_upperLipschitzEnvelope hf _ x))]
  linarith
end RegularPointCoordinates
end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]
noncomputable def compactUpperApprox (p : X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  radialCutoff p ((n:ℝ)+1) x*upperLipschitzEnvelope f (n:ℝ≥0) x
 theorem compactUpperApprox_bounds (p : X) {f : X → ℝ} (hf : ∀x, f x ≤ 0) (n : ℕ) (x : X) :
    f x ≤ compactUpperApprox p f n x ∧ compactUpperApprox p f n x ≤ 0 := by
  have hθ := radialCutoff_bounds p ((n:ℝ)+1) x
  have hu := le_upperLipschitzEnvelope hf (n:ℝ≥0) x
  have h0 := upperLipschitzEnvelope_nonpos hf (n:ℝ≥0) x
  constructor
  · unfold compactUpperApprox
    nlinarith
  · exact mul_nonpos_of_nonneg_of_nonpos hθ.1 h0
 theorem compactUpperApprox_tendsto (p : X) {f : X → ℝ} (hf : ∀x, f x ≤ 0) {x : X}
    (hfc : ContinuousAt f x) : Tendsto (fun n => compactUpperApprox p f n x) atTop (𝓝 (f x)) := by
  apply Tendsto.congr' _ (upperLipschitzEnvelope_tendsto hf hfc)
  obtain ⟨N,hN⟩ := exists_nat_gt (dist p x)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hd : dist p x ≤ (n:ℝ)+1 := by
    have hh : (N:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp only [compactUpperApprox,radialCutoff_eq_one p (by positivity) hd,one_mul]
variable [ProperSpace X]
 theorem compactUpperApprox_hasCompactSupport (p : X) (f : X → ℝ) (n : ℕ) :
    HasCompactSupport (compactUpperApprox p f n) :=
  (radialCutoff_hasCompactSupport p (by positivity : 0 < (n:ℝ)+1)).mul_right
 theorem compactUpperApprox_lipschitz (p : X) {f : X → ℝ} (hf : ∀x, f x ≤ 0) (n : ℕ) :
    ∃L : ℝ≥0, LipschitzWith L (compactUpperApprox p f n) := by
  apply lipschitz_mul_compact_cutoff (radialCutoff_lipschitz p (by positivity))
    (upperLipschitzEnvelope_lipschitz hf _) (radialCutoff_hasCompactSupport p (by positivity))
  intro x
  rw [abs_of_nonneg (radialCutoff_bounds p ((n:ℝ)+1) x).1]
  exact (radialCutoff_bounds p ((n:ℝ)+1) x).2
variable [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
 theorem compactUpperApprox_integral_tendsto (p : X) (f : X →ᵇ ℝ) (hf : ∀x, f x ≤ 0) :
    Tendsto (fun n => ∫x, compactUpperApprox p f n x ∂ν) atTop (𝓝 (∫x, f x ∂ν)) := by
  have hb (n : ℕ) (x : X) : ‖compactUpperApprox p f n x‖ ≤ ‖f‖ := by
    rw [Real.norm_eq_abs,abs_of_nonpos (compactUpperApprox_bounds p hf n x).2]
    have hfB := f.norm_coe_le_norm x
    rw [Real.norm_eq_abs,abs_of_nonpos (hf x)] at hfB
    linarith [(compactUpperApprox_bounds p hf n x).1]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    obtain ⟨L,hL⟩ := compactUpperApprox_lipschitz p hf n
    exact hL.continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (hb n)
  · exact ae_of_all _ (fun x => compactUpperApprox_tendsto p hf f.continuous.continuousAt)
end RegularPointCoordinates
end

 

 

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
 theorem exists_support_sublinear (p : E → ℝ) (p0 : p 0 = 0)
    (padd : ∀ x y, p (x+y) ≤ p x+p y)
    (psm : ∀ c : ℝ, 0 < c → ∀ x, p (c • x) = c*p x) (x : E) :
    ∃ L : E →ₗ[ℝ] ℝ, L x = p x ∧ ∀ y, L y ≤ p y := by
  have hom (c : ℝ) (hc : 0 ≤ c) (y : E) : p (c • y) = c*p y := by
    rcases eq_or_lt_of_le hc with rfl | hc
    · rw [zero_smul, p0, zero_mul]
    · exact psm c hc y
  let f : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (p x) (fun c hc => by
    rcases smul_eq_zero.mp hc with rfl | hx
    · simp
    · simp [hx, p0])
  obtain ⟨L,hL,hp⟩ := exists_extension_of_le_sublinear f p psm padd (by
    rintro ⟨y,hy⟩
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    rcases le_total 0 c with hc | hc
    · exact (hom c hc x).ge
    · have hneg : -p x ≤ p (-x) := by
        have h := padd x (-x)
        rw [add_neg_cancel, p0] at h
        linarith
      have hmul := mul_le_mul_of_nonneg_left hneg (neg_nonneg.mpr hc)
      have he : c • x = (-c) • (-x) := by simp
      rw [he, hom (-c) (neg_nonneg.mpr hc)]
      nlinarith)
  refine ⟨L,?_,hp⟩
  have hfself : f ⟨x, Submodule.mem_span_singleton_self _⟩ = p x := by
    dsimp [f]
    exact LinearPMap.mkSpanSingleton'_apply_self x (p x) _ _
  exact (hL ⟨x, Submodule.mem_span_singleton_self _⟩).trans hfself
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def separatedSum (f : X →ᵇ ℝ) (g : Y →ᵇ ℝ) : X×Y →ᵇ ℝ :=
  f.compContinuous ⟨Prod.fst, continuous_fst⟩ + g.compContinuous ⟨Prod.snd, continuous_snd⟩

 theorem bounded_continuous_integrable (f : X →ᵇ ℝ) : Integrable f μ := f.integrable μ

 theorem separatedSum_integral_mono (f F : (X →ᵇ ℝ)) (g G : (Y →ᵇ ℝ))
    (h : separatedSum f g ≤ separatedSum F G) :
    (∫ x, f x ∂μ)+(∫ y, g y ∂ν) ≤ (∫ x, F x ∂μ)+(∫ y, G y ∂ν) := by
  have hy (x : X) : f x+(∫ y, g y ∂ν) ≤ F x+(∫ y, G y ∂ν) := by
    have hh := integral_mono ((integrable_const (f x)).add (bounded_continuous_integrable ν g))
      ((integrable_const (F x)).add (bounded_continuous_integrable ν G)) (fun y => h (x,y))
    simp only [Pi.add_apply] at hh
    simpa only [integral_add (integrable_const _) (bounded_continuous_integrable ν _),
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hh := integral_mono ((bounded_continuous_integrable μ f).add (integrable_const _))
    ((bounded_continuous_integrable μ F).add (integrable_const _)) hy
  simp only [Pi.add_apply] at hh
  simpa only [integral_add (bounded_continuous_integrable μ _) (integrable_const _),
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh

noncomputable def transportEnvelopeValues (h : (X×Y →ᵇ ℝ)) : Set ℝ :=
  {a | ∃ f : (X →ᵇ ℝ), ∃ g : (Y →ᵇ ℝ), h ≤ separatedSum f g ∧ a = (∫ x, f x ∂μ)+(∫ y, g y ∂ν)}

noncomputable def transportEnvelope (h : (X×Y →ᵇ ℝ)) : ℝ := sInf (transportEnvelopeValues μ ν h)

omit [BorelSpace X] [BorelSpace Y] [IsProbabilityMeasure ν] in
 theorem transportEnvelopeValues_nonempty (h : (X×Y →ᵇ ℝ)) :
    (transportEnvelopeValues μ ν h).Nonempty := by
  refine ⟨‖h‖, BoundedContinuousFunction.const X ‖h‖, 0, ?_, ?_⟩
  · intro xy
    change h xy ≤ ‖h‖+0
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, add_zero] using h.norm_coe_le_norm xy)
  · simp only [BoundedContinuousFunction.const_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero, add_zero,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

 theorem transportEnvelopeValues_bddBelow (h : (X×Y →ᵇ ℝ)) :
    BddBelow (transportEnvelopeValues μ ν h) := by
  refine ⟨-‖h‖, ?_⟩
  rintro a ⟨f,g,hfg,rfl⟩
  have hh : separatedSum (BoundedContinuousFunction.const X (-‖h‖)) 0 ≤ separatedSum f g := by
    intro xy
    change -‖h‖+0 ≤ f xy.1+g xy.2
    have hl : -‖h‖ ≤ h xy := (abs_le.mp (h.norm_coe_le_norm xy)).1
    have hu : h xy ≤ f xy.1+g xy.2 := hfg xy
    simpa only [add_zero] using hl.trans hu
  simpa only [BoundedContinuousFunction.const_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero, add_zero,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      separatedSum_integral_mono μ ν (BoundedContinuousFunction.const X (-‖h‖)) f 0 g hh

 theorem transportEnvelope_le (h : (X×Y →ᵇ ℝ)) (f : (X →ᵇ ℝ)) (g : (Y →ᵇ ℝ))
    (hfg : h ≤ separatedSum f g) : transportEnvelope μ ν h ≤ (∫x, f x ∂μ)+(∫y, g y ∂ν) :=
  csInf_le (transportEnvelopeValues_bddBelow μ ν h) ⟨f,g,hfg,rfl⟩

 theorem transportEnvelope_separatedSum (f : (X →ᵇ ℝ)) (g : (Y →ᵇ ℝ)) :
    transportEnvelope μ ν (separatedSum f g) = (∫x, f x ∂μ)+(∫y, g y ∂ν) := by
  apply le_antisymm (transportEnvelope_le μ ν _ f g le_rfl)
  apply le_csInf (transportEnvelopeValues_nonempty μ ν _)
  rintro a ⟨F,G,hFG,rfl⟩
  exact separatedSum_integral_mono μ ν f F g G hFG

 theorem transportEnvelope_zero : transportEnvelope μ ν (0 : (X×Y →ᵇ ℝ)) = 0 := by
  have h : (0 : (X×Y →ᵇ ℝ)) = separatedSum (0:(X →ᵇ ℝ)) (0:(Y →ᵇ ℝ)) := by ext; simp [separatedSum]
  rw [h, transportEnvelope_separatedSum]
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero, add_zero]

 theorem transportEnvelope_add (h k : (X×Y →ᵇ ℝ)) :
    transportEnvelope μ ν (h+k) ≤ transportEnvelope μ ν h + transportEnvelope μ ν k := by
  have hh : transportEnvelope μ ν (h+k)-transportEnvelope μ ν k ≤ transportEnvelope μ ν h := by
    apply le_csInf (transportEnvelopeValues_nonempty μ ν h)
    rintro a ⟨f,g,hfg,rfl⟩
    have hk : transportEnvelope μ ν (h+k)-((∫x, f x ∂μ)+(∫y, g y ∂ν)) ≤ transportEnvelope μ ν k := by
      apply le_csInf (transportEnvelopeValues_nonempty μ ν k)
      rintro b ⟨F,G,hFG,rfl⟩
      have hu := transportEnvelope_le μ ν (h+k) (f+F) (g+G) (fun xy => by
        change h xy+k xy ≤ (f xy.1+F xy.1)+(g xy.2+G xy.2)
        have hh := add_le_add (hfg xy) (hFG xy)
        change h xy+k xy ≤ (f xy.1+g xy.2)+(F xy.1+G xy.2) at hh
        linarith)
      simp only [BoundedContinuousFunction.add_apply, integral_add (bounded_continuous_integrable μ f)
        (bounded_continuous_integrable μ F), integral_add (bounded_continuous_integrable ν g)
        (bounded_continuous_integrable ν G)] at hu
      linarith
    linarith
  linarith

 theorem transportEnvelope_smul_le {c : ℝ} (hc : 0 < c) (h : (X×Y →ᵇ ℝ)) :
    transportEnvelope μ ν (c • h) ≤ c*transportEnvelope μ ν h := by
  suffices hh : transportEnvelope μ ν (c • h)/c ≤ transportEnvelope μ ν h by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
  apply le_csInf (transportEnvelopeValues_nonempty μ ν h)
  rintro a ⟨f,g,hfg,rfl⟩
  apply (div_le_iff₀ hc).mpr
  have hu := transportEnvelope_le μ ν (c • h) (c • f) (c • g) (fun xy => by
    change c*h xy ≤ c*f xy.1+c*g xy.2
    have hh := mul_le_mul_of_nonneg_left (hfg xy) hc.le
    change c*h xy ≤ c*(f xy.1+g xy.2) at hh
    linarith)
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] at hu
  linarith

 theorem transportEnvelope_smul {c : ℝ} (hc : 0 < c) (h : (X×Y →ᵇ ℝ)) :
    transportEnvelope μ ν (c • h) = c*transportEnvelope μ ν h := by
  apply le_antisymm (transportEnvelope_smul_le μ ν hc h)
  have hh := transportEnvelope_smul_le μ ν (inv_pos.mpr hc) (c • h)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hh'
end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
 theorem transportEnvelope_support (h : X×Y →ᵇ ℝ) :
    ∃ L : (X×Y →ᵇ ℝ) →ₗ[ℝ] ℝ, L h = transportEnvelope μ ν h ∧
      (∀ f : X×Y →ᵇ ℝ, 0 ≤ f → 0 ≤ L f) ∧
      (∀ f : X →ᵇ ℝ, ∀ g : Y →ᵇ ℝ, L (separatedSum f g) = (∫ x, f x ∂μ)+(∫ y, g y ∂ν)) := by
  obtain ⟨L,hL,hp⟩ := exists_support_sublinear (transportEnvelope μ ν) (transportEnvelope_zero μ ν)
    (transportEnvelope_add μ ν) (fun c hc f => transportEnvelope_smul μ ν hc f) h
  refine ⟨L,hL,?_,?_⟩
  · intro f hf
    have hn := (hp (-f)).trans (transportEnvelope_le μ ν (-f) 0 0 (by
      intro xy
      change -f xy ≤ 0+0
      have hh : (0:ℝ) ≤ f xy := hf xy
      linarith))
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, integral_zero, add_zero,
      map_neg, neg_nonpos] using hn
  · intro f g
    apply le_antisymm ((hp _).trans_eq (transportEnvelope_separatedSum μ ν f g))
    have he : -(separatedSum f g) = separatedSum (-f) (-g) := by
      ext xy
      change -(f xy.1+g xy.2) = -f xy.1+ -g xy.2
      ring
    have hn := hp (-(separatedSum f g))
    rw [map_neg, he, transportEnvelope_separatedSum] at hn
    simp only [BoundedContinuousFunction.neg_apply, integral_neg] at hn
    linarith
end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u
variable {X : Type u} [MetricSpace X] [ProperSpace X]

noncomputable def cutoff (p : X) (k : ℕ) : C_c(X,ℝ) where
  toFun := fun x => min 1 (max 0 ((k:ℝ)+1-dist p x))
  continuous_toFun := by fun_prop
  hasCompactSupport' := by
    apply HasCompactSupport.intro (isCompact_closedBall p ((k:ℝ)+1))
    intro x hx
    have hd : (k:ℝ)+1 < dist p x := not_le.mp (by simpa only [Metric.mem_closedBall, dist_comm] using hx)
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]

 theorem cutoff_bounds (p : X) (k : ℕ) (x : X) : 0 ≤ cutoff p k x ∧ cutoff p k x ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

 theorem cutoff_eq_one (p : X) (k : ℕ) {x : X} (hx : dist p x ≤ (k:ℝ)) :
    cutoff p k x = 1 := by
  change min 1 (max 0 ((k:ℝ)+1-dist p x)) = 1
  apply min_eq_left
  exact le_max_of_le_right (by linarith)

 theorem cutoff_tendsto (p x : X) : Tendsto (fun k => cutoff p k x) atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (dist p x)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with k hk
  exact (cutoff_eq_one p k (hN.trans (by exact_mod_cast hk))).symm

 theorem cutoff_prod {Y : Type*} [MetricSpace Y] [ProperSpace Y]
    (p : X) (q : Y) (k : ℕ) (x : X) (y : Y) :
    cutoff (p,q) k (x,y) = min (cutoff p k x) (cutoff q k y) := by
  change min 1 (max 0 ((k:ℝ)+1-dist (p,q) (x,y))) =
    min (min 1 (max 0 ((k:ℝ)+1-dist p x))) (min 1 (max 0 ((k:ℝ)+1-dist q y)))
  rw [Prod.dist_eq]
  by_cases hd : dist p x ≤ dist q y
  · rw [max_eq_right hd]
    exact (min_eq_right (min_le_min_left 1 (max_le_max_left 0 (sub_le_sub_left hd _)))).symm
  · have hd' := (not_le.mp hd).le
    rw [max_eq_left hd']
    exact (min_eq_left (min_le_min_left 1 (max_le_max_left 0 (sub_le_sub_left hd' _)))).symm

variable [MeasurableSpace X] [BorelSpace X]
 theorem cutoff_integral_tendsto (μ : Measure X) [IsFiniteMeasure μ] (p : X) :
    Tendsto (fun k => ∫ x, cutoff p k x ∂μ) atTop (𝓝 (μ.real univ)) := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (1:ℝ))
    (fun k => (show AEStronglyMeasurable (fun x => cutoff p k x) μ from (cutoff p k).continuous.aestronglyMeasurable))
    (integrable_const 1) (fun k => ae_of_all μ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_bounds p k x).1]
      exact (cutoff_bounds p k x).2))
    (ae_of_all μ (cutoff_tendsto p))
  simpa only [integral_const, smul_eq_mul, mul_one] using ht

end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

 theorem positive_transport_representation (p : X) (q : Y)
    (L : (X×Y →ᵇ ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f : X×Y →ᵇ ℝ, 0 ≤ f → 0 ≤ L f)
    (hsep : ∀ f : X →ᵇ ℝ, ∀ g : Y →ᵇ ℝ,
      L (separatedSum f g) = (∫x, f x ∂μ)+(∫y, g y ∂ν)) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧
      ∀ h : X×Y →ᵇ ℝ, (∫ xy, h xy ∂π) = L h := by
  let : Nonempty X := ⟨p⟩
  let : Nonempty Y := ⟨q⟩
  have hmono : Monotone L := by
    intro f g hfg
    have hp := hpos (g-f) (sub_nonneg.mpr hfg)
    rw [map_sub] at hp
    linarith
  have h1 : L (1 : X×Y →ᵇ ℝ) = 1 := by
    have heq : (1 : X×Y →ᵇ ℝ) = separatedSum (1 : X →ᵇ ℝ) (0 : Y →ᵇ ℝ) := by
      ext; simp [separatedSum]
    rw [heq, hsep]
    simp
  let j : C_c(X×Y,ℝ) →ₗ[ℝ] (X×Y →ᵇ ℝ) :=
    { toFun := fun f => f.toBoundedContinuousFunction
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl }
  let Λ : C_c(X×Y,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (L.comp j) (fun f hf => hpos (j f) hf)
  let π : Measure (X×Y) := RealRMK.rieszMeasure Λ
  have he (f : C_c(X×Y,ℝ)) : (∫ xy, f xy ∂π) = L (j f) :=
    RealRMK.integral_rieszMeasure Λ f
  let ψ : ℕ → C_c(X×Y,ℝ) := fun k => cutoff (p,q) k
  have hup (k : ℕ) : L (j (ψ k)) ≤ 1 := by
    rw [← h1]
    exact hmono (fun xy => (cutoff_bounds (p,q) k xy).2)
  have hbound (k : ℕ) : π (Metric.closedBall (p,q) k) ≤ 1 := by
    have hb := RealRMK.rieszMeasure_le_of_eq_one Λ
      (fun xy => (cutoff_bounds (p,q) k xy).1) (isCompact_closedBall (p,q) (k:ℝ))
      (fun xy hxy => cutoff_eq_one (p,q) k (by simpa only [Metric.mem_closedBall, dist_comm] using hxy))
    apply hb.trans
    change ENNReal.ofReal (L (j (ψ k))) ≤ 1
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hup k)
  have huniv : π univ ≤ 1 := by
    rw [← Metric.iUnion_closedBall_nat (p,q)]
    have hm : Monotone (fun k : ℕ => Metric.closedBall (p,q) (k:ℝ)) :=
      fun i k hik => Metric.closedBall_subset_closedBall (by exact_mod_cast hik)
    rw [hm.measure_iUnion]
    exact iSup_le hbound
  let : IsFiniteMeasure π := ⟨huniv.trans_lt (by simp)⟩
  have hlo (k : ℕ) : (∫x, cutoff p k x ∂μ)+(∫y, cutoff q k y ∂ν)-1 ≤ L (j (ψ k)) := by
    have hm : separatedSum (cutoff p k).toBoundedContinuousFunction
        (cutoff q k).toBoundedContinuousFunction - 1 ≤ j (ψ k) := by
      rintro ⟨x,y⟩
      change cutoff p k x+cutoff q k y-1 ≤ cutoff (p,q) k (x,y)
      rw [cutoff_prod]
      apply le_min <;> linarith [(cutoff_bounds p k x).2,(cutoff_bounds q k y).2]
    have hh := hmono hm
    rw [map_sub,h1,hsep] at hh
    exact hh
  have hlimit : Tendsto (fun k => L (j (ψ k))) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun k => (∫x, cutoff p k x ∂μ)+(∫y, cutoff q k y ∂ν)-1)
      (h := fun _ : ℕ => (1:ℝ)) _ tendsto_const_nhds hlo hup
    have ht := ((cutoff_integral_tendsto μ p).add (cutoff_integral_tendsto ν q)).sub_const 1
    simpa only [probReal_univ, one_add_one_eq_two, sub_self, show (2:ℝ)-1=1 by norm_num] using ht
  have hall (h : X×Y →ᵇ ℝ) : (∫xy, h xy ∂π) = L h := by
    let hc (k : ℕ) : C_c(X×Y,ℝ) :=
      ⟨⟨fun xy => h xy*ψ k xy, h.continuous.mul (ψ k).continuous⟩,
        (ψ k).hasCompactSupport.mul_left⟩
    have hi : Tendsto (fun k => ∫xy, hc k xy ∂π) atTop (𝓝 (∫xy, h xy ∂π)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => ‖h‖)
        (fun k => (show AEStronglyMeasurable (fun xy => hc k xy) π from (hc k).continuous.aestronglyMeasurable))
        (integrable_const _) (fun k => ae_of_all π (fun xy => ?_)) (ae_of_all π (fun xy => ?_))
      · change ‖h xy*ψ k xy‖ ≤ ‖h‖
        rw [norm_mul, Real.norm_eq_abs (ψ k xy), abs_of_nonneg (cutoff_bounds (p,q) k xy).1]
        exact (mul_le_mul (h.norm_coe_le_norm xy) (cutoff_bounds (p,q) k xy).2
          (cutoff_bounds (p,q) k xy).1 (norm_nonneg h)).trans_eq (mul_one _)
      · change Tendsto (fun k => h xy*cutoff (p,q) k xy) atTop (𝓝 (h xy))
        simpa only [mul_one] using tendsto_const_nhds.mul (cutoff_tendsto (p,q) xy)
    have herr (k : ℕ) : |L h-L (j (hc k))| ≤ ‖h‖*(1-L (j (ψ k))) := by
      have hle : h-j (hc k) ≤ ‖h‖ • (1-j (ψ k)) := by
        intro xy
        change h xy-h xy*ψ k xy ≤ ‖h‖*(1-ψ k xy)
        have hh := mul_le_mul_of_nonneg_right
          ((le_abs_self (h xy)).trans (h.norm_coe_le_norm xy))
          (sub_nonneg.mpr (cutoff_bounds (p,q) k xy).2)
        nlinarith
      have hge : -‖h‖ • (1-j (ψ k)) ≤ h-j (hc k) := by
        intro xy
        change -‖h‖*(1-ψ k xy) ≤ h xy-h xy*ψ k xy
        have hh := mul_le_mul_of_nonneg_right
          ((abs_le.mp (h.norm_coe_le_norm xy)).1)
          (sub_nonneg.mpr (cutoff_bounds (p,q) k xy).2)
        nlinarith
      have hh := hmono hle
      have hg := hmono hge
      simp only [map_sub,map_smul,smul_eq_mul,h1] at hh hg
      exact abs_le.mpr ⟨by nlinarith, hh⟩
    have hz : Tendsto (fun k => L h-L (j (hc k))) atTop (𝓝 0) := by
      have hzt : Tendsto (fun k => ‖h‖*(1-L (j (ψ k)))) atTop (𝓝 0) := by
        have ht : Tendsto (fun k => ‖h‖*(1-L (j (ψ k)))) atTop (𝓝 (‖h‖*(1-1))) :=
          tendsto_const_nhds.mul (tendsto_const_nhds.sub hlimit)
        simpa only [sub_self,mul_zero] using ht
      exact squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using herr k) hzt
    have heq : Tendsto (fun k => ∫xy, hc k xy ∂π) atTop (𝓝 (L h)) := by
      have hh : Tendsto (fun k => L h-(L h-L (j (hc k)))) atTop (𝓝 (L h-0)) :=
        tendsto_const_nhds.sub hz
      simpa only [sub_sub_cancel,sub_zero,← he] using hh
    exact tendsto_nhds_unique hi heq
  have hprob : IsProbabilityMeasure π := by
    apply isProbabilityMeasure_iff_real.mpr
    have hh := (hall 1).trans h1
    simpa using hh
  exact ⟨π,hprob,hall⟩
end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
 theorem proper_transport_primal_dual (p : X) (q : Y) (h : X×Y →ᵇ ℝ) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫xy, h xy ∂π) = transportEnvelope μ ν h := by
  let : Nonempty X := ⟨p⟩
  let : Nonempty Y := ⟨q⟩
  obtain ⟨L,hL,hpos,hsep⟩ := transportEnvelope_support μ ν h
  obtain ⟨π,hprob,he⟩ := positive_transport_representation μ ν p q L hpos hsep
  let : IsProbabilityMeasure π := hprob
  refine ⟨π,hprob,?_,?_,(he h).trans hL⟩
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map measurable_fst.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (π.map Prod.fst) from f.continuous.aestronglyMeasurable)]
    have hx : (∫xy, f xy.1 ∂π) = L (separatedSum f.toBoundedContinuousFunction (0:Y →ᵇ ℝ)) := by
      convert he (separatedSum f.toBoundedContinuousFunction (0:Y →ᵇ ℝ)) using 1
      congr 1
      funext xy
      change f xy.1 = f xy.1+0
      exact (add_zero _).symm
    rw [hx,hsep]
    simp
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    rw [integral_map measurable_snd.aemeasurable
      (show AEStronglyMeasurable (fun x => g x) (π.map Prod.snd) from g.continuous.aestronglyMeasurable)]
    have hx : (∫xy, g xy.2 ∂π) = L (separatedSum (0:X →ᵇ ℝ) g.toBoundedContinuousFunction) := by
      convert he (separatedSum (0:X →ᵇ ℝ) g.toBoundedContinuousFunction) using 1
      congr 1
      funext xy
      change g xy.2 = 0+g xy.2
      exact (zero_add _).symm
    rw [hx,hsep]
    simp
end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
 theorem coupling_sequence_compact (p : X) (q : Y) (π : ℕ → ProbabilityMeasure (X×Y))
    (hf : ∀ k, (π k : Measure (X×Y)).map Prod.fst = μ)
    (hs : ∀ k, (π k : Measure (X×Y)).map Prod.snd = ν) :
    ∃ σ : ProbabilityMeasure (X×Y), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (π ∘ φ) atTop (𝓝 σ) ∧ (σ : Measure (X×Y)).map Prod.fst = μ ∧
        (σ : Measure (X×Y)).map Prod.snd = ν := by
  let : Nonempty X := ⟨p⟩
  let : Nonempty Y := ⟨q⟩
  let μp : ProbabilityMeasure X := ⟨μ,inferInstance⟩
  let νp : ProbabilityMeasure Y := ⟨ν,inferInstance⟩
  have ht : IsTightMeasureSet {((ρ : ProbabilityMeasure (X×Y)) : Measure (X×Y)) | ρ ∈ range π} := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := μ)).subset
      rintro τ ⟨ω,⟨ρ,⟨k,rfl⟩,rfl⟩,rfl⟩
      exact hf k
    · apply (isTightMeasureSet_singleton (μ := ν)).subset
      rintro τ ⟨ω,⟨ρ,⟨k,rfl⟩,rfl⟩,rfl⟩
      exact hs k
  obtain ⟨σ,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  refine ⟨σ,φ,hφ,hlim,?_,?_⟩
  · have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (π ∘ φ) σ hlim continuous_fst
    have he (k : ℕ) : ((π ∘ φ) k).map Prod.fst = μp := by
      apply Subtype.ext
      exact hf (φ k)
    have hh : σ.map Prod.fst = μp := by
      have hc : Tendsto (fun _ : ℕ => μp) atTop
          (𝓝 μp) := tendsto_const_nhds
      exact tendsto_nhds_unique h (by simpa only [he] using hc)
    exact congrArg Subtype.val hh
  · have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (π ∘ φ) σ hlim continuous_snd
    have he (k : ℕ) : ((π ∘ φ) k).map Prod.snd = νp := by
      apply Subtype.ext
      exact hs (φ k)
    have hh : σ.map Prod.snd = νp := by
      have hc : Tendsto (fun _ : ℕ => νp) atTop
          (𝓝 νp) := tendsto_const_nhds
      exact tendsto_nhds_unique h (by simpa only [he] using hc)
    exact congrArg Subtype.val hh
end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {Z : Type*} [TopologicalSpace Z]
noncomputable def truncatedCost (c : C(Z,ℝ)) (hc : ∀ z, 0 ≤ c z) (n : ℕ) : Z →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => min (c z) (n:ℝ)) (c.continuous.min continuous_const) n (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hc z) (Nat.cast_nonneg n))]
      exact min_le_right _ _)
 theorem truncatedCost_apply (c : C(Z,ℝ)) (hc : ∀ z, 0 ≤ c z) (n : ℕ) (z : Z) :
    truncatedCost c hc n z = min (c z) (n:ℝ) := rfl
 theorem truncatedCost_nonneg (c : C(Z,ℝ)) (hc : ∀ z, 0 ≤ c z) (n : ℕ) (z : Z) :
    0 ≤ truncatedCost c hc n z := le_min (hc z) (Nat.cast_nonneg n)
 theorem truncatedCost_mono (c : C(Z,ℝ)) (hc : ∀ z, 0 ≤ c z) :
    Monotone (truncatedCost c hc) := by
  intro n m hnm z
  exact min_le_min le_rfl (Nat.cast_le.mpr hnm)
 theorem truncatedCost_iSup (c : C(Z,ℝ)) (hc : ∀ z, 0 ≤ c z) (z : Z) :
    (⨆ n : ℕ, ENNReal.ofReal (truncatedCost c hc n z)) = ENNReal.ofReal (c z) := by
  apply le_antisymm (iSup_le (fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  obtain ⟨n,hn⟩ := exists_nat_ge (c z)
  calc
    ENNReal.ofReal (c z) = ENNReal.ofReal (truncatedCost c hc n z) := by
      rw [truncatedCost_apply,min_eq_left hn]
    _ ≤ _ := by
      change ENNReal.ofReal (min (c z) (n:ℝ)) ≤ _
      exact le_iSup (fun k : ℕ => ENNReal.ofReal (min (c z) (k:ℝ))) n

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
 theorem coupling_of_truncations (p : X) (q : Y) (c : C(X×Y,ℝ)) (hc : ∀ xy, 0 ≤ c xy)
    (A : ℝ) (hA : ∀ n : ℕ, ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      (∫xy, truncatedCost c hc n xy ∂π) ≤ A) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫⁻xy, ENNReal.ofReal (c xy) ∂π) ≤ ENNReal.ofReal A := by
  choose π hp hf hs hb using hA
  let P (n : ℕ) : ProbabilityMeasure (X×Y) := ⟨π n,hp n⟩
  obtain ⟨σ,φ,hφ,hlim,hfσ,hsσ⟩ := coupling_sequence_compact μ ν p q P hf hs
  refine ⟨σ,inferInstance,hfσ,hsσ,?_⟩
  have hbound (n : ℕ) : (∫xy, truncatedCost c hc n xy ∂(σ : Measure (X×Y))) ≤ A := by
    have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (truncatedCost c hc n)
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop n] with k hk
    have hnk : n ≤ φ k := hk.trans (hφ.id_le k)
    let : IsProbabilityMeasure (π (φ k)) := hp (φ k)
    have hh := integral_mono ((truncatedCost c hc n).integrable (π (φ k)))
      ((truncatedCost c hc (φ k)).integrable (π (φ k))) (truncatedCost_mono c hc hnk)
    exact hh.trans (hb (φ k))
  have he : (fun xy => ENNReal.ofReal (c xy)) =
      (fun xy => ⨆n : ℕ, ENNReal.ofReal (truncatedCost c hc n xy)) := by
    funext xy
    exact (truncatedCost_iSup c hc xy).symm
  rw [he,lintegral_iSup (f := fun n xy => ENNReal.ofReal (truncatedCost c hc n xy))
    (fun n => ENNReal.measurable_ofReal.comp (truncatedCost c hc n).continuous.measurable)
    (fun n m hnm xy => ENNReal.ofReal_le_ofReal (truncatedCost_mono c hc hnm xy))]
  apply iSup_le
  intro n
  rw [← ofReal_integral_eq_lintegral_ofReal ((truncatedCost c hc n).integrable (σ : Measure (X×Y)))
    (ae_of_all _ (truncatedCost_nonneg c hc n))]
  exact ENNReal.ofReal_le_ofReal (hbound n)
end BoundedTransport
end RegularPointCoordinates

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction
namespace RegularPointCoordinates
namespace BoundedTransport
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
 

 theorem coupling_of_dual_bound (p : X) (q : Y) (c : C(X×Y,ℝ)) (hc : ∀ xy, 0 ≤ c xy)
    (A : ℝ) (hA : ∀ f : X →ᵇ ℝ, ∀ g : Y →ᵇ ℝ,
      (∀ xy : X×Y, f xy.1+g xy.2 ≤ c xy) → (∫x, f x ∂μ)+(∫y,g y ∂ν) ≤ A) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫⁻xy, ENNReal.ofReal (c xy) ∂π) ≤ ENNReal.ofReal A := by
  apply coupling_of_truncations μ ν p q c hc A
  intro n
  obtain ⟨π,hp,hf,hs,he⟩ := proper_transport_primal_dual μ ν p q (-(truncatedCost c hc n))
  refine ⟨π,hp,hf,hs,?_⟩
  have hl : -A ≤ transportEnvelope μ ν (-(truncatedCost c hc n)) := by
    apply le_csInf (transportEnvelopeValues_nonempty μ ν _)
    rintro a ⟨f,g,hfg,rfl⟩
    have hh := hA (-f) (-g) (fun xy => by
      have h := hfg xy
      change -truncatedCost c hc n xy ≤ f xy.1+g xy.2 at h
      change -f xy.1+-g xy.2 ≤ c xy
      have hm : truncatedCost c hc n xy ≤ c xy := min_le_left _ _
      linarith)
    simp only [BoundedContinuousFunction.neg_apply,integral_neg] at hh
    linarith
  simp only [BoundedContinuousFunction.neg_apply,integral_neg] at he
  linarith
end BoundedTransport
end RegularPointCoordinates

end OAI
