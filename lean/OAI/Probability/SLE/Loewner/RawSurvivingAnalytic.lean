import OAI.Probability.SLE.Loewner.RawInverseHolomorphic
import OAI.Probability.SLE.Loewner.TargetForwardAnalytic
import OAI.Probability.SLE.Loewner.SmoothRawTrace

namespace OAI

/-! The raw surviving set is an open conformal image of the half-plane.
For a smooth driver its radial tip lies on the boundary of this set. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge

lemma Target.surviving_eq_inverse_image (b : Driver) (T : ℝ≥0) :
    {z | Surviving 1 b z T} = inverseFlow 1 b T '' upperHalfPlane := by
  ext z
  constructor
  · intro hz
    refine ⟨flow 1 b z T,surviving_flow_mem_upperHalfPlane 1 b z T T.coe_nonneg hz,?_⟩
    exact inverseFlow_eq_of_surviving 1 b T T.coe_nonneg z _ hz rfl
  · rintro ⟨w,hw,rfl⟩
    exact inverseFlow_surviving 1 (by norm_num) b T w hw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

lemma RegularSLEPresentation.raw_surviving_isOpen (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (b : Target.Driver) (T : ℝ≥0) :
    IsOpen {z | Target.Surviving 1 b z T} := by
  rw [Target.surviving_eq_inverse_image]
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨w,hw,rfl⟩
  exact univalent_nhds_le_map isOpen_upperHalfPlane (a.raw_inverse_holomorphic hκ b T)
    (Target.inverseFlow_injOn b T) hw (image_mem_map (isOpen_upperHalfPlane.mem_nhds hw))

lemma RegularSLEPresentation.raw_forward_holomorphic (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (b : Target.Driver) (T : ℝ≥0) :
    DifferentiableOn ℂ (fun z => Target.flow 1 b z T) {z | Target.Surviving 1 b z T} :=
  Target.differentiableOn_flow_of_inverse 1 (by norm_num) b T
    (a.raw_inverse_holomorphic hκ b T) (fun _ hz => a.raw_inverse_deriv_ne_zero hκ b T hz)

theorem RegularSLEPresentation.smooth_raw_tip_not_surviving
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ)
    (b : Target.Driver) (T : ℝ≥0) (b' : ℝ → ℝ)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt (Target.driverValue b)
      (b' t) (Icc 0 (T : ℝ)) t)
    {L : ℝ} (hL : 0 ≤ L) (hb : ∀ t ∈ Icc 0 (T : ℝ), |b' t| ≤ L) :
    ¬Target.Surviving 1 b (Target.trace 1 b T) T := by
  intro hs
  have hc := ((a.raw_forward_holomorphic hκ b T).differentiableAt
    ((a.raw_surviving_isOpen hκ b T).mem_nhds hs)).continuousAt
  have ht := hc.tendsto.comp (Target.tendsto_inverseFlow_smooth_trace b T b' hd hL hb)
  have he : (fun y : ℝ => Target.flow 1 b
      (Target.inverseFlow 1 b T ((b T : ℂ)+(y : ℂ)*Complex.I)) T)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun y => (b T : ℂ)+(y : ℂ)*Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact Target.flow_inverseFlow 1 (by norm_num) b T _
      (by simpa [upperHalfPlane] using hy)
  have hv : Tendsto (fun y : ℝ => (b T : ℂ)+(y : ℂ)*Complex.I)
      (𝓝[>] 0) (𝓝 (b T : ℂ)) := by
    have hc' : Continuous (fun y : ℝ => (b T : ℂ)+(y : ℂ)*Complex.I) := by fun_prop
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
      (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
  have hval := tendsto_nhds_unique ht (hv.congr' he.symm)
  have hp := Target.surviving_flow_mem_upperHalfPlane 1 b _ T T.coe_nonneg hs
  rw [hval] at hp
  simp [upperHalfPlane] at hp

end SLEExactGauge

end

end OAI
