import OAI.Probability.SLE.Loewner.TargetDensityBound
import OAI.Probability.SLE.Angle.AngleMomentWeight

namespace OAI

/-! The center-hit decay cancels the finite change-of-law density.
Consequently every terminal disk moment has one integrable angular bound. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem uniform_density_disk_terminal_moments
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (m : ℕ) :
    ∃ M : ℝ≥0∞, M<∞ ∧ ∀ (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ), 0≤ℓ →
      (∫⁻ ω, ENNReal.ofReal (Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ *
        (C.diskTerminalScalar θ hθ ω)^m) ∂P) ≤
          M*ENNReal.ofReal (1/(Real.sin θ)^greenExponent κ) := by
  obtain ⟨M,hM,hbound⟩ := C.uniform_diskTerminalScalar_centered_moments hB hc h0 hκ hκ8 F hw hgrowth m
  refine ⟨M,hM,?_⟩
  intro θ hθ ℓ hℓ
  let u := 4*ℓ/κ
  let e := Real.exp (-u)
  let c := Real.exp (u*codimension κ)/(Real.sin θ)^greenExponent κ
  let E := diskCenterHit γ G θ e
  let Z := C.diskTerminalScalar θ hθ
  have hs : 0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hc0 : 0≤c := div_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.le _)
  have hu : 0≤u := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have he : 0<e := Real.exp_pos _
  have he1 : e≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have hE := measurableSet_diskCenterHit
    (fun t => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B t))) hc
    κ θ hθ γ G F hw e he he1
  have hZ (ω) : 0≤Z ω := compactWeightedMass_nonneg _ _ _
  have hd (ω) : Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ ≤
      E.indicator (fun _ => c) ω := by
    exact Target.levelDensity_le_centerHit κ hκ hκ8 _ _ ((hc ω).const_mul _)
      (γ ω) (G ω) (F ω) (hw ω) (Target.normalizedDriver_matches κ hκ B hc h0 ω) θ hθ ℓ hℓ
  have hp : (∫⁻ ω, ENNReal.ofReal (Target.levelDensity κ θ
        (Target.normalizedDriver κ B hc h0 ω) ℓ * (Z ω)^m) ∂P) ≤
      ENNReal.ofReal c * ∫⁻ ω in E, (ENNReal.ofReal (Z ω))^m ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← lintegral_indicator hE]
    apply lintegral_mono
    intro ω
    by_cases hω : ω∈E
    · rw [indicator_of_mem hω]
      rw [← ENNReal.ofReal_pow (hZ ω),← ENNReal.ofReal_mul hc0]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by simpa only [indicator_of_mem hω] using hd ω) (pow_nonneg (hZ ω) m))
    · rw [indicator_of_notMem hω]
      apply le_of_eq
      apply ENNReal.ofReal_eq_zero.mpr
      have hh : Target.levelDensity κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ ≤ 0 := by
        simpa only [indicator_of_notMem hω] using hd ω
      exact mul_nonpos_of_nonpos_of_nonneg hh (pow_nonneg (hZ ω) m)
  have hec : c * e^codimension κ=1/(Real.sin θ)^greenExponent κ := by
    dsimp only [c,e]
    rw [← Real.exp_mul]
    field_simp [(Real.rpow_pos_of_pos hs (greenExponent κ)).ne']
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    _ ≤ ENNReal.ofReal c * ∫⁻ ω in E, (ENNReal.ofReal (Z ω))^m ∂P := hp
    _ ≤ ENNReal.ofReal c * (M*ENNReal.ofReal (e^codimension κ)) :=
      mul_le_mul' le_rfl (hbound θ hθ e he he1)
    _ = _ := by rw [mul_left_comm,← ENNReal.ofReal_mul hc0,hec]

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
