import OAI.Probability.SLE.Stochastic.PlanarDynkinStep
import OAI.Probability.SLE.OptionalStopping

namespace OAI

/-! Dynkin's formula for compact smooth tests of the actual planar Wiener
path, relative to its full two-coordinate past. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planar_compact_eval_integrable
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (A : Set (Driver×Driver)) (t : ℝ≥0) :
    Integrable (fun b => f (planarWiener t b)) ((W.prod W).restrict A) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K,hK,_⟩ := compact_smooth_bounded_lipschitz f hf hc
  exact Integrable.of_bound (hf.continuous.measurable.comp (measurable_planarWiener t)).aestronglyMeasurable K
    (Eventually.of_forall fun b => hK _)

lemma planar_generator_joint_measurable
    (f : ℝ×ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Measurable (fun p : ℝ×(Driver×Driver) => planarGenerator f (planarWiener p.1.toNNReal p.2)) := by
  have ht : Measurable (fun p : ℝ×(Driver×Driver) => (p.1.toNNReal,p.2)) := by fun_prop
  exact (planarGenerator_smooth f hf).continuous.measurable.comp (planarWiener_joint_measurable.comp ht)

theorem planarWiener_dynkin
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (s t : ℝ≥0) (hst : s≤t) (A : Set (Driver×Driver))
    (hA : MeasurableSet[planarWienerFiltration s] A) :
    (∫ b in A, f (planarWiener t b)-f (planarWiener s b) ∂W.prod W) =
      ∫ b in A, (∫ u in (s:ℝ)..(t:ℝ), planarGenerator f (planarWiener u.toNNReal b)) ∂W.prod W := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C,hC⟩ := planarWiener_one_step_error W hW f hf hc
  obtain ⟨D,hD,_⟩ := planarGenerator_bounded_lipschitz f hf hc
  let G (u : ℝ) (b : Driver×Driver) := planarGenerator f (planarWiener u.toNNReal b)
  have hG : Measurable (Function.uncurry G) := planar_generator_joint_measurable f hf
  have hGb (u b) : |G u b|≤D := hD _
  let c (r : ℝ≥0) := ∫ b in A, (∫ u in (s:ℝ)..(s+r:ℝ≥0), G u b) ∂W.prod W
  let v (r : ℝ≥0) := ∫ b in A, f (planarWiener r b) ∂W.prod W
  let F (r : ℝ≥0) := v (s+r)-c r
  have hI (r) := planar_compact_eval_integrable W hW f hf hc A r
  have hinc (r δ : ℝ≥0) : |F (r+δ)-F r|≤(C:ℝ)*(δ:ℝ)*Real.sqrt δ := by
    have hsr : s ≤ s+r := le_add_of_nonneg_right zero_le
    have hA' : MeasurableSet[planarWienerFiltration (s+r)] A :=
      planarWienerFiltration.mono hsr A hA
    have h := hC (s+r) δ A hA'
    have hc' : c (r+δ)-c r =
        ∫ b in A, (∫ u in (s+r:ℝ≥0)..((s+r)+δ:ℝ≥0), G u b) ∂W.prod W := by
      dsimp only [c]
      rw [← add_assoc]
      exact bounded_interval_integral_expectation_sub _ _ _
        (by exact_mod_cast hsr) (by simp only [NNReal.coe_add]; linarith [δ.coe_nonneg]) G hG D hGb
    have hv : v ((s+r)+δ)-v (s+r) =
        ∫ b in A, f (planarWiener ((s+r)+δ) b)-f (planarWiener (s+r) b) ∂W.prod W :=
      (integral_sub (hI _) (hI _)).symm
    have he : F (r+δ)-F r =
        (∫ b in A, f (planarWiener ((s+r)+δ) b)-f (planarWiener (s+r) b) ∂W.prod W)-
        (∫ b in A, (∫ u in (s+r:ℝ≥0)..((s+r)+δ:ℝ≥0), G u b) ∂W.prod W) := by
      dsimp only [F]
      rw [← add_assoc]
      linarith
    rw [he]
    exact h
  have hsqrt : Tendsto (fun δ : ℝ≥0 => Real.sqrt δ) (𝓝 0) (𝓝 0) := by
    have hh : Continuous (fun δ : ℝ≥0 => Real.sqrt δ) := by fun_prop
    simpa only [ContinuousAt,NNReal.coe_zero,Real.sqrt_zero] using hh.continuousAt (x := 0)
  have heq := eq_of_uniform_small_increment F (fun δ => Real.sqrt δ) C hsqrt hinc 0 (t-s) zero_le
  have hc0 : c 0=0 := by simp [c]
  have ht : s+(t-s)=t := add_tsub_cancel_of_le hst
  change v (s+(t-s))-c (t-s)=v (s+0)-c 0 at heq
  rw [ht,add_zero,hc0,sub_zero] at heq
  have hc' : c (t-s)=∫ b in A, (∫ u in (s:ℝ)..(t:ℝ), G u b) ∂W.prod W := by
    dsimp only [c]
    rw [ht]
  rw [integral_sub (hI _) (hI _)]
  change v t-v s=_
  linarith

end SLEExactGauge

end

end OAI
