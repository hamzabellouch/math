import OAI.Analysis.LipschitzHilbert.Trees.SourceKernelShells

namespace OAI

/-! The actual positive kernel tail is controlled by interval averages.
The constant is independent of the spatial scale. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem kernel_integral_of_interval_bounds (f : ℝ → ℝ) (hf : Measurable f)
    (C c r M : ℝ) (hr : 0<r) (hM : 0≤M)
    (hf0 : ∀ x, 0≤f x) (hbound : ∀ x, ‖f x‖≤C)
    (havg : ∀ n : ℕ,
      (∫ x in Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r), f x)≤12*((2:ℝ)^n*r)*M) :
    (∫ x, r⁻¹*lineEnvelope c r 1 x*f x)≤96*M := by
  let g := fun x => r⁻¹*lineEnvelope c r 1 x*f x
  have hg0 (x) : 0≤g x :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (lineEnvelope_nonneg _ _ _ _)) (hf0 x)
  have hgi : Integrable g :=
    ((integrable_lineEnvelope_one c r hr).const_mul r⁻¹).mul_bdd
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hfb (n : ℕ) : IntegrableOn f (Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r)) :=
    IntegrableOn.of_bound measure_Icc_lt_top hf.aestronglyMeasurable.restrict C
      (Filter.Eventually.of_forall hbound)
  have hshell (n : ℕ) :
      (∫ x in kernelShell c r n, g x)≤(48*M)*(1/2:ℝ)^n := by
    let t : ℝ := 2^n
    have ht : 0<t := by dsimp [t]; positivity
    let A : ℝ := r⁻¹*(4/t^2)
    have hA : 0≤A := by dsimp [A]; positivity
    have hlocal : (∫ x in kernelShell c r n, g x)≤
        A*∫ x in kernelShell c r n, f x := by
      rw [←integral_const_mul]
      apply setIntegral_mono_on hgi.integrableOn
        (((hfb n).mono_set (kernelShell_subset c r n)).const_mul A) (kernelShell_measurable c r n)
      intro x hx
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (kernelShell_envelope c r hr n hx) (inv_nonneg.mpr hr.le)) (hf0 x)
    have hsub : (∫ x in kernelShell c r n, f x)≤
        ∫ x in Icc (c-t*r) (c+t*r), f x :=
      setIntegral_mono_set (hfb n) (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall (kernelShell_subset c r n))
    calc
      _ ≤ A*(12*(t*r)*M) := hlocal.trans
        (mul_le_mul_of_nonneg_left (hsub.trans (havg n)) hA)
      _ = (48*M)*(1/2:ℝ)^n := by
        dsimp [A,t]
        rw [one_div_pow]
        field_simp
        ring
  have hgeo : Summable (fun n : ℕ => (48*M)*(1/2:ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_left _
  have hsum : (∑' n : ℕ, (48*M)*(1/2:ℝ)^n)=96*M := by
    rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]
    ring
  have hlin : ENNReal.ofReal (∫ x, g x)≤ENNReal.ofReal (96*M) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
    calc
      _ ≤ ∑' n : ℕ, ∫⁻ x in kernelShell c r n, ENNReal.ofReal (g x) := by
        simpa only [kernelShell_covers c r hr,Measure.restrict_univ] using
          lintegral_iUnion_le (kernelShell c r) (fun x => ENNReal.ofReal (g x))
      _ ≤ ∑' n : ℕ, ENNReal.ofReal ((48*M)*(1/2:ℝ)^n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [←ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
          (Filter.Eventually.of_forall hg0)]
        exact ENNReal.ofReal_le_ofReal (hshell n)
      _ = ENNReal.ofReal (96*M) := by
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hgeo,hsum]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤96*M)).mp hlin

/-- The kernel centered at any point within one scale of the evaluation
point is bounded by its actual three-grid maximal majorant. -/
theorem kernel_integral_le_threeGridMaximal (f : ℝ → ℝ) (hf : Measurable f)
    (hLp : MemLp f 2 volume) (C : ℝ) (hf0 : ∀ x, 0≤f x) (hbound : ∀ x, ‖f x‖≤C) :
    ∀ᵐ z ∂volume, ∀ c r : ℝ, 0<r → |z-c|≤r →
      (∫ x, r⁻¹*lineEnvelope c r 1 x*f x)≤96*DyadicLineGrid.threeGridMaximal f z := by
  filter_upwards [DyadicLineGrid.interval_average_le_threeGridMaximal hLp hf0] with z hz
  intro c r hr hzc
  apply kernel_integral_of_interval_bounds f hf C c r _ hr
    (DyadicLineGrid.threeGridMaximal_nonneg f z) hf0 hbound
  intro n
  have hpow : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  have hrad : 0<(2:ℝ)^n*r := mul_pos (by positivity) hr
  have hmem : z∈Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r) := by
    have h := hzc.trans (show r≤(2:ℝ)^n*r by nlinarith)
    exact ⟨by linarith [(abs_le.mp h).1],by linarith [(abs_le.mp h).2]⟩
  have h := (div_le_iff₀ (by positivity : 0<2*((2:ℝ)^n*r))).mp (hz c ((2:ℝ)^n*r) hrad hmem)
  nlinarith

end LipschitzHilbert

end

end OAI
