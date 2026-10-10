import OAI.Geometry.Convex.GeneralMahler.Smoothing

namespace OAI
/-! Integration-by-parts formula for the normal measure.
Derived by differentiating translations; includes Lipschitz projections. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Filter Topology Set Real WithLp
open scoped RealInnerProductSpace ENNReal NNReal
namespace GeneralMahler
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem smoothG_translate_derivative {f : Rn n → F}
    (hf : PolyBound f) (hc : Continuous f) (a : Rn n)
    (hD : ∀ᵐ x ∂normal n, HasFDerivAt f (fderiv ℝ f (x+a)) (x+a))
    {g : Rn n → ℝ} (hg : Integrable g (normal n))
    (hg' : ∀ x, ∀ b ∈ ball a 1, ‖f (x+b) - f (x+a)‖ ≤ g x * ‖b-a‖) :
    Integrable (fun x => fderiv ℝ f (x+a)) (normal n) ∧
      HasFDerivAt (smoothG f) (∫ x, fderiv ℝ f (x+a) ∂normal n) a := by
  let FF := fun (y x : Rn n) => f (x+y)
  have hF (y) : AEStronglyMeasurable (FF y) (normal n) :=
    (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hfa := (hf.comp ((PolyBound.id (X := Rn n)).add (PolyBound.const a))).gaussian_integrable (hF a)
  have he₁ : Measurable (fun x => fderiv ℝ f (x+a)) :=
    (measurable_fderiv _ f).comp (continuous_id.add continuous_const).measurable
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' (F := FF)
    (ball_mem_nhds a zero_lt_one)
    (fun y _ => hF y) hfa he₁.aestronglyMeasurable (ae_of_all _ hg') hg
  filter_upwards [hD] with x hx
  simpa only [FF,Function.comp_def, zero_add, ContinuousLinearMap.comp_id] using
    hx.comp a ((hasFDerivAt_const x a).add (hasFDerivAt_id a))

theorem smoothG_derivative_lipschitz {f : Rn n → F} {K : ℝ≥0} (h : LipschitzWith K f)
    (a : Rn n) :
    Integrable (fun x => fderiv ℝ f (x+a)) (normal n) ∧
      HasFDerivAt (smoothG f) (∫ x, fderiv ℝ f (x+a) ∂normal n) a := by
  have H : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := h.ae_differentiableAt
  have hh : ∀ᵐ x ∂normal n, DifferentiableAt ℝ f (x+a) :=
    normal_ac.ae_le ((measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae.eventually H)
  refine smoothG_translate_derivative (PolyBound.lipschitz h) h.continuous a
    (hh.mono fun x hx => hx.hasFDerivAt) (g := fun x => K) (integrable_const _) ?_
  intro x b _
  simpa only [← dist_eq_norm, dist_add_left] using h.dist_le_mul (x+b) (x+a)

theorem normal_IBP {f : Rn n → F}
    (hf : PolyBound f) (hc : Continuous f)
    (hD : ∀ᵐ x ∂normal n, DifferentiableAt ℝ f x)
    {g : Rn n → ℝ} (hg : Integrable g (normal n))
    (hg' : ∀ x, ∀ b : Rn n, ‖b‖ < 1 → ‖f (x+b) - f x‖ ≤ g x * ‖b‖)
    (v : Rn n) :
    (∫ x, fderiv ℝ f x v ∂normal n) = ∫ x, ⟪x,v⟫ • f x ∂normal n := by
  obtain ⟨hw,hde⟩ := smoothG_translate_derivative hf hc 0
    (by simpa using (hD.mono fun x hx => hx.hasFDerivAt)) hg
    (by simpa only [sub_zero,add_zero,mem_ball,dist_zero_right] using hg')
  simp only [add_zero] at hw hde
  obtain ⟨hw',hde'⟩ := smoothG_hasFDeriv hf hc.stronglyMeasurable 0
  rw [← ContinuousLinearMap.integral_apply hw, hde.unique hde',
    ContinuousLinearMap.integral_apply hw', normal_integral]
  apply integral_congr_ae; filter_upwards with x; simp [G',smul_smul]

theorem normal_IBP_lipschitz {f : Rn n → F}
    {K : ℝ≥0} (h : LipschitzWith K f) (v : Rn n) :
    (∫ x, fderiv ℝ f x v ∂normal n) = ∫ x, ⟪x,v⟫ • f x ∂normal n :=
  normal_IBP (PolyBound.lipschitz h) h.continuous
    (normal_ac.ae_le h.ae_differentiableAt) (g := fun x => K) (integrable_const _)
    (fun x b _ => by simpa [dist_eq_norm] using h.dist_le_mul (x+b) x) v

end GeneralMahler

end

end OAI
