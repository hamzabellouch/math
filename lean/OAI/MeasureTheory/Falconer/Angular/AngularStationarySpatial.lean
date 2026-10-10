import OAI.MeasureTheory.Falconer.Angular.MeasurableAngularJets
import OAI.MeasureTheory.Falconer.Angular.AngularOriginalFarPartition
import OAI.MeasureTheory.Falconer.Radial.RadialFailureMass

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def angularPairAngle (x y : Plane) : ℝ :=
  sourceAngle (sourceRadialUnit y x)

theorem angularPairAngle_measurable :
    Measurable (fun z : Plane × Plane => angularPairAngle z.1 z.2) :=
  measurable_sourceAngle.comp (measurable_sourceRadialUnit_joint.comp measurable_swap)

theorem angularPairAngle_represents (x y : Plane) :
    x-y = ‖x-y‖ • sourceDirection (angularPairAngle x y) := by
  have he := congrArg (fun u : UnitCircle => (u:Plane))
    (sourceUnitDirection_sourceAngle (sourceRadialUnit y x))
  change sourceDirection (angularPairAngle x y) = sourceRadialVector y x at he
  rw [he]
  by_cases hx : x=y
  · simp [hx]
  · simp only [sourceRadialVector,hx,↓reduceIte,smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)),one_smul]

noncomputable def angularPairStationary (β : Plane → UnitCircle → ℂ)
    (n : ℕ) (x y : Plane) (r : ℝ) : ℂ :=
  fullCircleStationaryExpansion (r*‖x-y‖)
    (fun t => β x (sourceUnitDirection (t+angularPairAngle x y))*
      conj (β y (sourceUnitDirection (t+angularPairAngle x y)))) n

theorem angularPairStationary_measurable (β : Plane → UnitCircle → ℂ)
    (hm : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hd : ∀ x, ContDiff ℝ ∞ (fun t => β x (sourceUnitDirection t))) (n : ℕ) :
    Measurable (fun p : (Plane × Plane) × ℝ => angularPairStationary β n p.1.1 p.1.2 p.2) := by
  let f := fun z : Plane × Plane => fun t =>
    β z.1 (sourceUnitDirection (t+angularPairAngle z.1 z.2))*
      conj (β z.2 (sourceUnitDirection (t+angularPairAngle z.1 z.2)))
  have hf : Measurable (fun p : (Plane × Plane) × ℝ => f p.1 p.2) := by
    have ha := angularPairAngle_measurable.comp (measurable_fst : Measurable (Prod.fst : (Plane × Plane) × ℝ → _))
    have hu := continuous_sourceUnitDirection.measurable.comp (measurable_snd.add ha)
    exact (hm.comp ((measurable_fst.comp measurable_fst).prodMk hu)).mul
      (Complex.continuous_conj.measurable.comp (hm.comp ((measurable_snd.comp measurable_fst).prodMk hu)))
  have hdf (z : Plane × Plane) : ContDiff ℝ ∞ (f z) :=
    ((hd z.1).comp (contDiff_id.add contDiff_const)).mul
      (Complex.conjCLE.contDiff.comp ((hd z.2).comp (contDiff_id.add contDiff_const)))
  exact (measurable_stationary_family f hf hdf n).comp
    (show Measurable (fun p : (Plane × Plane) × ℝ => (p.1,p.2*‖p.1.1-p.1.2‖)) from by fun_prop)

noncomputable def angularStationarySpatialKernel (β γ : Plane → UnitCircle → ℂ)
    (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) (x : Fin 4 → Plane) : ℂ :=
  ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
    (angularPairStationary β n (x 0) (x 1) r * angularPairStationary γ n (x 2) (x 3) r))

theorem angularStationarySpatialKernel_measurable (β γ : Plane → UnitCircle → ℂ)
    (hmβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hmγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    (hdβ : ∀ x, ContDiff ℝ ∞ (fun t => β x (sourceUnitDirection t)))
    (hdγ : ∀ x, ContDiff ℝ ∞ (fun t => γ x (sourceUnitDirection t)))
    (n : ℕ) (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) :
    Measurable (angularStationarySpatialKernel β γ n v Ψ) := by
  have h1 := (angularPairStationary_measurable β hmβ hdβ n).comp
    (show Measurable (fun p : (Fin 4 → Plane) × ℝ => ((p.1 0,p.1 1),p.2)) from by fun_prop)
  have h2 := (angularPairStationary_measurable γ hmγ hdγ n).comp
    (show Measurable (fun p : (Fin 4 → Plane) × ℝ => ((p.1 2,p.1 3),p.2)) from by fun_prop)
  have hi : Measurable (fun p : (Fin 4 → Plane) × ℝ => Ψ (p.2/(2:ℝ)^v) •
      (angularPairStationary β n (p.1 0) (p.1 1) p.2 * angularPairStationary γ n (p.1 2) (p.1 3) p.2)) :=
    (hΨ.comp (by fun_prop)).smul (h1.mul h2)
  exact (show Measurable (fun _ : Fin 4 → Plane => ((2:ℝ)^v)⁻¹) from measurable_const).smul
    (hi.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem spatial_replacement_integral_bound_ae (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (S : Set (Fin 4 → Plane)) (F G : (Fin 4 → Plane) → ℂ)
    (hF : IntegrableOn F S μ) (hG : Measurable G) {ε : ℝ}
    (hb : ∀ᵐ x ∂μ.restrict S, ‖F x-G x‖ ≤ ε) :
    ‖(∫ x in S, F x ∂μ)-(∫ x in S, G x ∂μ)‖ ≤ ε*μ.real S := by
  have hi : Integrable G (μ.restrict S) := by
    apply (hF.norm.add (integrable_const ε)).mono' hG.aestronglyMeasurable
    filter_upwards [hb] with x hx
    have ht := norm_add_le (F x) (G x-F x)
    rw [add_sub_cancel,norm_sub_rev (G x) (F x)] at ht
    change ‖G x‖ ≤ ‖F x‖+ε
    exact ht.trans (add_le_add (le_refl _) hx)
  rw [← integral_sub hF hi]
  simpa only [Measure.real,Measure.restrict_apply_univ] using norm_integral_le_of_norm_le_const hb

end PlanarFalconer

end OAI
