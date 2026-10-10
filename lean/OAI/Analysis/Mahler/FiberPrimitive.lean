import OAI.Analysis.Mahler.AngularFibers
import OAI.Analysis.Mahler.AngularIntegrals
import OAI.Analysis.Mahler.PrimitiveBound

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- The actual chosen angular fiber satisfies the singular sine estimate. -/
theorem fiberAngle_sine_bound {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) :
    sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (fiberAngle q r) := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have hs := fiberAngle_spec hmem
  have h := MahlerConformal.sine_bound hmem.1 hmem.2.1 ⟨hs.1.1.le,hs.1.2.le⟩
  rw [hs.2, ← hq] at h
  exact h

/-- The small-error estimate for the angular
fibers; measurability and the sine estimate are consequences, not premises. -/
theorem fiber_primitive_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ r₀ ∈ Ico (0 : ℝ) 1,
      ∀ q : ℝ, radialMap r₀ = |q| → ∀ s ∈ Ico r₀ 1,
        IntervalIntegrable (radialPrimitiveDensity (fiberAngle q) m) volume r₀ s ∧
        (∫ r in r₀..s, radialPrimitiveDensity (fiberAngle q) m r) < s^(2*m : ℝ)+ε := by
  obtain ⟨m₀,hm₀⟩ := radial_primitive_uniform_small hε
  refine ⟨m₀, ?_⟩
  intro m hm r₀ hr₀ q hq s hs
  exact hm₀ m hm r₀ hr₀ (fiberAngle q) (measurable_fiberAngle q)
    (fun r hr => fiberAngle_sine_bound hr₀.1 hq hr) s hs

/-- A concrete nonnegative error function, valid also for every smaller m≥2. -/
noncomputable def planarError (m : ℝ) : ℝ := max 0 (Real.pi*errorEnvelope m)

lemma planarError_nonneg (m : ℝ) : 0 ≤ planarError m := le_max_left _ _

lemma planarError_tendsto_zero : Filter.Tendsto planarError Filter.atTop (nhds 0) := by
  have h := error_envelope_tendsto_zero.const_mul Real.pi
  have hh := Filter.Tendsto.max (tendsto_const_nhds (x := (0 : ℝ))) h
  change Filter.Tendsto (fun m : ℝ => max 0 (Real.pi*errorEnvelope m)) Filter.atTop (nhds 0)
  simpa only [mul_zero, max_self] using! hh

/-- The actual radial primitive obeys the concrete error bound for every m≥2,
not only eventually large m. -/
theorem fiber_primitive_bound {q r₀ m s : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hs : s ∈ Ico r₀ 1) :
    (∫ r in r₀..s, radialPrimitiveDensity (fiberAngle q) m r) ≤ s^(2*m : ℝ)+planarError m := by
  have hp := radial_primitive_integral_bound (measurable_fiberAngle q) hm hr₀ hs.1 hs.2
    (fun r hr => fiberAngle_sine_bound hr₀ hq hr)
  have he := (uniform_error_bound measurable_radialMap continuousOn_radialMap
    (fun _ hr => hasDerivAt_radialMap hr.1 hr.2) hm hr₀ (hs.1.trans_lt hs.2)).2
  have he' := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hmax : Real.pi*errorEnvelope m ≤ planarError m := le_max_right _ _
  linarith

end SymmetricMahler

end OAI
