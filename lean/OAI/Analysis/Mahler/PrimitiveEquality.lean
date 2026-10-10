import OAI.Analysis.Mahler.PlanarDensity
import OAI.Analysis.Mahler.GlobalFiberParametrization

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- Along the actual fiber, the original vertical primitive has exactly the
radial density as derivative. This proves the substitution locally without
assuming a change-of-variables identity. -/
theorem hasDerivAt_planarPrimitive_fiber {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1)
    (hseg : ∀ t ∈ uIcc (0 : ℝ) (fiberHeight q r),
      (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    HasDerivAt (fun s => planarPrimitive m q (fiberHeight q s))
      (radialPrimitiveDensity (fiberAngle q) (m : ℝ) r) r := by
  have hmem := mem_fiberDomain_of_basepoint hr₀ hq hr
  have hH : HasDerivAt (fiberHeight q) (deriv (fiberHeight q) r) r :=
    (hasDerivAt_fiberHeight hmem).differentiableAt.hasDerivAt
  have hG := (hasDerivAt_planarPrimitive m hseg).comp r hH
  have hA := (hasDerivAt_actual_primitive_density hm hr₀ hq hr).comp r hH
  have hR : HasDerivAt (radialPrimitive q r₀ (m : ℝ))
      (planarDensity m ((q : ℂ)+(fiberHeight q r : ℂ)*Complex.I)*deriv (fiberHeight q) r) r := by
    apply hA.congr_of_eventuallyEq
    filter_upwards [(fiberDomain_isOpen q).mem_nhds hmem] with s hs
    simp only [Function.comp_def, verticalRadius_fiber hs]
  have heq := hR.unique (hasDerivAt_radialPrimitive (m := (m : ℝ)) (by exact_mod_cast hm) hr₀ hq hr)
  rw [heq] at hG
  exact hG

/-- Global radial substitution follows once the fiber's endpoint continuity
and vertical-segment geometry have been established. -/
theorem planarPrimitive_eq_radial_of_geometry {q r₀ r : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1)
    (hheight : ContinuousOn (fiberHeight q) (Icc r₀ r))
    (hseg : ∀ s ∈ Icc r₀ r, ∀ t ∈ uIcc (0 : ℝ) (fiberHeight q s),
      (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    planarPrimitive m q (fiberHeight q r) = radialPrimitive q r₀ (m : ℝ) r := by
  let G : ℝ → ℝ := fun s => planarPrimitive m q (fiberHeight q s) - radialPrimitive q r₀ (m : ℝ) s
  have hi := radial_primitive_integrable (m := (m : ℝ)) (measurable_fiberAngle q) (by exact_mod_cast hm)
    hr₀ hr.1.le hr.2 (fun s hs => fiberAngle_sine_bound hr₀ hq hs)
  have hRcont : ContinuousOn (radialPrimitive q r₀ (m : ℝ)) (Icc r₀ r) := by
    simpa only [radialPrimitive, uIcc_of_le hr.1.le] using!
      intervalIntegral.continuousOn_primitive_interval' hi (show r₀ ∈ uIcc r₀ r from left_mem_uIcc)
  have hGcont : ContinuousOn G (Icc r₀ r) := by
    apply ContinuousOn.sub _ hRcont
    intro s hs
    exact (hasDerivAt_planarPrimitive m (hseg s hs)).continuousAt.comp_continuousWithinAt (hheight s hs)
  have hGder : ∀ s ∈ Ioo r₀ r, HasDerivAt G 0 s := by
    intro s hs
    have hs1 : s ∈ Ioo r₀ 1 := ⟨hs.1,hs.2.trans hr.2⟩
    have hleft := hasDerivAt_planarPrimitive_fiber hm hr₀ hq hs1 (hseg s ⟨hs.1.le,hs.2.le⟩)
    have hright := hasDerivAt_radialPrimitive (m := (m : ℝ)) (by exact_mod_cast hm) hr₀ hq hs1
    simpa only [G, Pi.sub_apply, sub_self] using! hleft.sub hright
  obtain ⟨s,hs,heq⟩ := exists_hasDerivAt_eq_slope G (fun _ => 0) hr.1 hGcont hGder
  have hzero : G r₀ = 0 := by simp [G, fiberHeight_basepoint hq, planarPrimitive_zero, radialPrimitive]
  rw [hzero, sub_zero] at heq
  have hGr : G r = 0 := by
    have h := (eq_div_iff (sub_pos.mpr hr.1).ne').mp heq
    simpa using h.symm
  exact sub_eq_zero.mp hGr

end SymmetricMahler

end OAI
