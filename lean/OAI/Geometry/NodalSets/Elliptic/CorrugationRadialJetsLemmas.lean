import OAI.Geometry.NodalSets.Elliptic.CorrugationDiskJets

namespace OAI

noncomputable section

namespace Yau.Geometry

open Real

def radialComponent (z v : ℝ × ℝ) (r : ℝ) : ℝ := (z.1*v.1+z.2*v.2)/r

def angularComponent (z v : ℝ × ℝ) (r : ℝ) : ℝ := (-z.2*v.1+z.1*v.2)/r

lemma radial_angular_decomposition (z u v : ℝ × ℝ) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) :
    u.1*v.1+u.2*v.2 =
      radialComponent z u r*radialComponent z v r +
      angularComponent z u r*angularComponent z v r := by
  unfold radialComponent angularComponent
  field_simp
  nlinarith only [congrArg (fun t : ℝ ↦ t*(u.1*v.1+u.2*v.2)) hz]

lemma corrugationDiskWell_radial_first (a R : ℝ) (z v : ℝ × ℝ) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) :
    fderiv ℝ (corrugationDiskWell a R) z v =
      corrugationSlope a R r*radialComponent z v r := by
  rw [corrugationDiskWell_fderiv]
  have ht : R^2-z.1^2-z.2^2 = R^2-r^2 := by linarith
  rw [ht]
  unfold corrugationSlope radialComponent
  field_simp

lemma corrugationDiskWell_radial_second (a R : ℝ) (z u v : ℝ × ℝ) {r : ℝ}
    (hr : r ≠ 0) (hz : r^2=z.1^2+z.2^2) :
    fderiv ℝ (fderiv ℝ (corrugationDiskWell a R)) z u v =
      deriv (corrugationSlope a R) r*radialComponent z u r*radialComponent z v r +
      (corrugationSlope a R r/r)*angularComponent z u r*angularComponent z v r := by
  rw [corrugationDiskWell_second,corrugationSlope_deriv]
  have ht : R^2-z.1^2-z.2^2 = R^2-r^2 := by linarith
  rw [ht,radial_angular_decomposition z u v hr hz]
  have hu : z.1*u.1+z.2*u.2 = r*radialComponent z u r := by
    unfold radialComponent; field_simp
  have hv : z.1*v.1+z.2*v.2 = r*radialComponent z v r := by
    unfold radialComponent; field_simp
  rw [hu,hv]
  unfold corrugationSlope
  field_simp
  ring

open Real Set
open scoped ContDiff

theorem exists_fixed_corrugation_well : ∃ (a C l₀ : ℝ) (f : ℝ × ℝ → ℝ),
    0 < a ∧ a ≤ 1 ∧ 0 < C ∧ 0 < l₀ ∧
    f = corrugationPeriodicWell a ∧ ContDiff ℝ ∞ f ∧
    (∀ (m : ℤ × ℤ) (z : ℝ × ℝ), f (z.1+(m.1:ℝ),z.2+(m.2:ℝ)) = f z) ∧
    (∀ z : ℝ × ℝ, |z.1| ≤ 1/2 → |z.2| ≤ 1/2 →
      f z = -(∫ t in Real.sqrt (z.1^2+z.2^2)..(1/4), corrugationSlope a (1/4) t)) ∧
    (∀ r : ℝ, 0 ≤ r → 0 ≤ corrugationSlope a (1/4) r ∧ corrugationSlope a (1/4) r ≤ 1 ∧
      max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ C*(corrugationSlope a (1/4) r)^((7:ℝ)/8) ∧
      corrugationSlope a (1/4) r * max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ 1/(64*(1/4:ℝ))) ∧
    (∀ r ∈ Icc (1/16:ℝ) (1/8), l₀ ≤ corrugationSlope a (1/4) r) ∧
    (∀ z : ℝ × ℝ, |z.1| ≤ 1/2 → |z.2| ≤ 1/2 →
      (1/4:ℝ)^2 ≤ z.1^2+z.2^2 → f z = 0) := by
  obtain ⟨a,C,l₀,ha,ha1,hC,hl₀,_,hb,hann,_⟩ := exists_fixed_corrugation_slope
  refine ⟨a,C,l₀,corrugationPeriodicWell a,ha,ha1,hC,hl₀,rfl,
    corrugationPeriodicWell_smooth a,corrugationPeriodicWell_periodic a,?_,hb,hann,?_⟩
  · intro z hz1 hz2
    rw [corrugationPeriodicWell_cell a z hz1 hz2,corrugationDiskWell_radial,
      corrugationRadialPotential_integral]
  · intro z hz1 hz2 hz
    exact corrugationPeriodicWell_plateau a z hz1 hz2 hz

end Yau.Geometry

end

end OAI
