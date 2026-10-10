import OAI.Probability.ContinuumTransition.TransformAttainment

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma isLUB_div_image {f : ℝ → ℝ} {S : Set ℝ} {c z : ℝ}
    (hc : 0 < c) (hz : IsLUB (f '' S) z) :
    IsLUB ((fun d => f d/c) '' S) (z/c) := by
  have hh := hz.mul_right (inv_pos.mpr hc).le
  simpa only [image_image,Function.comp_def,← div_eq_mul_inv] using hh

lemma physicalPressure_isLUB {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B h : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsLUB ((fun d => h*d-physicalCanonical φ t β d) '' Ici 0)
      (physicalPressure φ t (β,h)) := by
  have hh : IsLUB ((fun d => (t*h)*d-canonicalDensity φ β d) '' Ici 0)
      (canonicalPressure φ β (t*h)) :=
    isLUB_csSup (Set.Nonempty.image _ nonempty_Ici)
      (canonicalPressure_bddAbove hφ ht hβ hstable hcore)
  have hh' := isLUB_div_image (lt_trans zero_lt_one ht) hh
  convert hh' using 2
  dsimp [physicalCanonical]
  field_simp
  rfl

lemma physical_meanField {t a : ℝ} (ht : 1 < t) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (hgap : t*a/2 ≤ (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) :
    IsMeanField (physicalPressure (physicalProfile t σ R) t) a
      (fun x => quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)/t) := by
  intro x hx
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hb : x.1*(t*a)/2 ≤ x.1*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) := by
    have := mul_le_mul_of_nonneg_left hgap (le_of_lt hx)
    nlinarith only [this]
  have hp : IsLUB ((fun d => (t*x.2)*d+(x.1*(t*a)/2)*d^2-
      canonicalDensity (physicalProfile t σ R) x.1 d) '' Ici 0)
      (quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)) :=
    isLUB_csSup (Set.Nonempty.image _ nonempty_Ici)
      (quadraticPressure_bddAbove ht (le_of_lt hx) hσ hR hs hsmall hb)
  have hpn := isLUB_div_image ht0 hp
  have hpn' : IsLUB ((fun d => x.2*d+x.1*a*d^2/2-
      physicalCanonical (physicalProfile t σ R) t x.1 d) '' Ici 0)
      (quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)/t) := by
    convert hpn using 2
    dsimp [physicalCanonical]
    field_simp
  exact convolution_isLUB (mul_nonneg (le_of_lt hx) ha)
    (fun h => physicalPressure_isLUB hφ ht (le_of_lt hx) hst hcore (h := h)) hpn'

end ContinuumTemperature
end
end

end OAI
