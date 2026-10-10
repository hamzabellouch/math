import OAI.Probability.SLE.Geometry.ReflectedInvertedUpperConnected
import OAI.Probability.SLE.Geometry.ExteriorJoukowski

namespace OAI

/-! Conjugate inversion identifies the upper half of the punctured disk
with the upper exterior disk. -/
noncomputable section
open Set Complex Function Metric
open scoped ComplexConjugate

namespace SLEExactGauge

@[simp] lemma norm_conjugateInversion (z : ℂ) : ‖conjugateInversion z‖=‖z‖⁻¹ := by
  simp only [conjugateInversion,norm_inv,norm_conj]

lemma conjugateInversion_injective : Injective conjugateInversion :=
  Function.LeftInverse.injective conjugateInversion_involutive

lemma conjugateInversion_disk_upper_bijOn :
    BijOn conjugateInversion (ball (0:ℂ) 1 ∩ upperHalfPlane) exteriorUpperDisk := by
  have hn : ∀ z ∈ upperHalfPlane, 0 < ‖z‖ := by
    intro z hz
    apply norm_pos_iff.mpr
    intro he
    simp only [upperHalfPlane,mem_ofPred_eq,he,zero_im,lt_self_iff_false] at hz
  refine ⟨?_,conjugateInversion_injective.injOn,?_⟩
  · intro z hz
    refine ⟨?_,conjugateInversion_upper hz.2⟩
    rw [norm_conjugateInversion,inv_eq_one_div,lt_div_iff₀ (hn z hz.2)]
    simpa only [one_mul,mem_ball,dist_zero_right] using hz.1
  · intro z hz
    refine ⟨conjugateInversion z,⟨?_,conjugateInversion_upper hz.2⟩,
      conjugateInversion_involutive z⟩
    rw [mem_ball,dist_zero_right,norm_conjugateInversion,inv_eq_one_div,
      div_lt_iff₀ (hn z hz.2)]
    simpa only [one_mul] using hz.1

lemma conjugateInversion_slit_bijOn
    (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    BijOn conjugateInversion (upperHalfPlane \ range p)
      (invertedExterior (reflectedArcSet p) ∩ upperHalfPlane) := by
  rw [reflected_inverted_upper_image p h0 hH]
  exact conjugateInversion_injective.injOn.bijOn_image

end SLEExactGauge

end

end OAI
