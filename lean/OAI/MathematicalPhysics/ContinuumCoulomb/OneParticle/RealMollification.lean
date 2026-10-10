import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SobolevDensityInput
import OAI.Analysis.CoulombRadii.FormDomain.HardyMollifier

namespace OAI

/-! Smooth approximation of real L² functions on the actual configuration
space. Fatou and the contraction estimate suffice; no Sobolev density input
is used. This is the scalar approximation needed for the H=W discharge. -/

noncomputable section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution
namespace ContinuumCoulomb

private theorem l2_error_eventually_lt {n : ℕ}
    (u : Configuration n → ℝ) (v : ℕ → Configuration n → ℝ)
    (hu : MemLp u 2) (hv : ∀ k, MemLp (v k) 2)
    (ht : ∀ᵐ x, Tendsto (fun k => v k x) atTop (𝓝 (u x)))
    (hb : ∀ k, (∫ x, v k x ^ 2) ≤ ∫ x, u x ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∫ x, (v k x-u x)^2) < ε := by
  by_contra h
  have hfreq : ∃ᶠ k in atTop, ε ≤ ∫ x, (v k x-u x)^2 := by
    simpa only [Filter.Frequently,not_le,not_not] using h
  obtain ⟨ns,hns,hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hsum (k : ℕ) :
      (∫ x, (v k x+u x)^2)+(∫ x, (v k x-u x)^2) =
        2*(∫ x, v k x^2)+2*(∫ x, u x^2) := by
    calc
      _ = ∫ x, (v k x+u x)^2+(v k x-u x)^2 :=
        (integral_add ((hv k).add hu).integrable_sq ((hv k).sub hu).integrable_sq).symm
      _ = ∫ x, 2*v k x^2+2*u x^2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => by ring)
      _ = _ := by
        rw [integral_add ((hv k).integrable_sq.const_mul 2) (hu.integrable_sq.const_mul 2),
          integral_const_mul,integral_const_mul]
  have hlim : ∀ᵐ x, Tendsto (fun k => (v (ns k) x+u x)^2)
      atTop (𝓝 (4*u x^2)) := by
    filter_upwards [ht] with x hx
    have he : (u x+u x)^2 = 4*u x^2 := by ring
    simpa only [Function.comp_apply,he] using ((hx.comp hns).add_const (u x)).pow 2
  have hbound (k : ℕ) : (∫ x, (v (ns k) x+u x)^2) ≤
      4*(∫ x, u x^2)-ε := by
    have hs := hsum (ns k)
    have hb' := hb (ns k)
    have he := hbad k
    linarith
  have hf := Coulomb.ae_nonneg_fatou_integrable volume (fun x => 4*u x^2)
    (fun k x => (v (ns k) x+u x)^2) (4*(∫ x, u x^2)-ε)
    (fun k => ((hv (ns k)).add hu).integrable_sq)
    (fun k x => sq_nonneg (v (ns k) x+u x))
    (fun x => mul_nonneg (by norm_num) (sq_nonneg (u x)))
    hlim hbound
  rw [integral_const_mul] at hf
  linarith [hf.2]

def realMollification {n : ℕ} (u : Configuration n → ℝ) (k : ℕ) :
    Configuration n → ℝ := (Coulomb.hardyMollifier k).normed volume ⋆ u

theorem realMollification_smooth {n : ℕ} {u : Configuration n → ℝ}
    (hu : MemLp u 2) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (realMollification u k) :=
  (Coulomb.hardyMollifier k).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (Coulomb.hardyMollifier k).contDiff_normed
    (hu.locallyIntegrable (by norm_num))

theorem realMollification_contraction {n : ℕ} {u : Configuration n → ℝ}
    (hu : MemLp u 2) (k : ℕ) :
    MemLp (realMollification u k) 2 ∧
      (∫ x, realMollification u k x ^ 2) ≤ ∫ x, u x ^ 2 := by
  have h := Coulomb.convolution_sq_integral_le
    ((Coulomb.hardyMollifier k).normed volume) u
    ((Coulomb.hardyMollifier k).contDiff_normed (n := (⊤ : ℕ∞))).continuous
    (Coulomb.hardyMollifier k).hasCompactSupport_normed
    (Coulomb.hardyMollifier k).nonneg_normed
    (Coulomb.hardyMollifier k).integral_normed
    (hu.locallyIntegrable (by norm_num)) hu.integrable_sq
  exact ⟨(memLp_two_iff_integrable_sq
    (realMollification_smooth hu k).continuous.aestronglyMeasurable).mpr h.1,h.2⟩

theorem realMollification_error {n : ℕ} {u : Configuration n → ℝ}
    (hu : MemLp u 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (∫ x, (realMollification u k x-u x)^2) < ε := by
  apply l2_error_eventually_lt u (realMollification u) hu
    (fun k => (realMollification_contraction hu k).1) ?_
    (fun k => (realMollification_contraction hu k).2) hε
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun k => Coulomb.hardyMollifier k) (K := 2)
    Coulomb.hardyMollifier_tendsto _ (hu.locallyIntegrable (by norm_num))
  apply Eventually.of_forall
  intro k
  simp only [Coulomb.hardyMollifier]
  simp only [mul_one_div,le_refl]

end ContinuumCoulomb

end

end OAI
