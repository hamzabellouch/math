import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHigherMoments

namespace OAI

/-! Translated fourth/eighth moments and the weighted tails used in the
finite-slab operator estimate. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedDensityMoment (freq : ℝ) (u : PlanarPosition) (k : ℕ) : ℝ :=
  ∫ x : Position, ‖x‖^k*localizedDensity freq u x

theorem localizedDensityMoment_nonnegative (freq : ℝ) (u : PlanarPosition) (k : ℕ) :
    0 ≤ localizedDensityMoment freq u k :=
  integral_nonneg (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) k)
    (localizedDensity_nonnegative freq u x))

private theorem translated_moment {freq : ℝ} (hfreq : 0 < freq) (k : ℕ)
    (hk : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq 0 x))
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) ∧
      localizedDensityMoment freq u k ≤
        (2:ℝ)^(k-1)*(localizedDensityMoment freq 0 k+‖u‖^k) := by
  let c := planarCenter u
  let F (x : Position) := ‖x‖^k*localizedDensity freq 0 x+
    ‖c‖^k*localizedDensity freq 0 x
  have hF : Integrable F := hk.add ((localizedDensity_integrable hfreq 0).const_mul _)
  have hmajor : Integrable (fun x => (2:ℝ)^(k-1)*F (x-c)) :=
    (hF.comp_sub_right c).const_mul _
  have hp (x : Position) : ‖x‖^k*localizedDensity freq u x ≤ (2:ℝ)^(k-1)*F (x-c) := by
    have hn : ‖x‖ ≤ ‖x-c‖+‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x-c) c
    have hb := (pow_le_pow_left₀ (norm_nonneg x) hn k).trans
      (add_pow_le (norm_nonneg (x-c)) (norm_nonneg c) k)
    have hm := mul_le_mul_of_nonneg_right hb (localizedDensity_nonnegative freq 0 (x-c))
    rw [localizedDensity_translate]
    convert hm using 1
    dsimp [F, c]
    ring
  have hi : Integrable (fun x : Position => ‖x‖^k*localizedDensity freq u x) := by
    apply hmajor.mono' ((continuous_norm.pow k).mul (localizedDensity_continuous freq u)).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖x‖^k*localizedDensity freq u x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) k)
      (localizedDensity_nonnegative freq u x))]
    exact hp x
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hmajor hp
  change localizedDensityMoment freq u k ≤ _ at h
  rw [integral_const_mul, integral_sub_right_eq_self] at h
  dsimp [F] at h
  rw [integral_add hk ((localizedDensity_integrable hfreq 0).const_mul _),
    integral_const_mul, localizedDensity_mass hfreq 0, mul_one] at h
  simpa only [c, planarCenter_norm, localizedDensityMoment] using h

theorem localizedDensity_fourth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^4*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 4 ≤ 8*(localizedDensityMoment freq 0 4+‖u‖^4) := by
  convert translated_moment hfreq 4 (localizedDensity_fourth_moment_integrable hfreq) u using 1
  norm_num

theorem localizedDensity_eighth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^8*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 8 ≤ 128*(localizedDensityMoment freq 0 8+‖u‖^8) := by
  convert translated_moment hfreq 8 (localizedDensity_eighth_moment_integrable hfreq) u using 1
  norm_num

theorem localizedDensity_twentyFourth_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^24*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 24 ≤ 8388608*(localizedDensityMoment freq 0 24+‖u‖^24) := by
  convert translated_moment hfreq 24 (localizedDensity_twentyFourth_moment_integrable hfreq) u using 1
  norm_num

theorem localizedDensity_seventySecond_moment_translate {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) :
    Integrable (fun x : Position => ‖x‖^72*localizedDensity freq u x) ∧
      localizedDensityMoment freq u 72 ≤
        (2:ℝ)^71*(localizedDensityMoment freq 0 72+‖u‖^72) :=
  translated_moment hfreq 72 (localizedDensity_seventySecond_moment_integrable hfreq) u

private theorem weighted_tail {freq R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    (a b : ℕ) (ha : Integrable (fun x : Position => ‖x‖^a*localizedDensity freq u x))
    (hab : Integrable (fun x : Position => ‖x‖^(a+b)*localizedDensity freq u x))
    {S : Set Position} (hS : MeasurableSet S) (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^a*localizedDensity freq u x) ≤
      localizedDensityMoment freq u (a+b)/R^b := by
  have hp (x : Position) (hx : x ∈ Sᶜ) :
      R^b*(‖x‖^a*localizedDensity freq u x) ≤ ‖x‖^(a+b)*localizedDensity freq u x := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hR.le (hout x hx) b)
      (mul_nonneg (pow_nonneg (norm_nonneg x) a) (localizedDensity_nonnegative freq u x))
    simpa only [pow_add, mul_left_comm, mul_assoc] using h
  have h := setIntegral_mono_on (ha.const_mul (R^b)).integrableOn hab.integrableOn hS.compl hp
  have hfull := integral_mono_measure (μ := volume.restrict Sᶜ) Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) (a+b))
      (localizedDensity_nonnegative freq u x))) hab
  rw [integral_const_mul] at h
  apply (le_div_iff₀ (pow_pos hR b)).mpr
  simpa only [localizedDensityMoment, mul_comm] using h.trans hfull

theorem localizedDensity_mass_tail_eighth {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq u x) ≤ localizedDensityMoment freq u 8/R^8 := by
  simpa only [pow_zero, one_mul, zero_add] using weighted_tail hR u 0 8
    (by simpa only [pow_zero, one_mul] using localizedDensity_integrable hfreq u)
    (localizedDensity_eighth_moment_translate hfreq u).1 hS hout

theorem localizedDensity_fourth_tail_eighth {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 8/R^4 := by
  exact weighted_tail hR u 4 4 (localizedDensity_fourth_moment_translate hfreq u).1
    (localizedDensity_eighth_moment_translate hfreq u).1 hS hout

theorem localizedDensity_mass_tail_twentyFourth {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq u x) ≤ localizedDensityMoment freq u 24/R^24 := by
  simpa only [pow_zero, one_mul, zero_add] using weighted_tail hR u 0 24
    (by simpa only [pow_zero, one_mul] using localizedDensity_integrable hfreq u)
    (localizedDensity_twentyFourth_moment_translate hfreq u).1 hS hout

theorem localizedDensity_fourth_tail_twentyFourth {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 24/R^20 := by
  exact weighted_tail hR u 4 20 (localizedDensity_fourth_moment_translate hfreq u).1
    (localizedDensity_twentyFourth_moment_translate hfreq u).1 hS hout

theorem localizedDensity_mass_tail_seventySecond {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, localizedDensity freq u x) ≤ localizedDensityMoment freq u 72/R^72 := by
  simpa only [pow_zero,one_mul,zero_add] using weighted_tail hR u 0 72
    (by simpa only [pow_zero,one_mul] using localizedDensity_integrable hfreq u)
    (localizedDensity_seventySecond_moment_translate hfreq u).1 hS hout

theorem localizedDensity_fourth_tail_seventySecond {freq R : ℝ} (hfreq : 0 < freq) (hR : 0 < R)
    (u : PlanarPosition) {S : Set Position} (hS : MeasurableSet S)
    (hout : ∀ x ∉ S, R ≤ ‖x‖) :
    (∫ x in Sᶜ, ‖x‖^4*localizedDensity freq u x) ≤ localizedDensityMoment freq u 72/R^68 := by
  exact weighted_tail hR u 4 68 (localizedDensity_fourth_moment_translate hfreq u).1
    (localizedDensity_seventySecond_moment_translate hfreq u).1 hS hout

end ContinuumCoulomb

end

end OAI
