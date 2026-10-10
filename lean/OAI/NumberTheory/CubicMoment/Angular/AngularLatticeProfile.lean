import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.SchwartzLattice
import OAI.NumberTheory.CubicGram.GramPoisson

namespace OAI

/-! The actual angular annulus is a smooth compactly supported plane
function. Its area integral is zero in every nonzero integral mode. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff SchwartzMap Topology
namespace CubicFirstMoment

def angularPlanePhase (ℓ : ℤ) (z : ℂ) : ℂ := (z/(‖z‖:ℂ))^ℓ

def angularAnnulus (ℓ : ℤ) (W : ℝ → ℂ) (z : ℂ) : ℂ :=
  angularPlanePhase ℓ z*W (Complex.normSq z)

lemma angularPlanePhase_mul (ℓ : ℤ) (z w : ℂ) :
    angularPlanePhase ℓ (z*w) = angularPlanePhase ℓ z*angularPlanePhase ℓ w := by
  simp only [angularPlanePhase,norm_mul,Complex.ofReal_mul]
  rw [mul_div_mul_comm,mul_zpow]

lemma angularPlanePhase_coe (ℓ : ℤ) (a : Eisenstein) :
    angularPlanePhase ℓ (a:ℂ) = theta ℓ a := rfl

lemma angularPlanePhase_contDiffAt (ℓ : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (angularPlanePhase ℓ) z := by
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hc : ContDiffAt ℝ ∞ (fun w : ℂ => (‖w‖:ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℂ hz)
  have hq : ContDiffAt ℝ ∞ (fun w : ℂ => w/(‖w‖:ℂ)) z := by
    simpa only [div_eq_mul_inv] using! (contDiffAt_id (x := z)).mul (hc.inv hn)
  cases ℓ with
  | ofNat n => simpa only [angularPlanePhase,zpow_natCast] using! hq.pow n
  | negSucc n =>
      have hp := (hq.pow (n+1)).inv (pow_ne_zero _ (div_ne_zero hz hn))
      simpa only [angularPlanePhase,zpow_negSucc] using! hp

lemma angularAnnulus_compact (ℓ : ℤ) {W : ℝ → ℂ} (hW : HasCompactSupport W) :
    HasCompactSupport (angularAnnulus ℓ W) := by
  have hn := hasCompactSupport_normProfile hW (show (0:ℝ) < 1 by norm_num)
  simp only [div_one] at hn
  exact hn.mul_left

lemma angularAnnulus_smooth (ℓ : ℤ) {W : ℝ → ℂ}
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (angularAnnulus ℓ W) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have hzero : (0:ℝ) ∉ tsupport W := fun hh => (lt_irrefl (0:ℝ)) (hpos hh)
    have ht : Tendsto (fun z : ℂ => Complex.normSq z) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using Complex.continuous_normSq.tendsto (0:ℂ)
    have he := (notMem_tsupport_iff_eventuallyEq.mp hzero).comp_tendsto ht
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with w hw
    change W (Complex.normSq w) = 0 at hw
    simp only [angularAnnulus,hw,mul_zero]
  · have hw : ContDiff ℝ ∞ (fun w : ℂ => W (Complex.normSq w)) := by
      simpa only [div_one] using contDiff_normProfile hsm 1
    exact (angularPlanePhase_contDiffAt ℓ hz).mul hw.contDiffAt

def angularAnnulusSchwartz (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) : 𝓢(ℂ,ℂ) :=
  (angularAnnulus_compact ℓ hW).toSchwartzMap (angularAnnulus_smooth ℓ hpos hsm)

lemma angularAnnulus_rotation (ℓ : ℤ) (W : ℝ → ℂ) {q : ℂ} (hq : ‖q‖ = 1) (z : ℂ) :
    angularAnnulus ℓ W (q*z) = angularPlanePhase ℓ q*angularAnnulus ℓ W z := by
  have hn : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq,hq]; norm_num
  simp only [angularAnnulus,angularPlanePhase_mul,Complex.normSq_mul,hn,one_mul]
  ring

lemma exists_angular_sign_rotation {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ∃ q : ℂ, ‖q‖ = 1 ∧ angularPlanePhase ℓ q = -1 := by
  let q : ℂ := Complex.exp (((Real.pi/(ℓ:ℝ):ℝ):ℂ)*Complex.I)
  have hq : ‖q‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  refine ⟨q,hq,?_⟩
  rw [angularPlanePhase,hq,Complex.ofReal_one,div_one]
  dsimp [q]
  rw [←Complex.exp_int_mul]
  convert Complex.exp_pi_mul_I using 1
  have hc : (ℓ:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hℓ
  push_cast
  field_simp

/-- Continuous rotational symmetry kills the area term; the discrete
primary-lattice sum itself need not vanish. -/
theorem integral_angularAnnulus_eq_zero {ℓ : ℤ} (hℓ : ℓ ≠ 0) (W : ℝ → ℂ) :
    (∫ z : ℂ, angularAnnulus ℓ W z) = 0 := by
  obtain ⟨q,hq,hphase⟩ := exists_angular_sign_rotation hℓ
  have hq0 : q ≠ 0 := by intro hh; simp [hh] at hq
  have hN : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq,hq]; norm_num
  have hi := integral_complexMul q hq0 (angularAnnulus ℓ W)
  simp_rw [angularAnnulus_rotation ℓ W hq,hphase,neg_one_mul] at hi
  rw [integral_neg,hN,inv_one,one_smul] at hi
  have he : (2:ℂ)*(∫ z : ℂ, angularAnnulus ℓ W z) = 0 := by linear_combination -hi
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end CubicFirstMoment

end

end OAI
