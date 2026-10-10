import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyComponents
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # Exact free energy rates on the completed space

The low and high squared Sobolev norms acquire the factors exp(-a s)
and exp((6-2a-k)s). Density extends the identities from Schwartz data to
every element of the faithful Y space.
-/

open scoped SchwartzMap

namespace DefocusingNLS

theorem homogeneousLowEnergy_free (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousLowEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk f)‖ ^ 2 =
      Real.exp (-a * s) * ‖homogeneousLowEnergy a k ha1 hk f‖ ^ 2 := by
  have h : (fun g : HomogeneousY a k =>
      ‖homogeneousLowEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk g)‖ ^ 2) =
      (fun g => Real.exp (-a * s) * ‖homogeneousLowEnergy a k ha1 hk g‖ ^ 2) :=
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (((homogeneousLowEnergy a k ha1 hk).continuous.comp
      (homogeneousFreeOperator a b k s ha ha1 hk).continuous).norm.pow 2)
    (continuous_const.mul ((homogeneousLowEnergy a k ha1 hk).continuous.norm.pow 2)) (by
      funext ψ
      simp only [Function.comp_apply]
      rw [homogeneousFreeOperator_on_Schwartz, homogeneousLowEnergy_Schwartz_norm_sq,
        homogeneousLowEnergy_Schwartz_norm_sq, homogeneousFreeFourier_energy]
      have he : 6 - 2 * a - (6 - a) = -a := by ring
      rw [he]
      ring)
  exact congrFun h f

theorem homogeneousHighEnergy_free (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousHighEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk f)‖ ^ 2 =
      Real.exp ((6 - 2 * a - k) * s) * ‖homogeneousHighEnergy a k ha1 hk f‖ ^ 2 := by
  have h : (fun g : HomogeneousY a k =>
      ‖homogeneousHighEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk g)‖ ^ 2) =
      (fun g => Real.exp ((6 - 2 * a - k) * s) * ‖homogeneousHighEnergy a k ha1 hk g‖ ^ 2) :=
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (((homogeneousHighEnergy a k ha1 hk).continuous.comp
      (homogeneousFreeOperator a b k s ha ha1 hk).continuous).norm.pow 2)
    (continuous_const.mul ((homogeneousHighEnergy a k ha1 hk).continuous.norm.pow 2)) (by
      funext ψ
      simp only [Function.comp_apply]
      rw [homogeneousFreeOperator_on_Schwartz, homogeneousHighEnergy_Schwartz_norm_sq,
        homogeneousHighEnergy_Schwartz_norm_sq, homogeneousFreeFourier_energy]
      ring)
  exact congrFun h f

theorem homogeneousFreeEnergy_formula (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousFreeOperator a b k s ha ha1 hk f‖ ^ 2 =
      Real.exp (-a * s) * ‖homogeneousLowEnergy a k ha1 hk f‖ ^ 2 +
      Real.exp ((6 - 2 * a - k) * s) * ‖homogeneousHighEnergy a k ha1 hk f‖ ^ 2 := by
  rw [homogeneousEnergy_norm_sq a k ha1 hk, homogeneousLowEnergy_free,
    homogeneousHighEnergy_free]

theorem hasDerivAt_homogeneousFreeEnergy_zero (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    HasDerivAt (fun s => ‖homogeneousFreeOperator a b k s ha ha1 hk f‖ ^ 2)
      (-a * ‖homogeneousLowEnergy a k ha1 hk f‖ ^ 2 +
        (6 - 2 * a - k) * ‖homogeneousHighEnergy a k ha1 hk f‖ ^ 2) 0 := by
  have hlow := (((hasDerivAt_id (0 : ℝ)).const_mul (-a)).exp).mul_const
    (‖homogeneousLowEnergy a k ha1 hk f‖ ^ 2)
  have hhigh := (((hasDerivAt_id (0 : ℝ)).const_mul (6 - 2 * a - k)).exp).mul_const
    (‖homogeneousHighEnergy a k ha1 hk f‖ ^ 2)
  have he : (fun s => ‖homogeneousFreeOperator a b k s ha ha1 hk f‖ ^ 2) =
      (fun s => Real.exp (-a * s) * ‖homogeneousLowEnergy a k ha1 hk f‖ ^ 2 +
        Real.exp ((6 - 2 * a - k) * s) * ‖homogeneousHighEnergy a k ha1 hk f‖ ^ 2) :=
    funext (fun s => homogeneousFreeEnergy_formula a b k s ha ha1 hk f)
  rw [he]
  simpa only [id_eq, mul_zero, Real.exp_zero, one_mul, mul_one, Pi.add_apply] using!
    hlow.add hhigh

theorem homogeneousLowEnergy_free_inner (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f g : HomogeneousY a k) :
    inner ℝ (homogeneousLowEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk f))
      (homogeneousLowEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk g)) =
      Real.exp (-a * s) * inner ℝ (homogeneousLowEnergy a k ha1 hk f)
        (homogeneousLowEnergy a k ha1 hk g) := by
  have h := homogeneousLowEnergy_free a b k s ha ha1 hk (f + g)
  simp only [map_add] at h
  rw [norm_add_sq_real, norm_add_sq_real,
    homogeneousLowEnergy_free a b k s ha ha1 hk f,
    homogeneousLowEnergy_free a b k s ha ha1 hk g] at h
  nlinarith [h]

theorem homogeneousHighEnergy_free_inner (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f g : HomogeneousY a k) :
    inner ℝ (homogeneousHighEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk f))
      (homogeneousHighEnergy a k ha1 hk (homogeneousFreeOperator a b k s ha ha1 hk g)) =
      Real.exp ((6 - 2 * a - k) * s) * inner ℝ (homogeneousHighEnergy a k ha1 hk f)
        (homogeneousHighEnergy a k ha1 hk g) := by
  have h := homogeneousHighEnergy_free a b k s ha ha1 hk (f + g)
  simp only [map_add] at h
  rw [norm_add_sq_real, norm_add_sq_real,
    homogeneousHighEnergy_free a b k s ha ha1 hk f,
    homogeneousHighEnergy_free a b k s ha ha1 hk g] at h
  nlinarith [h]

theorem homogeneousEnergy_inner (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f g : HomogeneousY a k) :
    inner ℝ f g = inner ℝ (homogeneousLowEnergy a k ha1 hk f)
      (homogeneousLowEnergy a k ha1 hk g) +
        inner ℝ (homogeneousHighEnergy a k ha1 hk f) (homogeneousHighEnergy a k ha1 hk g) := by
  have h := homogeneousEnergy_norm_sq a k ha1 hk (f + g)
  simp only [map_add] at h
  rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real,
    homogeneousEnergy_norm_sq a k ha1 hk f, homogeneousEnergy_norm_sq a k ha1 hk g] at h
  linarith

end DefocusingNLS

end OAI
