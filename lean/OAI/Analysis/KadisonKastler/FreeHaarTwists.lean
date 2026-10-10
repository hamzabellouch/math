import OAI.Analysis.KadisonKastler.FreeHaarTwist

namespace OAI

/-! # Adjoint and left twists of the constructed free Haar unitary -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- Taking the adjoint negates every Haar exponent. -/
theorem haarPower_star (u : unitary B) (k : ℤ) :
    haarPower (star u) k = haarPower u (-k) := by
  simp only [haarPower, Unitary.star_eq_inv, inv_zpow, zpow_neg]

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {s : unitary B}

theorem star (h : FreeHaarMoments τ A s) : FreeHaarMoments τ A (star s) where
  haar_moment k hk := by
    rw [haarPower_star]
    exact h.haar_moment (-k) (neg_ne_zero.mpr hk)
  alternating_moment n hn a k ha hz hk := by
    simp_rw [haarPower_star]
    exact h.alternating_moment n hn a (fun i => -k i) ha hz
      (fun i hi => neg_ne_zero.mpr (hk i hi))

/-- Multiplication on the left by a unitary in the base preserves the
same free Haar moment identities. -/
theorem mul_left (h : FreeHaarMoments τ A s) (U : unitary B) (hU : (U : B) ∈ A) :
    FreeHaarMoments τ A (U * s) := by
  have ht := (h.star.mul_right (Star.star U) (star_mem hU)).star
  simpa only [star_mul, star_star] using ht

end FreeHaarMoments

end

end KadisonKastler

end OAI
