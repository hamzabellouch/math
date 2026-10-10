import OAI.NumberTheory.JointDickman.Amplification.SmallMajorArcRescaling

namespace OAI

/-! # The real-valued arc partition for controlling integrated errors -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

theorem smallMajorArc_finite_sum_real :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ U : ℝ → ℝ, Continuous U → Periodic U 1 →
      (∫ x in smallMajorArcRegion B j X Q, U x) =
        ∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
          ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
            ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
              (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), U x
          else 0 else 0 := by
  filter_upwards [smallMajorArc_finite_sum] with B hB
  intro X hX hlog j hj Q U hU hp
  let : NeZero j := hj
  have hh := hB X hX hlog j hj Q (fun x => (U x : ℂ))
    (Complex.continuous_ofReal.comp hU) (fun x => by simp only [hp x])
  apply Complex.ofReal_injective
  simpa only [integral_complex_ofReal,intervalIntegral.integral_ofReal,
    Complex.ofReal_sum,apply_ite,Complex.ofReal_zero] using hh

end JointDickman

end OAI
