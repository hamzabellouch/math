import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousProductCompact
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization

namespace OAI

/-! # Compact low-order part of the actual linearized potential

The two coefficients of the odd-power derivative are actual vectors in Y.
Their physical formulas identify the algebraic decomposition, so the
low-order compactness theorem applies directly to the Schrödinger potential.
-/

open Filter Topology
open scoped ComplexConjugate ZeroAtInfty

namespace DefocusingNLS

noncomputable def homogeneousLinearizedFirstCoefficient (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k) :
    HomogeneousY a k :=
  (-Complex.I * ((m + 2 : ℕ) : ℂ)) •
    homogeneousYProduct a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m q)
      (homogeneousConjugation a k ha ha1 hk q)

noncomputable def homogeneousLinearizedSecondCoefficient (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k) :
    HomogeneousY a k :=
  (-Complex.I * ((m + 1 : ℕ) : ℂ)) •
    homogeneousYProduct a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m q) q

theorem homogeneousLinearizedPotential_decomposition (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q v : HomogeneousY a k) :
    homogeneousLinearizedPotential a k ha ha1 hk (m + 1) q v =
      homogeneousYProduct a k ha ha1 hk
        (homogeneousLinearizedFirstCoefficient a k ha ha1 hk m q) v +
      homogeneousYProduct a k ha ha1 hk
        (homogeneousLinearizedSecondCoefficient a k ha ha1 hk m q)
        (homogeneousConjugation a k ha ha1 hk v) := by
  apply homogeneousPhysicalCLM_injective a k ha ha1 hk
  apply DFunLike.ext
  intro x
  rw [homogeneousLinearizedPotential_physical, map_add, ZeroAtInftyContinuousMap.add_apply]
  simp only [homogeneousYProduct_physical, homogeneousLinearizedFirstCoefficient,
    homogeneousLinearizedSecondCoefficient, map_smul, ZeroAtInftyContinuousMap.smul_apply,
    homogeneousConjugation_physical, homogeneousOddPower_physical, smul_eq_mul,
    oddPowerDerivative, oddPowerNonlinearity, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    starL'_apply, starRingEnd_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem tendsto_homogeneousLowEnergy_linearizedPotential (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousLowEnergy a k ha1 hk
      (homogeneousLinearizedPotential a k ha ha1 hk (m + 1) q (u n))) atTop (𝓝 0) := by
  have hfirst := tendsto_homogeneousLowEnergy_product a k M ha ha1 hk
    (homogeneousLinearizedFirstCoefficient a k ha ha1 hk m q) u hu hweak
  have hconj (ℓ : HomogeneousY a k →L[ℝ] ℂ) :
      Tendsto (fun n => ℓ (homogeneousConjugation a k ha ha1 hk (u n))) atTop (𝓝 0) :=
    hweak (ℓ.comp (homogeneousConjugation a k ha ha1 hk))
  have hsecond := tendsto_homogeneousLowEnergy_product a k M ha ha1 hk
    (homogeneousLinearizedSecondCoefficient a k ha ha1 hk m q)
    (fun n => homogeneousConjugation a k ha ha1 hk (u n))
    (fun n => by simpa only [homogeneousConjugation_norm] using hu n) hconj
  simpa only [homogeneousLinearizedPotential_decomposition, map_add, add_zero] using
    hfirst.add hsecond

end DefocusingNLS

end OAI
