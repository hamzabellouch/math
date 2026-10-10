import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialEquation

namespace OAI

/-! # The actual two-channel linearized potential

Physical evaluation of the complexified real derivative gives exactly the
circular coefficient matrix used in the spectral ODE.
-/

open scoped ComplexConjugate ZeroAtInfty

namespace DefocusingNLS

private theorem circularComplexification_scalar (A B f g : ℂ) :
    let x := (1 / 2 : ℂ) * (f + conj g)
    let y := (-Complex.I / 2 : ℂ) * (f - conj g)
    let L := fun z => -Complex.I * (A * z + B * conj z)
    (L x + Complex.I * L y, conj (L x) + Complex.I * conj (L y)) =
      (-Complex.I * (A * f + B * g),
        Complex.I * (conj A * g + conj B * f)) := by
  dsimp only
  have htwo : conj (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Complex.I_sq, neg_one_mul]
  apply Prod.ext
  all_goals
    simp only [map_add, map_mul, map_div₀, map_sub, map_neg, map_one,
      htwo, Complex.conj_I, starRingEnd_self_apply]
    ring_nf
    rw [hI3]
    ring

section

variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "H" => HomogeneousY a k
local notation "P" => homogeneousPhysicalCLM a k ha ha1 hk

@[simp] theorem homogeneousComplexReal_physical (z : H × H) (x : E) :
    P (homogeneousComplexReal a k ha ha1 hk z) x =
      (1 / 2 : ℂ) * (P z.1 x + conj (P z.2 x)) := by
  simp only [homogeneousComplexReal_apply, map_smul, map_add,
    ZeroAtInftyContinuousMap.smul_apply, ZeroAtInftyContinuousMap.add_apply,
    homogeneousConjugation_physical, smul_eq_mul]

@[simp] theorem homogeneousComplexImag_physical (z : H × H) (x : E) :
    P (homogeneousComplexImag a k ha ha1 hk z) x =
      (-Complex.I / 2 : ℂ) * (P z.1 x - conj (P z.2 x)) := by
  simp only [homogeneousComplexImag_apply, map_smul, map_sub,
    ZeroAtInftyContinuousMap.smul_apply, ZeroAtInftyContinuousMap.sub_apply,
    homogeneousConjugation_physical, smul_eq_mul]

theorem homogeneousComplexifiedPotential_physical (m : ℕ) (q : H) (z : H × H) (x : E) :
    let L := homogeneousComplexification a k ha ha1 hk
      (homogeneousLinearizedPotential a k ha ha1 hk m q)
    (P (L z).1 x, P (L z).2 x) =
      (-Complex.I * (spectralDiagonalCoefficient m (P q x) * P z.1 x +
          spectralCrossCoefficient m (P q x) * P z.2 x),
        Complex.I * (conj (spectralDiagonalCoefficient m (P q x)) * P z.2 x +
          conj (spectralCrossCoefficient m (P q x)) * P z.1 x)) := by
  dsimp only
  simp only [homogeneousComplexification_apply, map_add, map_smul,
    ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
    homogeneousConjugation_physical, smul_eq_mul,
    homogeneousLinearizedPotential_physical,
    homogeneousComplexReal_physical, homogeneousComplexImag_physical]
  simpa only [spectralCoefficient_decomposition, ← starRingEnd_apply] using
      circularComplexification_scalar (spectralDiagonalCoefficient m (P q x))
        (spectralCrossCoefficient m (P q x)) (P z.1 x) (P z.2 x)

end

end DefocusingNLS

end OAI
