import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorPotential
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDerivativeConjugation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedCompact

namespace OAI

/-! # Compact top-order error for the actual odd-power linearization

The first two terms in the displayed identity are exactly the pointwise
principal coefficients acting on the ordered derivative. The remaining
real-linear map vanishes strongly on every bounded weakly null sequence.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure E)

noncomputable def homogeneousLinearizedTopCommutator (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) :
    HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] H :=
  ((homogeneousTopCommutator a (N + 1) ha ha1 hk j
    (homogeneousLinearizedFirstCoefficient a ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)).restrictScalars ℝ) +
  ((homogeneousTopCommutator a (N + 1) ha ha1 hk j
    (homogeneousLinearizedSecondCoefficient a ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)).restrictScalars ℝ).comp
      (homogeneousConjugation a ((N + 1 : ℕ) : ℝ) ha ha1 hk)

theorem homogeneousLinearized_ordered_derivative (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (m : ℕ) (q u : HomogeneousY a ((N + 1 : ℕ) : ℝ)) :
    homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j
      (homogeneousLinearizedPotential a ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u) =
    homogeneousPhysicalL2Product a ((N + 1 : ℕ) : ℝ) ha ha1 hk
        (homogeneousLinearizedFirstCoefficient a ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)
        (homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j u) +
      homogeneousPhysicalL2Product a ((N + 1 : ℕ) : ℝ) ha ha1 hk
        (homogeneousLinearizedSecondCoefficient a ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)
        (star (homogeneousPhysicalDerivative a (N + 1) ha ha1 hk j u)) +
      homogeneousLinearizedTopCommutator a N ha ha1 hk j m q u := by
  rw [homogeneousLinearizedPotential_decomposition, map_add]
  simp only [homogeneousLinearizedTopCommutator, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    homogeneousTopCommutator_apply, homogeneousTopCommutatorValue,
    homogeneousPhysicalDerivative_conjugation]
  abel

theorem tendsto_homogeneousLinearizedTopCommutator (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ))
    (u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ)) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousLinearizedTopCommutator a N ha ha1 hk j m q (u n))
      atTop (𝓝 0) := by
  have hfirst := tendsto_homogeneousTopCommutator a M N ha ha1 hk j
    (homogeneousLinearizedFirstCoefficient a ((N + 1 : ℕ) : ℝ) ha ha1 hk m q) u hu hweak
  have hconj (ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ) :
      Tendsto (fun n => ℓ (homogeneousConjugation a ((N + 1 : ℕ) : ℝ) ha ha1 hk (u n))) atTop (𝓝 0) :=
    hweak (ℓ.comp (homogeneousConjugation a ((N + 1 : ℕ) : ℝ) ha ha1 hk))
  have hsecond := tendsto_homogeneousTopCommutator a M N ha ha1 hk j
    (homogeneousLinearizedSecondCoefficient a ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)
    (fun n => homogeneousConjugation a ((N + 1 : ℕ) : ℝ) ha ha1 hk (u n))
    (fun n => by simpa only [homogeneousConjugation_norm] using hu n) hconj
  simpa only [homogeneousLinearizedTopCommutator, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', add_zero] using
      hfirst.add hsecond

end DefocusingNLS

end OAI
