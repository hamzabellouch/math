import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousL2Product
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorFourier

namespace OAI

/-! # The actual top-order commutator on the faithful homogeneous space

This is the difference between differentiating the physical product and
multiplying the physical derivative. Its coefficient dependence is bounded
in the Y norm, allowing approximation of the actual profile coefficients.
-/

open MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "H" => Lp ℂ 2 (volume : Measure E)

noncomputable def homogeneousTopCommutatorValue (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (V u : HomogeneousY a N) : H :=
  homogeneousPhysicalDerivative a N ha ha1 hk j (homogeneousYProduct a N ha ha1 hk V u) -
    homogeneousPhysicalL2Product a N ha ha1 hk V (homogeneousPhysicalDerivative a N ha ha1 hk j u)

theorem homogeneousTopCommutatorValue_norm_le (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (V u : HomogeneousY a N) :
    ‖homogeneousTopCommutatorValue a N ha ha1 hk j V u‖ ≤
      (‖homogeneousYProduct a N ha ha1 hk‖ + ‖homogeneousPointEvaluation a N ha ha1 hk 0‖) *
        ‖V‖ * ‖u‖ := by
  let B := homogeneousYProduct a N ha ha1 hk
  let D := homogeneousPhysicalDerivative a N ha ha1 hk j
  let P := homogeneousPhysicalL2Product a N ha ha1 hk
  have hD : ‖D (B V u)‖ ≤ ‖B‖ * ‖V‖ * ‖u‖ :=
    (homogeneousPhysicalDerivative_norm_le a N ha ha1 hk j _).trans (B.le_opNorm₂ V u)
  have hP : ‖P V (D u)‖ ≤ ‖homogeneousPointEvaluation a N ha ha1 hk 0‖ * ‖V‖ * ‖u‖ := by
    exact (homogeneousPhysicalL2ProductValue_norm_le a N ha ha1 hk V (D u)).trans
      (mul_le_mul_of_nonneg_left (homogeneousPhysicalDerivative_norm_le a N ha ha1 hk j u)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  change ‖D (B V u) - P V (D u)‖ ≤ _
  calc
    _ ≤ ‖D (B V u)‖ + ‖P V (D u)‖ := norm_sub_le _ _
    _ ≤ ‖B‖ * ‖V‖ * ‖u‖ + ‖homogeneousPointEvaluation a N ha ha1 hk 0‖ * ‖V‖ * ‖u‖ := add_le_add hD hP
    _ = _ := by ring

noncomputable def homogeneousTopCommutator (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12) :
    HomogeneousY a N →L[ℂ] HomogeneousY a N →L[ℂ] H :=
  (LinearMap.mk₂ ℂ (homogeneousTopCommutatorValue a N ha ha1 hk j)
    (fun V W u => by
      simp only [homogeneousTopCommutatorValue, map_add, add_apply]
      abel)
    (fun c V u => by
      simp only [homogeneousTopCommutatorValue, map_smul, smul_apply, smul_sub])
    (fun V u v => by
      simp only [homogeneousTopCommutatorValue, map_add]
      abel)
    (fun c V u => by
      simp only [homogeneousTopCommutatorValue, map_smul, smul_sub])).mkContinuous₂
    (‖homogeneousYProduct a N ha ha1 hk‖ + ‖homogeneousPointEvaluation a N ha ha1 hk 0‖)
    (homogeneousTopCommutatorValue_norm_le a N ha ha1 hk j)

@[simp] theorem homogeneousTopCommutator_apply (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (V u : HomogeneousY a N) :
    homogeneousTopCommutator a N ha ha1 hk j V u =
      homogeneousTopCommutatorValue a N ha ha1 hk j V u := rfl

theorem homogeneousTopCommutator_Schwartz (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (V f : 𝓢(E, ℂ)) :
    homogeneousTopCommutator a N ha ha1 hk j
      (homogeneousSchwartzEmbedding a N ha ha1 hk V)
      (homogeneousSchwartzEmbedding a N ha ha1 hk f) =
      (homogeneousOrderedCommutator N j V f).toLp 2 volume := by
  change homogeneousPhysicalDerivative a N ha ha1 hk j
    (homogeneousYProduct a N ha ha1 hk
      (homogeneousSchwartzEmbedding a N ha ha1 hk V)
      (homogeneousSchwartzEmbedding a N ha ha1 hk f)) -
    homogeneousPhysicalL2Product a N ha ha1 hk
      (homogeneousSchwartzEmbedding a N ha ha1 hk V)
      (homogeneousPhysicalDerivative a N ha ha1 hk j
        (homogeneousSchwartzEmbedding a N ha ha1 hk f)) = _
  rw [homogeneousYProduct_physicalSchwartz, homogeneousPhysicalDerivative_Schwartz,
    homogeneousPhysicalDerivative_Schwartz]
  change (homogeneousOrderedDerivative N j (SchwartzMap.smulLeftCLM ℂ V f)).toLp 2 volume -
    homogeneousPhysicalL2Product a N ha ha1 hk
      (homogeneousSchwartzEmbedding a N ha ha1 hk V)
      ((homogeneousOrderedDerivative N j f).toLp 2 volume) = _
  rw [homogeneousPhysicalL2Product_Schwartz]
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ - (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ =
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume) (_ - _)
  rw [map_sub]

end DefocusingNLS

end OAI
