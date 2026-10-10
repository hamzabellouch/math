import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseNorm
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! The actual simplex vertex satisfies every scalar phase condition
of the original physical plane estimate, uniformly in the shift count. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem source_vertex_plane_parameters (L D : ℝ) (K : ℕ)
    (hL : 256 ≤ L) (hD : 2 ≤ D) (hK : 0 < K)
    (i : Fin K) (eta : Fin K → ℝ)
    (heta : Real.sqrt (∑ j, (eta j)^2) ≤ L^2) :
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu D p
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let a := mu/(K:ℝ)
    let phase := phaseTubePoint (Pi.single i mu) eta
    0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧
      (alpha-1)/p ≤ 1/12 ∧ p*mu = alpha-1 ∧
      (∀ j, ‖phase j‖ ≤ 2*L^2) ∧
      (∀ j, j ≠ i → (phase j).re = 0) ∧ (phase i).re = mu := by
  classical
  dsimp only
  let mu := PhaseCombinatorics.phaseMu D (Real.sqrt L)
  let alpha := 2+PhaseCombinatorics.phaseParameter D
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hmu : 0 < mu ∧ mu ≤ 1/12 := source_phaseMu_small (by linarith) hL
  have htheta := PhaseCombinatorics.phaseParameter_range (by linarith : 1 ≤ D)
  change 0 < PhaseCombinatorics.phaseParameter D ∧
    PhaseCombinatorics.phaseParameter D ≤ 1/3 at htheta
  have hKreal : (1:ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K from hK)
  have halpha : 1 ≤ alpha ∧ alpha ≤ 3 := by
    dsimp only [alpha]
    constructor <;> linarith [htheta.1,htheta.2]
  have hquot : (alpha-1)/Real.sqrt L = mu := by
    dsimp only [alpha,mu,PhaseCombinatorics.phaseMu]
    congr 1
    ring
  have hrelation : Real.sqrt L*mu = alpha-1 := by
    rw [←hquot]
    exact mul_div_cancel₀ _ hp.ne'
  have ha0 : 0 ≤ mu/(K:ℝ) := div_nonneg hmu.1.le (zero_le_one.trans hKreal)
  have ha1 : mu/(K:ℝ) ≤ 1 :=
    (div_le_self hmu.1.le hKreal).trans (by linarith)
  refine ⟨ha0,ha1,halpha.1,halpha.2,?_,hrelation,?_,?_,?_⟩
  · rw [hquot]
    exact hmu.2
  · intro j
    have hn := sourceShiftSimplex_phase_norm (Pi.single i mu) eta
      (sourceShiftSimplex_vertex hmu.1.le i) j
    have hL2 : 1 ≤ L^2 := one_le_pow₀ (by linarith : 1 ≤ L)
    exact hn.trans (by linarith [hmu.2,heta])
  · intro j hji
    simp [phaseTubePoint,hji]
  · simp [phaseTubePoint]

end LipschitzHilbert

end

end OAI
