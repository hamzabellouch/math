import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHilbertCompact
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialCompactInclusion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialConductor
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierRadial

namespace OAI

/-! The compact Green operator on all nonzero trace-Fourier cusp modes.
The actual lattice norm supplies the finite-mode exhaustion. -/
noncomputable section
open Set
namespace CubicFirstMoment

abbrev CubicThetaNonzeroFrequency := {h : Eisenstein // h≠0}
abbrev CubicThetaCuspModes := lp (fun _ : CubicThetaNonzeroFrequency => CubicThetaRadialL2) 2

def cubicThetaCuspPotential (h : CubicThetaNonzeroFrequency) : ℝ :=
  4*cubicThetaRowHeatScale h.val

lemma cubicThetaCuspPotential_pos (h : CubicThetaNonzeroFrequency) :
    0<cubicThetaCuspPotential h :=
  mul_pos (by norm_num) (cubicThetaRowHeatScale_pos h.property)

lemma cubicThetaCuspPotential_eq (h : CubicThetaNonzeroFrequency) :
    cubicThetaCuspPotential h=(16*Real.pi^2/27)*norm h.val := by
  rw [cubicThetaCuspPotential,cubicThetaRowHeatScale_eq]
  ring

def cubicThetaCuspGreen : CubicThetaCuspModes →L[ℂ] CubicThetaCuspModes :=
  cubicThetaHilbertDiagonal (fun h => cubicThetaRadialGreen (cubicThetaCuspPotential h))
    zero_le_one (fun _ => cubicThetaRadialGreen_norm _)

lemma cubicThetaCuspGreen_apply (F : CubicThetaCuspModes) (h : CubicThetaNonzeroFrequency) :
    cubicThetaCuspGreen F h=cubicThetaRadialGreen (cubicThetaCuspPotential h) (F h) := rfl

lemma cubicThetaCuspGreen_norm : ‖cubicThetaCuspGreen‖ ≤ 1 :=
  cubicThetaHilbertDiagonal_norm _ zero_le_one _

lemma cubicThetaCuspGreen_small_modes {ε : ℝ} (hε : 0<ε) :
    ∃ s : Finset CubicThetaNonzeroFrequency, ∀ h, h∉s →
      ‖cubicThetaRadialGreen (cubicThetaCuspPotential h)‖ ≤ ε := by
  classical
  let c : ℝ := 16*Real.pi^2/27
  have hc : 0<c := by dsimp [c]; positivity
  let R : ℝ := ε⁻¹/c
  have hfin : Set.Finite {h : CubicThetaNonzeroFrequency | norm h.val ≤ R} :=
    (finite_norm_le R).preimage Subtype.val_injective.injOn
  refine ⟨hfin.toFinset,?_⟩
  intro h hh
  have hN : R<norm h.val := lt_of_not_ge (by simpa using hh)
  have hmul : ε⁻¹<c*norm h.val := by
    have hh' := (div_lt_iff₀ hc).mp hN
    simpa [mul_comm] using hh'
  have hεmul : 1<ε*(c*norm h.val) := by
    have he := mul_lt_mul_of_pos_left hmul hε
    simpa [ne_of_gt hε] using he
  have hA := cubicThetaCuspPotential_pos h
  calc
    _ ≤ (1+cubicThetaCuspPotential h)⁻¹ := cubicThetaRadialGreen_conductor_bound hA.le
    _ ≤ ε := by
      rw [← one_div]
      apply (div_le_iff₀ (by linarith : 0<1+cubicThetaCuspPotential h)).mpr
      rw [cubicThetaCuspPotential_eq]
      change 1 ≤ ε*(1+c*norm h.val)
      nlinarith

theorem cubicThetaCuspGreen_compact : IsCompactOperator cubicThetaCuspGreen := by
  apply cubicThetaHilbertDiagonal_compact
  · exact fun h => cubicThetaRadialGreen_compact (cubicThetaCuspPotential_pos h)
  · exact fun ε hε => cubicThetaCuspGreen_small_modes hε

end CubicFirstMoment

end

end OAI
