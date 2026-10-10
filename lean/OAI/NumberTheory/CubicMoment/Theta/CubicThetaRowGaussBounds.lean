import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowPoisson

namespace OAI

/-! Elementary bounds and the exact norm of the fixed dual frequency. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_norm (c d : Eisenstein) :
    ‖cubicThetaEisensteinWeight c d‖ ≤ 1 := by
  unfold cubicThetaEisensteinWeight
  split_ifs with h
  · exact norm_cubicSymbol_le_one h.1 c
  · norm_num

lemma cubicThetaEisensteinGaussCoefficient_norm {c : Eisenstein} (hc : c ≠ 0)
    (h : Eisenstein) :
    ‖cubicThetaEisensteinGaussCoefficient c h‖ ≤ (Nat.card (Residues (3*c)):ℝ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  unfold cubicThetaEisensteinGaussCoefficient
  rw [tsum_fintype, Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ x : Residues (3*c),
        ‖cubicThetaEisensteinResidueWeight c x*
          (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
            ((h:ℂ)/((3*c:Eisenstein)*traceLambda))):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residues (3*c), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, Circle.norm_coe, mul_one]
      exact cubicThetaEisensteinWeight_norm c _
    _ = _ := by simp

def cubicThetaRowFrequency (h : Eisenstein) : ℂ := (h:ℂ)/(3*traceLambda)

def cubicThetaRowHeatScale (h : Eisenstein) : ℝ :=
  4*Real.pi^2*Complex.normSq (cubicThetaRowFrequency h)

lemma cubicThetaRowHeatScale_eq (h : Eisenstein) :
    cubicThetaRowHeatScale h = (4*Real.pi^2/27)*norm h := by
  unfold cubicThetaRowHeatScale cubicThetaRowFrequency
  rw [Complex.normSq_div, map_mul, traceLambda_normSq]
  norm_num
  change 4*Real.pi^2*(norm h/27) = _
  ring

lemma cubicThetaRowHeatScale_pos {h : Eisenstein} (hh : h ≠ 0) :
    0 < cubicThetaRowHeatScale h := by
  rw [cubicThetaRowHeatScale_eq]
  exact mul_pos (by positivity) (norm_pos_of_ne_zero hh)

@[simp] lemma cubicThetaRowHeatScale_zero : cubicThetaRowHeatScale 0 = 0 := by
  simp [cubicThetaRowHeatScale_eq, norm]

end CubicFirstMoment

end

end OAI
