import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanInversion

namespace OAI

/-! The finite Kloosterman operator factors into two exact Fourier
transforms and a weighted unit inversion. In particular its energy norm
has the sharp finite Fourier factor, with no logarithmic loss. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaFiniteKloostermanApply (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (h : Residues (3*c)) : ℂ :=
  ∑ k : Residues (3*c),cubicThetaFiniteKloosterman c hc0 h k*f k

lemma cubicThetaFiniteKloostermanApply_factor (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) (h : Residues (3*c)) :
    cubicThetaFiniteKloostermanApply c hc0 f h=
      cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0)
        (cubicThetaWeightedResidueInversion c
          (cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f)) h := by
  unfold cubicThetaFiniteKloostermanApply cubicThetaFiniteKloosterman
    cubicThetaFiniteFourier cubicThetaWeightedResidueInversion
  simp_rw [tsum_fintype,AddChar.map_add_eq_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (Ring.inverse x) k]
  ring

theorem cubicThetaFiniteKloostermanApply_contract (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (∑ h : Residues (3*c),‖cubicThetaFiniteKloostermanApply c hc0 f h‖^2)≤
      (Fintype.card (Residues (3*c)):ℝ)^2*∑ k : Residues (3*c),‖f k‖^2 := by
  simp_rw [cubicThetaFiniteKloostermanApply_factor]
  rw [cubicThetaFiniteFourier_norm_sq]
  calc
    _ ≤ (Fintype.card (Residues (3*c)):ℝ)*
        ∑ x : Residues (3*c),‖cubicThetaFiniteFourier (3*c) (mul_ne_zero (by norm_num) hc0) f x‖^2 :=
      mul_le_mul_of_nonneg_left (cubicThetaWeightedResidueInversion_contract c _) (by positivity)
    _ = _ := by rw [cubicThetaFiniteFourier_norm_sq]; ring

end CubicFirstMoment

end

end OAI
