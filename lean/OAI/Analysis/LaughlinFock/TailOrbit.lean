import Mathlib
import OAI.Analysis.LaughlinFock.SquareSplitting
import OAI.Analysis.LaughlinFock.ThreeOrbit

namespace OAI

/-! Tail Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem threeSpinProjection_relative_bound {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (((spinRatio Q z * (z+1) : ℝ) : ℂ) • hamiltonian Q -
      exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z *
        (threeWedgeMatrix Q)ᴴ)).PosSemidef := by
  have ha := fockAverage_posSemidef Q _ (highestThreeAnnihilator_pair_posSemidef hQ hz)
  rw [map_sub, fockAverage_highestThree hQ hz,
    fockAverage_pair_family (by omega : 1 ≤ Q) (fun p : Fin (z+1) => p.val)
      (by intro p; have := p.isLt; omega), Fintype.card_fin] at ha
  have hn : ((3*Q-1-2*z : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 3*Q-1-2*z ≠ 0 by omega)
  have hc : ((3*Q-1-2*z : ℕ) : ℂ) *
      ((z+1 : ℕ) / ((2*Q-1 : ℕ) : ℂ)) = ((spinRatio Q z * (z+1) : ℝ) : ℂ) := by
    push_cast [spinRatio, Nat.cast_sub (show 2*z ≤ 3*Q-1 by omega),
      Nat.cast_sub (show 1 ≤ 3*Q by omega), Nat.cast_sub (show 1 ≤ 2*Q by omega)]
    ring
  have hh := ha.smul (show (0:ℂ) ≤ ((3*Q-1-2*z : ℕ) : ℂ) by exact_mod_cast (Nat.zero_le _))
  simpa only [smul_sub, smul_smul, hc, one_div, mul_inv_cancel₀ hn, one_smul] using hh

 

theorem gramShift_even_nonneg {Q z : ℕ} (hQ : 1 ≤ Q) (hz₁ : 1 ≤ z)
    (hz : z ≤ Q) (he : Even z) : 0 ≤ gramShift Q z := by
  have hQr : 0 < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hzr : (1:ℝ) ≤ z := by exact_mod_cast hz₁
  have hzQ : (z:ℝ) ≤ Q := by exact_mod_cast hz
  have hdiv : (z:ℝ)*(z+1)/Q ≤ z+1 := by
    rw [div_le_iff₀ hQr]
    nlinarith
  have hb : 0 ≤ 3*(z:ℝ)-1-z*(z+1)/Q := by linarith
  rw [gramShift, he.neg_pow, one_pow, one_mul]
  exact mul_nonneg (fallingRatio_nonneg Q z) hb

 

theorem threeSpinProjection_negative_bound {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    ((gramShift Q z : ℂ) •
        exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ) +
      ((spinRatio Q z * |gramShift Q z| * (z+1) : ℝ) : ℂ) • hamiltonian Q).PosSemidef := by
  let X := exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ)
  have h₁ := (threeSpinProjection_relative_bound hQ hz).smul
    (show (0:ℂ) ≤ (|gramShift Q z| : ℝ) by exact_mod_cast abs_nonneg (gramShift Q z))
  have h₂ := (threeSpinProjection_lift_posSemidef Q z).smul
    (show (0:ℂ) ≤ ((gramShift Q z + |gramShift Q z| : ℝ) : ℂ) by
      exact_mod_cast (show 0 ≤ gramShift Q z + |gramShift Q z| by linarith [neg_le_abs (gramShift Q z)]))
  have he : ((|gramShift Q z| : ℝ) : ℂ) • (((spinRatio Q z * (z+1) : ℝ) : ℂ) • hamiltonian Q-X) +
      ((gramShift Q z+|gramShift Q z| : ℝ) : ℂ) • X =
    (gramShift Q z : ℂ) • X + ((spinRatio Q z * |gramShift Q z| * (z+1) : ℝ) : ℂ) • hamiltonian Q := by
    push_cast
    simp only [smul_sub, smul_smul, add_smul]
    rw [show ((|gramShift Q z| : ℝ) : ℂ) * ((spinRatio Q z : ℂ)*((z:ℂ)+1)) =
      (spinRatio Q z : ℂ)*((|gramShift Q z| : ℝ) : ℂ)*((z:ℂ)+1) by ring]
    abel
  exact he ▸ h₁.add h₂

 

theorem tailCoefficient_eq_Ico (Q : ℕ) :
    tailCoefficient Q = ∑ z ∈ Finset.Ico 16 (Q+1),
      if Odd z then spinRatio Q z * |gramShift Q z| * (z+1) else 0 := by
  classical
  rw [tailCoefficient_eq_odd_sum, ← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hz, hz₁, ho⟩; exact ⟨⟨by omega,hz⟩,ho⟩
  · rintro ⟨⟨hz₁,hz⟩,ho⟩
    have hp := Nat.odd_iff.mp ho
    exact ⟨hz,by omega,ho⟩

 

theorem tailThreeTarget_relative_bound {Q : ℕ} (hQ : 2 ≤ Q) :
    (tailThreeTarget Q + (tailCoefficient Q : ℂ) • hamiltonian Q).PosSemidef := by
  classical
  have hm (c : ℂ) (M : Matrix (SectorOccupation Q 3) (SectorOccupation Q 3) ℂ) :
      exteriorLift Q 3 (c • M) = c • exteriorLift Q 3 M :=
    (exteriorLiftLinear Q 3).map_smul c M
  have hs : tailThreeTarget Q + (tailCoefficient Q : ℂ) • hamiltonian Q =
      ∑ z ∈ Finset.Ico 16 (Q+1),
        ((gramShift Q z : ℂ) • exteriorLift Q 3
          (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ) +
        ((if Odd z then spinRatio Q z * |gramShift Q z| * (z+1) else 0 : ℝ) : ℂ) • hamiltonian Q) := by
    simp only [tailThreeTarget, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, exteriorLift_sum, hm,
      tailCoefficient_eq_Ico, Complex.ofReal_sum, ← Finset.sum_smul, Finset.sum_add_distrib]
  rw [hs]
  apply Matrix.posSemidef_sum
  intro z hm
  have hz : z ≤ Q := by have := (Finset.mem_Ico.mp hm).2; omega
  have hz₁ : 1 ≤ z := by have := (Finset.mem_Ico.mp hm).1; omega
  by_cases ho : Odd z
  · rw [ite_eq_left ho]
    exact threeSpinProjection_negative_bound hQ hz
  · rw [ite_eq_right ho, Complex.ofReal_zero, zero_smul, add_zero]
    exact (threeSpinProjection_lift_posSemidef Q z).smul
      (by exact_mod_cast gramShift_even_nonneg (by omega : 1 ≤ Q) hz₁ hz (Nat.not_odd_iff_even.mp ho))

end LaughlinFock
end

end OAI
