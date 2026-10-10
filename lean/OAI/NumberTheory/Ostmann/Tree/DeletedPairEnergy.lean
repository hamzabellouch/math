import OAI.NumberTheory.Ostmann.Tree.NonnegativeDifference

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

def deletedPairEnergy (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℝ :=
  if d=0 then 0 else ‖pairSpectrum g χ ((σ:ZMod p)*d)‖^2

theorem deletedPairEnergy_nonneg (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ : MulChar (ZMod p) ℂ) (d : ZMod p) : 0≤deletedPairEnergy g σ χ d := by
  unfold deletedPairEnergy
  split_ifs <;> positivity

theorem deletedPairEnergy_total (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ : MulChar (ZMod p) ℂ) :
    (∑ d : ZMod p,deletedPairEnergy g σ χ d)≤(p:ℝ)*pairFourthMass g χ := by
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  calc
    _ ≤ ∑ d : ZMod p,‖pairSpectrum g χ ((σ:ZMod p)*d)‖^2 := by
      apply Finset.sum_le_sum
      intro d _
      unfold deletedPairEnergy
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl
    _ = _ := by
      rw [pairFourthMass_eq_l2Sq,← l2Sq_unitMul (pairSpectrum g χ) σ]
      unfold l2Sq
      field_simp

def pairSquareEnergy (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (d : ZMod p) : ℝ := by
  classical
  exact ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,deletedPairEnergy g σ χ d

theorem pairSquareEnergy_nonneg (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) (d : ZMod p) : 0≤pairSquareEnergy g σ ρ d := by
  classical
  exact Finset.sum_nonneg (fun χ _ => deletedPairEnergy_nonneg g σ χ d)

theorem pairSquareEnergy_total (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    (∑ d : ZMod p,pairSquareEnergy g σ ρ d) ≤
      (p:ℝ)*∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,pairFourthMass g χ := by
  classical
  unfold pairSquareEnergy
  rw [Finset.sum_comm,Finset.mul_sum]
  exact Finset.sum_le_sum (fun χ _ => deletedPairEnergy_total g σ χ)

theorem pairFourthMass_square_fiber (g : ZMod p → ℂ) (ρ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,pairFourthMass g χ) ≤
      2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2*(correlationBound g:ℝ)^2 := by
  classical
  let B : ℝ := ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2*(correlationBound g:ℝ)^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hχ (χ : MulChar (ZMod p) ℂ) : pairFourthMass g χ≤B := by
    exact (pairFourthMass_le g χ hg0).trans
      ((mul_le_mul_of_nonneg_left hg hB).trans_eq (mul_one _))
  calc
    _ ≤ ∑ χ : MulChar (ZMod p) ℂ with χ^2=ρ,B := Finset.sum_le_sum (fun χ _ => hχ χ)
    _ ≤ 2*B := by
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast character_square_fiber_card (Finset.univ.filter (fun χ : MulChar (ZMod p) ℂ => χ^2=ρ)) ρ
        (fun χ hχ => (Finset.mem_filter.mp hχ).2)
    _ = _ := by dsimp [B]; ring

end
end Ostmann.FiniteField

end OAI
