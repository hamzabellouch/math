import OAI.NumberTheory.Ostmann.Tree.NonnegativeDifference

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]

def crossSquareMajorant (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ := by
  classical
  exact ∑ ν : MulChar (ZMod p) ℂ with ν^2=ρ,crossMajorant g h σ τ L R ν y

theorem crossSquareMajorant_nonneg (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0≤crossSquareMajorant g h σ τ L R ρ y := by
  classical
  exact Finset.sum_nonneg (fun ν _ => crossMajorant_nonneg g h σ τ L R ν y)

theorem crossSquareMajorant_mean_small (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ρ : MulChar (ZMod p) ℂ)
    (hσ : (σ:ZMod p)^2=1) (hτ : (τ:ZMod p)^2=1)
    (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    unitMean (crossSquareMajorant g h σ τ L R ρ) ≤
      200*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
      ((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ))) := by
  classical
  let B : ℝ := 100*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
      ((correlationBound g:ℝ)^2+(correlationBound h:ℝ)^2+Real.sqrt (3/(p:ℝ)))
  have hB : 0≤B := by dsimp [B]; positivity
  unfold crossSquareMajorant
  rw [unitMean_sum]
  calc
    _ ≤ ∑ ν : MulChar (ZMod p) ℂ with ν^2=ρ,B := Finset.sum_le_sum
      (fun ν _ => crossMajorant_mean_small g h σ τ L R ν hσ hτ hg0 hg hh0 hh)
    _ ≤ 2*B := by
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast character_square_fiber_card (Finset.univ.filter (fun ν : MulChar (ZMod p) ℂ => ν^2=ρ)) ρ
        (fun ν hν => (Finset.mem_filter.mp hν).2)
    _ = _ := by dsimp [B]; ring

theorem crossSquareMajorant_mean_total (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (hg0 : g 0=0) (hg : l2Sq g≤1) (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (crossSquareMajorant g h σ τ L R ρ)) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  classical
  unfold crossSquareMajorant
  simp_rw [unitMean_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact crossMajorant_mean_total g h σ τ L R hg0 hg hh0 hh

end
end Ostmann.FiniteField

end OAI
