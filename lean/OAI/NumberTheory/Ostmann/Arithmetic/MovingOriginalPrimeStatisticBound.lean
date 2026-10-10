import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPrimeStatistic
import OAI.NumberTheory.Ostmann.Characters.MixedExternalMass
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalOuterWeight

namespace OAI

/-! # A finite upper bound for the original symmetrized statistic -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalPrimeStatistic_upper {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφnorm : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hν : ∀ b a, 0 ≤ ν b a) (hmass : ∀ b, ∑ a, ν b a = 1) (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ)
    (hshort : w ≤ r + 1) (hvcenter : v ≤ center + 1) (E : ℝ) (hE : 0 ≤ E)
    (henergy : (movingOriginalSymmetrizedEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg Jleft Jright diagonal u v r w center).re ≤ E) :
    ‖movingOriginalPrimeStatistic q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg ggiant favorable Jleft Jright diagonal u v r w‖ ^ 2 ≤
      Real.exp (center - u) ^ 2 * diagonalOuterMajorant Bφ Dφ diagonal *
        (2 * V n + 1 : ℕ) * Real.exp 2 * E := by
  let W := fun (_ : ℤ) (_ : B → σ) (x z : ℝ) =>
    giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hC := (diagonalOuterMajorant_pos Bφ Dφ diagonal).le
  have hW (s y x z) : 0 ≤ (W s y x z).re := by
    obtain ⟨a, ha, heq⟩ := giantOuterWeight_positive φ hφ Jleft Jright diagonal
      ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    change W s y x z = (a : ℂ) at heq
    rw [heq]
    exact ha
  have hWupper (s y x z) : (W s y x z).re ≤ diagonalOuterMajorant Bφ Dφ diagonal := by
    apply (Complex.re_le_norm _).trans
    exact (giantOuterWeight_norm φ Jleft Jright Bφ Dφ hBφ hDφ hφnorm hlip hout diagonal _ _).trans
      (by unfold diagonalOuterMajorant; linarith)
  have hm0 := mixedExternalAverage_re_nonneg ν hν (V n) u v r w center W hW
  have hmb := mixedExternalAverage_mass_bound ν hν hmass (V n) u v r w center
    (diagonalOuterMajorant Bφ Dφ diagonal) hC W hWupper
  have hmupper : (mixedExternalAverage ν (V n) u v r w center W).re ≤
      diagonalOuterMajorant Bφ Dφ diagonal * (2 * V n + 1 : ℕ) * Real.exp 2 := by
    apply hmb.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (mul_nonneg hC (Nat.cast_nonneg _))
  have hc := movingOriginalPrimeStatistic_cauchy q value outside μ ν childBound pivotBound V f g Dq S
    ψ X lo hi φ hφ G n m small slot hsmall hν hidentical greg ggiant favorable
    Jleft Jright diagonal u v r w center
  have hstep := mul_le_mul_of_nonneg_left henergy
    (mul_nonneg (sq_nonneg (Real.exp (center - u))) hm0)
  have hnext := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmupper (sq_nonneg (Real.exp (center - u)))) hE
  exact hc.trans ((hstep.trans hnext).trans_eq (by ring))

end Ostmann

end OAI
