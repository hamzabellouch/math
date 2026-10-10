import OAI.Analysis.MarkovType.ReversibleMartingales
import OAI.Analysis.MarkovType.PowerSmoothness
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem stateCost_le_of_symmetricPowerSmooth {q D : ℝ}
    (hq : 1 ≤ q) (hq₂ : q ≤ 2) (hD : 1 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    {S : Type*} [Fintype S] (C : FiniteReversibleChain S)
    (f : S → X) (n : ℕ) :
    stateCost C f q n ≤ 64 * D * (n : ℝ) * stateCost C f q 1 := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hcost : 0 ≤ stateCost C f q 1 := stateCost_nonneg C f q 1
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · subst n
    have heven := even_stateCost_le hq hq₂ hD0 hsmooth C f m
    have hprod : 0 ≤ D * ((2 * m : ℕ) : ℝ) * stateCost C f q 1 :=
      mul_nonneg (mul_nonneg hD0 (Nat.cast_nonneg _)) hcost
    nlinarith only [heven, hprod]
  · subst n
    have hstep := stateCost_succ_le_two hq hq₂ C f (2 * m)
    have heven := even_stateCost_le hq hq₂ hD0 hsmooth C f m
    have hcostD : stateCost C f q 1 ≤ D * stateCost C f q 1 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD hcost
    have hcast : ((2 * m + 1 : ℕ) : ℝ) = ((2 * m : ℕ) : ℝ) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    nlinarith only [hstep, heven, hcostD, hcost]

theorem markovTypeWith_of_symmetricPowerSmooth {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hD : 1 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X) :
    MarkovTypeWith q (64 * D) X := by
  have hK : 1 ≤ 64 * D := by linarith
  refine ⟨lt_trans zero_lt_one hq, lt_of_lt_of_le zero_lt_one hK, ?_⟩
  intro m C f n _hn
  have hbound := stateCost_le_of_symmetricPowerSmooth hq.le hq₂ hD hsmooth C f n
  have hpower : 64 * D ≤ (64 * D) ^ q := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hK hq.le)
  calc
    stateCost C f q n ≤ 64 * D * (n : ℝ) * stateCost C f q 1 := hbound
    _ ≤ (64 * D) ^ q * (n : ℝ) * stateCost C f q 1 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg n))
        (stateCost_nonneg C f q 1)

theorem markovTypeWith_of_symmetricPowerSmooth_nonneg {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (_hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X) :
    MarkovTypeWith q (64 * max 1 D) X := by
  apply markovTypeWith_of_symmetricPowerSmooth hq hq₂ (le_max_left 1 D)
  intro x y
  have hmono := mul_le_mul_of_nonneg_right (le_max_right 1 D)
    (Real.rpow_nonneg (norm_nonneg y) q)
  have hbase := hsmooth x y
  nlinarith only [hmono, hbase]

theorem markovTypeWith_of_normPowerSmooth {q C : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hC : 0 ≤ C)
    (hsmooth : NormPowerSmoothWith q C X) :
    MarkovTypeWith q (64 * (1 + q * C)) X := by
  apply markovTypeWith_of_symmetricPowerSmooth hq hq₂
  · have := mul_nonneg (le_trans zero_le_one hq.le) hC
    linarith
  · exact symmetricPowerSmoothWith_of_normPowerSmooth hq hq₂ hC hsmooth

theorem hasMarkovType_of_normPowerSmooth {q C : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hC : 0 ≤ C)
    (hsmooth : NormPowerSmoothWith q C X) : HasMarkovType q X := by
  exact ⟨64 * (1 + q * C), markovTypeWith_of_normPowerSmooth hq hq₂ hC hsmooth⟩

end MarkovSuperreflexivity

end OAI
