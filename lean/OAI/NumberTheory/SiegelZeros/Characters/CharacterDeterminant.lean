import Mathlib.Analysis.Real.Sqrt
import OAI.NumberTheory.SiegelZeros.Determinants.GeneratedGreedyDivisibility
import OAI.NumberTheory.SiegelZeros.Structure.Radicand

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W60

open scoped BigOperators NumberField
open WeightedTorusJets

noncomputable def sqrtTwo : ℂ := (Real.sqrt 2 : ℂ)

theorem sqrtTwo_sq : sqrtTwo ^ 2 = (2 : ℂ) := by
  change (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = (2 : ℂ)
  exact_mod_cast (Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num))

theorem actual_character_determinant_norm_divisibility
    {q M : ℕ} [NeZero q] (hq3 : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hreal : W09.IsRealCharacter χ) (hn : χ ≠ 1)
    (H C : ℕ) (hH : 2 ≤ H) (exponents : Fin M → Fin 4 →₀ ℕ) :
    ∃ (d k : ℤ) (a : ℂ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
      (ha : a ^ 2 = (d : ℂ)),
      W09.signedConductor χ = k ^ 2 * d ∧ d.natAbs ≤ q ∧
      IntermediateField.adjoin ℚ ({a} : Set ℂ) = W09.characterField χ ∧
      let L := SiegelZeros.W10.rootField a sqrtTwo
      let f := algebraMap (𝓞 L) L
      let u := W37.integralRootA a sqrtTwo d ha sqrtTwo_sq
      let v := W37.integralRootB a sqrtTwo d ha sqrtTwo_sq
      let n : Fin M → Fin 4 → ℤ := fun j i => (exponents j i : ℤ)
      W29.rowSpan (K := L)
        (weightedRow f (fun j => Awei.W39.theta u v (n j))
          (fun j => Awei.W39.theta (-u) v (n j))
          (fun j => Awei.W39.theta (-u) (-v) (n j))) (W62.cutoff H C) = ⊤ →
      ∃ hcard : (greedySet f H C
        (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j))).card = M,
      let idx := greedyIndex f H C
        (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j)) hcard
      let Δ := W37.concreteDelta a sqrtTwo d hd hd1 hd2 ha sqrtTwo_sq exponents
        (fun i => (idx i).coords)
      Δ ≠ 0 ∧ Algebra.norm ℤ Δ ≠ 0 ∧
        (Algebra.norm ℤ Δ : ℚ) = Algebra.norm ℚ (Δ : L) ∧
        ∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ (p : ZMod q) = -1 →
          (p : ℤ) ^ (4 * (∑ i, (idx i).coords 0 / p)) ∣ Algebra.norm ℤ Δ := by
  obtain ⟨d, k, a, hd, hd1, hd2, hk, hD, hbound, hadef, ha, hfield, hsign⟩ :=
    Awei.W39.actual_squarefree_radicand_with_prime_signs hq3 hq8 χ hprim hreal hn
  refine ⟨d, k, a, hd, hd1, hd2, ha, hD, hbound, hfield, ?_⟩
  dsimp only
  intro hspan
  let : NumberField (SiegelZeros.W10.rootField a sqrtTwo) :=
    SiegelZeros.W10.squarefreeRootField_numberField a sqrtTwo d hd hd1 hd2 ha sqrtTwo_sq
  obtain ⟨hcard, hnonzero, hdiv⟩ := exists_concrete_greedy_divisibility
    a sqrtTwo d hd hd1 hd2 ha sqrtTwo_sq H C (lt_of_lt_of_le (by decide : 0 < 2) hH)
    exponents hspan
  refine ⟨hcard, hnonzero, W43.integral_norm_ne_zero _ hnonzero,
    Algebra.coe_norm_int _, ?_⟩
  intro p hp hpH hpq hχ
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := ne_of_gt (lt_of_le_of_lt hH hpH)
  have hleg : legendreSym p d = -1 :=
    Awei.W39.realCharacter_goodPrime_legendre_radicand H p hH hpH hpq χ hprim
      hreal hχ d k hD
  exact W43.quartic_norm_dvd
    (SiegelZeros.W10.squarefreeRootField_finrank a sqrtTwo d hd hd1 hd2 ha sqrtTwo_sq)
    p _ _ (hdiv p hp hpH hp2 hleg)

end SiegelZerosAwei.W60


end SiegelZeros

end OAI
