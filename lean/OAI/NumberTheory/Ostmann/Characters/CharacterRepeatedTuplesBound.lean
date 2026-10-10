import OAI.NumberTheory.Ostmann.Characters.CharacterRepeatedTuplesDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters
open Construction Preliminaries

lemma reciprocal_sqrt_product_bound {M M₀ Q C N : ℝ}
    (hM₀ : 0 < M₀) (hM : M₀ ≤ M) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hN : 0 ≤ N) :
    (N/M)*(C*(Real.sqrt M/Q)) ≤ (C*N/Real.sqrt M₀)/Q := by
  calc
    _ = (C*N/Q)*(Real.sqrt M/M) := by ring
    _ = (C*N/Q)/Real.sqrt M := by rw [Real.sqrt_div_self']; ring
    _ ≤ (C*N/Q)/Real.sqrt M₀ := div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.mpr hM₀) (Real.sqrt_le_sqrt hM)
    _ = _ := by ring

theorem characterRepeatedContribution_bound {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (hχ : ∀ i, ∀ p ∈ E i, χ i p.val ≠ 1)
    (hz : ∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (hB : ∀ w, 0 ≤ B w ∧ B w ≤ 1)
    {X R M₀ M₁ : ℝ} (hX : 0 < X) (hR : 0 < R) (hM₀ : 0 < M₀)
    (hmin : ∀ i, ∀ p ∈ E i, R ≤ (p.val : ℝ))
    (hwindow : ∀ w : Fin b → PrimeUpTo Q, (∀ i, w i ∈ E i) → B w ≠ 0 →
      M₀ ≤ (characterTupleProduct w : ℝ) ∧ (characterTupleProduct w : ℝ) ≤ M₁)
    (hsmall : M₁ < 4*X*R) :
    ‖characterRepeatedContribution E hE χ a z B X‖ ≤
      (Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖*(∏ i, (primeShellMass (E i))⁻¹)/Real.sqrt M₀)*
        ((b : ℝ)^b*Real.exp (primeShellMass (Finset.univ.biUnion E))) := by
  classical
  let μ := characterTuplePrior E hE
  let N := ∏ i, (primeShellMass (E i))⁻¹
  let C := Real.sqrt X*‖𝓕 SchwartzCutoff.psi 0‖
  let K := C*N/Real.sqrt M₀
  have hN : 0 ≤ N := Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hE i).le)
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hC hN) (Real.sqrt_nonneg _)
  have hpoint (w : Fin b → PrimeUpTo Q) :
      μ.mass w*‖if Function.Injective w then 0 else
        (B w : ℂ)*characterTuplePhysical χ a z X w‖ ≤
      K*(if ∀ i, w i ∈ E i then 1/(characterTuplePeriod w : ℝ) else 0) := by
    by_cases hw : ∀ i, w i ∈ E i
    · rw [ite_eq_left hw]
      have hQ : (0 : ℝ) < characterTuplePeriod w := by exact_mod_cast characterTuplePeriod_pos w
      by_cases hinj : Function.Injective w
      · simp only [ite_eq_left hinj, norm_zero, mul_zero]
        positivity
      rw [ite_eq_right hinj]
      by_cases hbw : B w = 0
      · simp only [hbw, Complex.ofReal_zero, zero_mul, norm_zero, mul_zero]
        positivity
      have hn : ¬ Function.Injective (fun i => (w i).val) := by
        intro hn
        apply hinj
        intro i j hij
        exact hn (congrArg Subtype.val hij)
      have hper := repeated_distinct_product_le_div (fun i => (w i).val)
        (fun i => (primeUpTo_prime (w i)).one_le) hn hR (fun i => hmin i (w i) (hw i))
      have hwindow' := hwindow w hw hbw
      have hperiod : (characterTuplePeriod w : ℝ)/4 < X := by
        have hper' : (characterTuplePeriod w : ℝ) ≤ (characterTupleProduct w : ℝ)/R := by
          simpa only [characterTuplePeriod, characterTupleProduct, Nat.cast_prod] using hper
        have hmul := (le_div_iff₀ hR).mp (hper'.trans (div_le_div_of_nonneg_right hwindow'.2 hR.le))
        nlinarith
      have hphys := phased_character_tuple_bound (fun i => (w i).val)
        (fun i => primeUpTo_prime (w i)) χ a z
        (fun i => hχ i (w i) (hw i)) (fun i => hz i (w i) (hw i)) hX hperiod
      change ‖characterTuplePhysical χ a z X w‖ ≤
        C*(Real.sqrt (characterTupleProduct w : ℝ)/(characterTuplePeriod w : ℝ)) at hphys
      have hmasked : ‖(B w : ℂ)*characterTuplePhysical χ a z X w‖ ≤
          C*(Real.sqrt (characterTupleProduct w : ℝ)/(characterTuplePeriod w : ℝ)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB w).1]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hB w).2).trans hphys
      calc
        _ ≤ (N/(characterTupleProduct w : ℝ))*
            (C*(Real.sqrt (characterTupleProduct w : ℝ)/(characterTuplePeriod w : ℝ))) :=
          mul_le_mul (characterTuplePrior_mass_le E hE w) hmasked (norm_nonneg _)
            (div_nonneg hN (Nat.cast_nonneg _))
        _ ≤ (C*N/Real.sqrt M₀)/(characterTuplePeriod w : ℝ) :=
          reciprocal_sqrt_product_bound hM₀ hwindow'.1 hQ.le hC hN
        _ = _ := by dsimp [K]; ring
    · rw [ite_eq_right hw, characterTuplePrior_mass_eq_zero E hE w hw]
      simp
  apply (μ.norm_cmean_le _).trans
  change (∑ w, μ.mass w*‖if Function.Injective w then 0 else
    (B w : ℂ)*characterTuplePhysical χ a z X w‖) ≤ _
  calc
    _ ≤ ∑ w, K*(if ∀ i, w i ∈ E i then 1/(characterTuplePeriod w : ℝ) else 0) :=
      Finset.sum_le_sum (fun w _ => hpoint w)
    _ = K*(∑ w : Fin b → PrimeUpTo Q,
        if ∀ i, w i ∈ E i then 1/(characterTuplePeriod w : ℝ) else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (characterTuple_supported_reciprocal_sum_le E) hK

end Ostmann.Characters

end

end OAI
