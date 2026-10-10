import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPolynomialWeight

namespace OAI

/-! # Character cancellation for the actual smooth polynomial weight

The interval and variation hypotheses are constructed from the polynomial roots.
Only a bounded function of the root cell is retained for the regular supports.
Irregular unary prime restrictions are handled separately by Cauchy--Schwarz.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- One allowed residue progression. The factor 1/a is the long-variable
saving; summing over the residue classes gives the frequency-modulus loss. -/
theorem polynomial_weighted_character_progression {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (ha : 0 < a) (hM : M.Coprime (q * r))
    {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i x, x ∈ (F i).polynomial.derivative.roots → x ∈ S)
    (flag : (S → Ordering) → ℂ) (hflag : ∀ i, ‖flag i‖ ≤ 1) :
    ‖∑ j ∈ Finset.range N,
      flag (rootCellCode S ((a + M * j : ℕ) : ℝ)) *
      (Complex.ofReal (((a + M * j : ℕ) : ℝ)⁻¹) *
        smoothPolynomialWeight F ((a + M * j : ℕ) : ℝ)) *
      (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤
      (3 ^ S.card : ℕ) * (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r) := by
  let u : ℕ → ℝ := fun j => ((a + M * j : ℕ) : ℝ)
  have hu : Monotone u := by
    intro i j hij
    change ((a + M * i : ℕ) : ℝ) ≤ ((a + M * j : ℕ) : ℝ)
    exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left M hij) a
  obtain ⟨starts, K, e, he, hcode⟩ := exists_rootCell_partition S N u hu
  let b : (S → Ordering) → ℕ := fun i => a + M * starts i
  have hval (i : S → Ordering) (j : ℕ) : a + M * (starts i + j) = b i + M * j := by
    dsimp [b]
    ring
  have huval (i : S → Ordering) (j : ℕ) : u (starts i + j) = (b i : ℝ) + M * j := by
    change ((a + M * (starts i + j) : ℕ) : ℝ) = _
    rw [hval]
    push_cast
    rfl
  let w : (S → Ordering) → ℕ → ℂ := fun i j =>
    if K i = 0 then 0 else flag i *
      (Complex.ofReal (((b i : ℝ) + M * j)⁻¹) *
        smoothPolynomialWeight F ((b i : ℝ) + M * j))
  have hvar (i : S → Ordering) :
      discreteVariation (w i) (K i) ≤ 2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F := by
    by_cases hK : K i = 0
    · simp only [w, hK, ite_true, discreteVariation, norm_zero,
        zero_add]
      have hbudget := smoothPolynomialBudget_nonneg F
      positivity
    · have hKi : 0 < K i := Nat.pos_of_ne_zero hK
      have hc0 := hcode i ⟨0, hKi⟩
      have hc1 := hcode i ⟨K i - 1, by omega⟩
      have hc : rootCellCode S (b i : ℝ) =
          rootCellCode S ((b i : ℝ) + M * ((K i - 1 : ℕ) : ℝ)) := by
        have hc := hc0.trans hc1.symm
        simpa only [huval, Nat.cast_zero, mul_zero, add_zero] using hc
      have hba : (a : ℝ) ≤ b i := by
        change (a : ℝ) ≤ ((a + M * starts i : ℕ) : ℝ)
        exact_mod_cast Nat.le_add_right a (M * starts i)
      have hb : 0 < (b i : ℝ) := lt_of_lt_of_le (by exact_mod_cast ha) hba
      have hv := smoothPolynomial_reciprocal_variation F S hroots (b i) M hb
        (Nat.cast_nonneg M) (K i) hc
      have hvar0 := discreteVariation_nonneg
        (fun j => Complex.ofReal (((b i : ℝ) + M * j)⁻¹) *
          smoothPolynomialWeight F ((b i : ℝ) + M * j)) (K i)
      simp only [w, ite_eq_right hK]
      rw [discreteVariation_const_mul]
      calc
        _ ≤ 1 * (2 * (b i : ℝ)⁻¹ * smoothPolynomialBudget F) :=
          mul_le_mul (hflag i) hv hvar0 (by norm_num)
        _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (inv_anti₀ (by exact_mod_cast ha) hba) (by norm_num))
            (smoothPolynomialBudget_nonneg F)
  have hsum : (∑ j ∈ Finset.range N,
      flag (rootCellCode S (u j)) * (Complex.ofReal ((u j)⁻¹) * smoothPolynomialWeight F (u j)) *
        (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))) =
      ∑ i : S → Ordering, ∑ j ∈ Finset.range (K i), w i j *
        (χ ((b i + M * j : ℕ) : ZMod q) * conj (ψ ((b i + M * j : ℕ) : ZMod r))) := by
    let f : ℕ → ℂ := fun j =>
      flag (rootCellCode S (u j)) * (Complex.ofReal ((u j)⁻¹) * smoothPolynomialWeight F (u j)) *
        (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))
    change (∑ j ∈ Finset.range N, f j) = _
    rw [← Fin.sum_univ_eq_sum_range f N,
      ← e.symm.sum_comp (fun j : Fin N => f j.val), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hp (j : Fin (K i)) : f (e.symm ⟨i, j⟩).val = w i j.val *
        (χ ((b i + M * j.val : ℕ) : ZMod q) * conj (ψ ((b i + M * j.val : ℕ) : ZMod r))) := by
      have hK : K i ≠ 0 := by have hj := j.isLt; omega
      rw [he i j]
      dsimp only [f]
      rw [hcode i j, huval, hval]
      simp only [w, ite_eq_right hK]
    simp_rw [hp]
    exact Fin.sum_univ_eq_sum_range (fun j => w i j *
      (χ ((b i + M * j : ℕ) : ZMod q) * conj (ψ ((b i + M * j : ℕ) : ZMod r)))) (K i)
  change ‖∑ j ∈ Finset.range N,
      flag (rootCellCode S (u j)) * (Complex.ofReal ((u j)⁻¹) * smoothPolynomialWeight F (u j)) *
        (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤ _
  rw [hsum]
  apply character_interval_pieces_bound hqr χ ψ hχ b (fun _ => M) K (fun _ => hM) w _
  calc
    _ ≤ ∑ _i : S → Ordering, 2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F :=
      Finset.sum_le_sum (fun i _ => hvar i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, rootCellCode_card]

end Ostmann

end OAI
