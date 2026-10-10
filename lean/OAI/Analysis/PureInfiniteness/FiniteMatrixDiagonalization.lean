import OAI.Analysis.PureInfiniteness.BoundedPairDiagonalization
import OAI.Analysis.PureInfiniteness.OneStepContraction

namespace OAI

/-! Finite diagonal coefficient updates for KR02 Lemma 5.7.
Multipliers at untouched coordinates are handled in the unitization; all
actual coefficients and witnesses stay in the original nonunital algebra. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A I : Type*} [NonUnitalCStarAlgebra A] [DecidableEq I]

def coefficientMatrix (M : I → I → A) (d : I → A) (i j : I) : A :=
  star (d i) * M i j * d j

def updateTwoCoefficients (d : I → A) (i j : I) (s t : A) (k : I) : A :=
  if k = i then d k * s else if k = j then d k * t else d k

def updateTwoMultiplier (i j : I) (s t : A) (k : I) : Unitization ℂ A :=
  if k = i then (s : Unitization ℂ A) else
    if k = j then (t : Unitization ℂ A) else 1

lemma updateTwoCoefficients_inr (d : I → A) (i j : I) (s t : A) (k : I) :
    (↑(updateTwoCoefficients d i j s t k) : Unitization ℂ A) =
      (d k : Unitization ℂ A) * updateTwoMultiplier i j s t k := by
  unfold updateTwoCoefficients updateTwoMultiplier
  split_ifs <;> simp only [Unitization.inr_mul, mul_one]

lemma norm_updateTwoMultiplier_le (i j : I) (s t : A) (C : ℝ) (hC : 1 ≤ C)
    (hs : ‖s‖ ≤ C) (ht : ‖t‖ ≤ C) (k : I) :
    ‖updateTwoMultiplier i j s t k‖ ≤ C := by
  unfold updateTwoMultiplier
  split_ifs
  · simpa only [Unitization.norm_inr] using hs
  · simpa only [Unitization.norm_inr] using ht
  · simpa only [norm_one] using hC

lemma coefficientMatrix_update_inr (M : I → I → A) (d : I → A)
    (i j : I) (s t : A) (p q : I) :
    (↑(coefficientMatrix M (updateTwoCoefficients d i j s t) p q) : Unitization ℂ A) =
      star (updateTwoMultiplier i j s t p) *
        (↑(coefficientMatrix M d p q) : Unitization ℂ A) * updateTwoMultiplier i j s t q := by
  simp only [coefficientMatrix, Unitization.inr_mul, Unitization.inr_star,
    updateTwoCoefficients_inr, star_mul, mul_assoc]

lemma norm_coefficientMatrix_update_le (M : I → I → A) (d : I → A)
    (i j : I) (s t : A) (C : ℝ) (hC : 1 ≤ C) (hs : ‖s‖ ≤ C) (ht : ‖t‖ ≤ C)
    (p q : I) :
    ‖coefficientMatrix M (updateTwoCoefficients d i j s t) p q‖ ≤
      C ^ 2 * ‖coefficientMatrix M d p q‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ)
    (a := coefficientMatrix M (updateTwoCoefficients d i j s t) p q)]
  rw [coefficientMatrix_update_inr]
  calc
    _ ≤ ‖star (updateTwoMultiplier i j s t p)‖ *
        ‖(↑(coefficientMatrix M d p q) : Unitization ℂ A)‖ * ‖updateTwoMultiplier i j s t q‖ :=
      norm_mul₃_le
    _ ≤ C * ‖coefficientMatrix M d p q‖ * C := by
      rw [norm_star, Unitization.norm_inr]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (norm_updateTwoMultiplier_le i j s t C hC hs ht p)
          (norm_nonneg _))
        (norm_updateTwoMultiplier_le i j s t C hC hs ht q)
        (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))
    _ = _ := by ring

lemma norm_updateTwoCoefficients_le (d : I → A) (i j : I) (s t : A)
    (C D : ℝ) (hC : 1 ≤ C) (hs : ‖s‖ ≤ C) (ht : ‖t‖ ≤ C)
    (hd : ∀ k, ‖d k‖ ≤ D) (k : I) :
    ‖updateTwoCoefficients d i j s t k‖ ≤ D * C := by
  rw [← Unitization.norm_inr (𝕜 := ℂ) (a := updateTwoCoefficients d i j s t k),
    updateTwoCoefficients_inr]
  calc
    _ ≤ ‖(d k : Unitization ℂ A)‖ * ‖updateTwoMultiplier i j s t k‖ := norm_mul_le _ _
    _ ≤ D * C := by
      rw [Unitization.norm_inr]
      exact mul_le_mul (hd k) (norm_updateTwoMultiplier_le i j s t C hC hs ht k)
        (norm_nonneg _) ((norm_nonneg (d k)).trans (hd k))

lemma coefficientMatrix_update_first (M : I → I → A) (d : I → A)
    (i j : I) (s t : A) :
    coefficientMatrix M (updateTwoCoefficients d i j s t) i i =
      star s * coefficientMatrix M d i i * s := by
  simp only [coefficientMatrix, updateTwoCoefficients, ite_true, star_mul, mul_assoc]

lemma coefficientMatrix_update_second (M : I → I → A) (d : I → A)
    (i j : I) (hij : i ≠ j) (s t : A) :
    coefficientMatrix M (updateTwoCoefficients d i j s t) j j =
      star t * coefficientMatrix M d j j * t := by
  simp only [coefficientMatrix, updateTwoCoefficients, Ne.symm hij, ite_false,
    ite_true, star_mul, mul_assoc]

lemma coefficientMatrix_update_selected (M : I → I → A) (d : I → A)
    (i j : I) (hij : i ≠ j) (s t : A) :
    coefficientMatrix M (updateTwoCoefficients d i j s t) i j =
      star s * coefficientMatrix M d i j * t := by
  simp only [coefficientMatrix, updateTwoCoefficients, Ne.symm hij, ite_false,
    ite_true, star_mul, mul_assoc]

lemma coefficientMatrix_update_other (M : I → I → A) (d : I → A)
    (i j : I) (s t : A) (k : I) (hi : k ≠ i) (hj : k ≠ j) :
    coefficientMatrix M (updateTwoCoefficients d i j s t) k k = coefficientMatrix M d k k := by
  simp only [coefficientMatrix, updateTwoCoefficients, hi, hj, ite_false]

section Construction

local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- Finite diagonalization with an implementer bound independent of the
off-diagonal tolerance. Only the positive diagonal entries enter the bound. -/
theorem finite_matrix_diagonalization_uniform (hP : MainGap.PropertyP A)
    {n : ℕ} (M₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M : Fin n → Fin n → A,
      (∀ i, 0 ≤ M i i) → (∀ i, ‖M i i‖ ≤ M₀) →
      ∀ ζ : ℝ, 0 < ζ → ∃ d : Fin n → A,
      (∀ i, ‖d i‖ ≤ C) ∧ (∀ i, ‖coefficientMatrix M d i i - M i i‖ < η) ∧
      ∀ i j, i ≠ j → ‖coefficientMatrix M d i j‖ < ζ := by
  classical
  let P := {p : Fin n × Fin n // p.1 ≠ p.2}
  let N := Fintype.card P
  let e : Fin N ≃ P := (Fintype.equivFin P).symm
  let L : ℝ := max 1 M₀ + η
  let τ : ℝ := η / (2 * ((N : ℝ) + 1))
  have hτ : 0 < τ := div_pos hη (by positivity)
  have hbudget (k : ℕ) (hk : k ≤ N) : η / 2 + (k : ℝ) * τ < η := by
    have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have he : τ * (2 * ((N : ℝ) + 1)) = η := div_mul_cancel₀ η (by positivity)
    nlinarith
  obtain ⟨K, hK, hpair⟩ := uniform_bounded_pair_diagonalization hP L τ hτ
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨K ^ N, one_le_pow₀ hK, ?_⟩
  intro M hpos hM ζ hζ
  let κ := ζ / (2 * K ^ (2 * N))
  have hκ : 0 < κ := div_pos hζ (by positivity)
  have hfinal : κ * K ^ (2 * N) = ζ / 2 := by
    dsimp only [κ]
    field_simp
  have hsteps : ∀ k : ℕ, k ≤ N → ∃ d : Fin n → A,
      (∀ i, ‖d i‖ ≤ K ^ k) ∧
      (∀ i, ‖coefficientMatrix M d i i - M i i‖ < η / 2 + (k : ℝ) * τ) ∧
      ∀ l : Fin N, l.val < k →
        ‖coefficientMatrix M d (e l).val.1 (e l).val.2‖ < κ * K ^ (2 * k) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨f, hf, hfn, happ⟩ := exists_positive_contraction_sandwich_approximation
        (Finset.univ.image (fun i : Fin n => M i i)) (η / 2) (by positivity)
      refine ⟨fun _ => f, ?_, ?_, ?_⟩
      · intro _
        simpa only [pow_zero] using hfn
      · intro i
        simpa only [coefficientMatrix, hf.isSelfAdjoint.star_eq,
          Nat.cast_zero, zero_mul, add_zero] using
          happ (M i i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · intro l hl
        omega
    | succ k ih =>
      intro hk
      obtain ⟨d, hdn, hdiag, hoff⟩ := ih (by omega)
      let l : Fin N := ⟨k, by omega⟩
      let i := (e l).val.1
      let j := (e l).val.2
      have hij : i ≠ j := (e l).property
      have hnorm (p : Fin n) : ‖coefficientMatrix M d p p‖ ≤ L := by
        have h1 := hdiag p
        have h2 := hbudget k (by omega)
        have h3 := (hM p).trans (le_max_right (1 : ℝ) M₀)
        have h4 : ‖coefficientMatrix M d p p‖ ≤
            ‖coefficientMatrix M d p p - M p p‖ + ‖M p p‖ := by
          calc
            _ = ‖(coefficientMatrix M d p p - M p p) + M p p‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        dsimp only [L]
        linarith
      obtain ⟨s, t, hs, ht, hsi, htj, hst⟩ := hpair
        (coefficientMatrix M d i i) (coefficientMatrix M d j j)
        (star_left_conjugate_nonneg (hpos i) (d i))
        (star_left_conjugate_nonneg (hpos j) (d j))
        (hnorm i) (hnorm j) (coefficientMatrix M d i j) κ hκ
      let d' := updateTwoCoefficients d i j s t
      refine ⟨d', ?_, ?_, ?_⟩
      · intro p
        simpa only [pow_succ] using
          norm_updateTwoCoefficients_le d i j s t K (K ^ k) hK hs ht hdn p
      · intro p
        have hchange : ‖coefficientMatrix M d' p p - coefficientMatrix M d p p‖ < τ := by
          by_cases hpi : p = i
          · subst p
            simpa only [d', coefficientMatrix_update_first] using hsi
          · by_cases hpj : p = j
            · subst p
              simpa only [d', coefficientMatrix_update_second M d i j hij] using htj
            · rw [show coefficientMatrix M d' p p = coefficientMatrix M d p p from
                coefficientMatrix_update_other M d i j s t p hpi hpj, sub_self, norm_zero]
              exact hτ
        calc
          _ ≤ ‖coefficientMatrix M d' p p - coefficientMatrix M d p p‖ +
              ‖coefficientMatrix M d p p - M p p‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < τ + (η / 2 + (k : ℝ) * τ) := add_lt_add hchange (hdiag p)
          _ = η / 2 + ((k + 1 : ℕ) : ℝ) * τ := by push_cast; ring
      · intro m hm
        by_cases hmk : m.val = k
        · have hml : m = l := Fin.ext hmk
          subst m
          have hbound : κ ≤ κ * K ^ (2 * (k + 1)) := by
            have hp := one_le_pow₀ (n := 2 * (k + 1)) hK
            nlinarith
          have hnew : ‖coefficientMatrix M d' i j‖ < κ := by
            simpa only [d', coefficientMatrix_update_selected M d i j hij] using hst
          exact hnew.trans_le hbound
        · have hmk' : m.val < k := by omega
          calc
            _ ≤ K ^ 2 * ‖coefficientMatrix M d (e m).val.1 (e m).val.2‖ :=
              norm_coefficientMatrix_update_le M d i j s t K hK hs ht _ _
            _ < K ^ 2 * (κ * K ^ (2 * k)) :=
              mul_lt_mul_of_pos_left (hoff m hmk') (by positivity)
            _ = κ * K ^ (2 * (k + 1)) := by
              rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
              ring
  obtain ⟨d, hdn, hdiag, hoff⟩ := hsteps N le_rfl
  refine ⟨d, hdn, fun i => (hdiag i).trans (hbudget N le_rfl), ?_⟩
  intro i j hij
  let l : Fin N := e.symm ⟨(i, j), hij⟩
  have h := hoff l l.isLt
  have he : (e l).val = (i, j) := congrArg Subtype.val (e.apply_symm_apply ⟨(i, j), hij⟩)
  rw [he, hfinal] at h
  exact h.trans (by linarith)

end Construction

end WeakPureInfiniteness

end

end OAI
