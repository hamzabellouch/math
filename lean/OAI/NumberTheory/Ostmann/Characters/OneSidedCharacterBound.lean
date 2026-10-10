import OAI.NumberTheory.Ostmann.Construction.OneSidedCauchy
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionCharacterCancellation

namespace OAI

/-! # The one-sided bound on an explicitly partitioned long-variable range -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The actual correlation weight on one interval/residue piece. Values
outside the piece are set to zero only to state finite variation on ℕ. -/
noncomputable def progressionCorrelationWeight {A I B : Type*} (N : I → ℕ)
    (e : A ≃ Σ i, Fin (N i)) (η : A → ℝ) (W : B → A → ℂ)
    (q r : B) (i : I) (j : ℕ) : ℂ :=
  if hj : j < N i then
    let x := e.symm ⟨i, ⟨j, hj⟩⟩
    (η x : ℂ) * (W q x * conj (W r x))
  else 0

theorem partitioned_character_correlation {A I : Type*} [Fintype A] [Fintype I]
    (N a M : I → ℕ) (e : A ≃ Σ i, Fin (N i)) (value : A → ℕ)
    (hvalue : ∀ i (j : Fin (N i)), value (e.symm ⟨i, j⟩) = a i + M i * j.val)
    (η : A → ℝ) (W₁ W₂ : A → ℂ)
    {q r : ℕ} [NeZero q] [NeZero r] (hqr : q.Coprime r)
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) (hχ : χ ≠ 1)
    (hM : ∀ i, (M i).Coprime (q * r)) (V : ℝ)
    (hvar : ∑ i, discreteVariation
      (progressionCorrelationWeight N e η (fun b : Bool => if b then W₁ else W₂) true false i)
      (N i) ≤ V) :
    ‖∑ x, (η x : ℂ) * ((χ (value x : ZMod q) * W₁ x) *
      conj (ψ (value x : ZMod r) * W₂ x))‖ ≤ V * (q * r) := by
  let w := progressionCorrelationWeight N e η (fun b : Bool => if b then W₁ else W₂) true false
  have he : (∑ x, (η x : ℂ) * ((χ (value x : ZMod q) * W₁ x) *
        conj (ψ (value x : ZMod r) * W₂ x))) =
      ∑ i, ∑ j ∈ Finset.range (N i), w i j *
        (χ ((a i + M i * j : ℕ) : ZMod q) * conj (ψ ((a i + M i * j : ℕ) : ZMod r))) := by
    rw [← e.symm.sum_comp (fun x => (η x : ℂ) * ((χ (value x : ZMod q) * W₁ x) *
      conj (ψ (value x : ZMod r) * W₂ x))), Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hp (j : Fin (N i)) :
        (η (e.symm ⟨i, j⟩) : ℂ) *
          ((χ (value (e.symm ⟨i, j⟩) : ZMod q) * W₁ (e.symm ⟨i, j⟩)) *
            conj (ψ (value (e.symm ⟨i, j⟩) : ZMod r) * W₂ (e.symm ⟨i, j⟩))) =
        w i j.val * (χ ((a i + M i * j.val : ℕ) : ZMod q) *
          conj (ψ ((a i + M i * j.val : ℕ) : ZMod r))) := by
      simp only [w, progressionCorrelationWeight, dite_eq_left j.isLt,
        ite_true, Bool.false_eq_true, ite_false, hvalue, map_mul]
      ring
    simp_rw [hp]
    exact Fin.sum_univ_eq_sum_range
      (fun j => w i j * (χ ((a i + M i * j : ℕ) : ZMod q) *
        conj (ψ ((a i + M i * j : ℕ) : ZMod r)))) (N i)
  rw [he]
  exact character_interval_pieces_bound hqr χ ψ hχ a M N hM w V hvar

/-- All off-diagonal correlations are derived from exact progression
cancellation. Irregular unary restrictions remain in U and V. -/
theorem one_sided_character_bound {A I : Type*} [Fintype A] [Fintype I]
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (N a M : I → ℕ) (e : A ≃ Σ i, Fin (N i)) (value : A → ℕ)
    (hvalue : ∀ i (j : Fin (N i)), value (e.symm ⟨i, j⟩) = a i + M i * j.val)
    (hM : ∀ i (q : Q), (M i).Coprime (q : ℕ))
    (μ η : A → ℝ) (ν : Q → ℝ) (U : A → ℂ) (V : Q → ℂ) (W : Q → A → ℂ)
    (C α H B Z : ℝ) (Bq : ℕ) (hC : 0 ≤ C) (hα : 0 ≤ α) (hH : 0 ≤ H) (hZ : 0 ≤ Z)
    (hμ : ∀ p, 0 ≤ μ p) (hmassμ : ∑ p, μ p ≤ 1)
    (hdom : ∀ p, μ p ≤ C * η p) (hη : ∀ p, 0 ≤ η p) (hmassη : ∑ p, η p ≤ H)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ p, ‖U p‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1)
    (hW : ∀ q p, ‖W q p‖ ≤ B) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (hvar : ∀ q r : Q, q ≠ r → ∑ i, discreteVariation
      (progressionCorrelationWeight N e η W q r i) (N i) ≤ Z) :
    ‖∑ p, (μ p : ℂ) * (U p * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q (value p : ZMod (q : ℕ)) * W q p))‖ ^ 2 ≤
      C * (α * (H * B ^ 2) + Z * (Bq : ℝ) ^ 2) := by
  let F : Q → A → ℂ := fun q p => χ q (value p : ZMod (q : ℕ)) * W q p
  have hF (q : Q) (p : A) : ‖F q p‖ ≤ B := by
    change ‖χ q (value p : ZMod (q : ℕ)) * W q p‖ ≤ B
    rw [norm_mul]
    exact (mul_le_mul ((χ q).norm_le_one _) (hW q p) (norm_nonneg _) (by norm_num)).trans_eq (one_mul B)
  apply one_sided_cauchy_of_offdiagonal μ η ν U V F C α H B (Z * (Bq : ℝ) ^ 2)
    hC hα hH (mul_nonneg hZ (sq_nonneg _)) hμ hmassμ hdom hη hmassη hν hmassν hatom hU hV hF
  intro q r hqr
  have : NeZero (q : ℕ) := ⟨(hprime q q.property).ne_zero⟩
  have : NeZero (r : ℕ) := ⟨(hprime r r.property).ne_zero⟩
  have hcop : (q : ℕ).Coprime (r : ℕ) :=
    (Nat.coprime_primes (hprime q q.property) (hprime r r.property)).mpr
      (fun he => hqr (Subtype.ext he))
  have hv : ∑ i, discreteVariation
      (progressionCorrelationWeight N e η (fun b : Bool => if b then W q else W r) true false i)
      (N i) ≤ Z := by
        have hw : progressionCorrelationWeight N e η
            (fun b : Bool => if b then W q else W r) true false =
            progressionCorrelationWeight N e η W q r := by
          funext i j
          unfold progressionCorrelationWeight
          split_ifs <;> rfl
        rw [hw]
        exact hvar q r hqr
  have hb := partitioned_character_correlation N a M e value hvalue η (W q) (W r) hcop
    (χ q) (χ r) (hnonprincipal q) (fun i => (hM i q).mul_right (hM i r)) Z hv
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hZ
  have hq : (q : ℝ) ≤ Bq := by exact_mod_cast hBq q
  have hr : (r : ℝ) ≤ Bq := by exact_mod_cast hBq r
  simpa only [pow_two] using mul_le_mul hq hr (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end Ostmann

end OAI
