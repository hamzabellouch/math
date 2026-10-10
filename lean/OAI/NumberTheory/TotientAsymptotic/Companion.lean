import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-! The zero alternative for weighted totient counts when no arithmetic seed exists. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma fk_nonneg (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ fk k r := by
  unfold fk
  apply sub_nonneg.mpr
  exact min_le_min_left 1 (div_le_div_of_nonneg_right (by norm_num) hr)

lemma fk_zero_of_le (k : ℕ) {r : ℝ} (hr : 0 < r) (hk : r ≤ k) : fk k r = 0 := by
  unfold fk
  have h₁ : 1 ≤ (k : ℝ) / r := (le_div_iff₀ hr).mpr (by simpa using hk)
  have h₂ : 1 ≤ (k+1 : ℝ) / r := (le_div_iff₀ hr).mpr (by linarith)
  rw [min_eq_left h₁, min_eq_left h₂, sub_self]

lemma ell_le_mul_of_no_seed (k : ℕ)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) {d : ℕ} (hd : IsTotient d) :
    ell d ≤ k*d := by
  by_contra h
  exact hno ⟨d, hd, Nat.lt_of_not_ge h⟩

lemma fk_ell_zero_of_no_seed (k : ℕ)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) {d : ℕ} (hd : IsTotient d) :
    fk k ((ell d : ℝ) / d) = 0 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (isTotient_pos hd)
  apply fk_zero_of_le k (lt_of_lt_of_le zero_lt_one (one_le_ell_ratio hd))
  apply (div_le_iff₀ hdpos).mpr
  exact_mod_cast ell_le_mul_of_no_seed k hno hd

lemma N_zero_of_no_seed (k : ℕ)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) {x : ℝ} (hx : 0 < x) :
    N k x = 0 := by
  classical
  unfold N
  have hempty : (Finset.Icc 1 ⌊x⌋₊).filter (fun v =>
      IsTotient v ∧ (k : ℝ) * x < ell v ∧ (ell v : ℝ) ≤ (k+1 : ℝ) * x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro v hv ⟨hvt, hvx, _⟩
    have hvle : (v : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hv).2).trans (Nat.floor_le hx.le)
    have hel : (ell v : ℝ) ≤ (k : ℝ) * v := by
      exact_mod_cast ell_le_mul_of_no_seed k hno hvt
    have hmul := mul_le_mul_of_nonneg_left hvle (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    exact (not_lt_of_ge (hel.trans hmul)) hvx
  rw [hempty]
  simp

lemma AH_zero_of_zero_weights (H : ℕ) (f : ℝ → ℝ) (s : ℝ)
    (hf : ∀ d : ℕ, IsTotient d → f ((ell d : ℝ) / d) = 0) : AH H f s = 0 := by
  classical
  unfold AH
  have hz : (∑ᶠ d : ℕ, if IsTotient d then
      f ((ell d : ℝ) / d) / d *
        ∑ᶠ T : Finset (TailDatum H),
          if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
            (-1 : ℝ)^(T.card-1) * Real.exp (-(gamma / alpha s) *
              ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
          else 0
      else 0) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd : IsTotient d
    · simp only [ite_eq_left hd, hf d hd, zero_div, zero_mul]
    · simp only [ite_eq_right hd]
  rw [hz, mul_zero]

lemma AH_fk_zero_of_no_seed (k : ℕ)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) (H : ℕ) (s : ℝ) :
    AH H (fk k) s = 0 :=
  AH_zero_of_zero_weights H (fk k) s (fun _ hd => fk_ell_zero_of_no_seed k hno hd)

lemma A_fk_zero_of_no_seed (k : ℕ)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) (s : ℝ) : A (fk k) s = 0 := by
  have ht : Tendsto (fun H : ℕ => AH H (fk k) s) atTop (nhds 0) := by
    simpa only [AH_fk_zero_of_no_seed k hno] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  exact ht.limUnder_eq

theorem companion_zero_case (k : ℕ) (_hk : 0 < k)
    (hno : ¬ ∃ d : ℕ, IsTotient d ∧ k*d < ell d) :
    (∀ x : ℝ, 0 < x → N k x = 0) ∧
    (∀ s ∈ Set.Ico (0 : ℝ) 1, A (fk k) s = 0) := by
  exact ⟨fun _ hx => N_zero_of_no_seed k hno hx,
    fun s _ => A_fk_zero_of_no_seed k hno s⟩

end TotientAsymptotic

end

end OAI
