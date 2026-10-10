import OAI.NumberTheory.Ostmann.Construction.WeightedPrimeSelection
import OAI.NumberTheory.Ostmann.Construction.LargeCellTargets

namespace OAI

/-! # Selecting many heavy cells with positive mean -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def positiveHeavyCells (I : Finset ℕ) (w score : ℕ → ℝ) (δ θ : ℝ) : Finset ℕ :=
  I.filter (fun h => δ / 2 ≤ score h ∧ θ ≤ w h)

/-- Removing low-mass cells from a positively biased shell retains a fixed
amount of mass. -/
theorem positiveHeavyCells_mass (I : Finset ℕ) (w score : ℕ → ℝ) (δ θ : ℝ)
    (hw : ∀ h ∈ I, 0 ≤ w h) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hscore : ∀ h ∈ I, score h ≤ 1)
    (hbias : δ * (∑ h ∈ I, w h) ≤ ∑ h ∈ I, w h * score h)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ h ∈ I, w h) :
    (δ / 4) * (∑ h ∈ I, w h) ≤ ∑ h ∈ positiveHeavyCells I w score δ θ, w h := by
  let S := I.filter (fun h => δ / 2 ≤ score h)
  have hS : (δ / 2) * (∑ h ∈ I, w h) ≤ ∑ h ∈ S, w h :=
    weighted_bias_superlevel I w score δ hw hδ hscore hbias
  have hbad : (∑ h ∈ S.filter (fun h => ¬θ ≤ w h), w h) ≤ I.card * θ := by
    calc
      _ ≤ ∑ _h ∈ S.filter (fun h => ¬θ ≤ w h), θ := by
        apply Finset.sum_le_sum
        intro h hh
        exact (lt_of_not_ge (Finset.mem_filter.mp hh).2).le
      _ = ((S.filter (fun h => ¬θ ≤ w h)).card : ℝ) * θ := by simp
      _ ≤ I.card * θ := by
        gcongr
        exact fun h hh => (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  have heq : S.filter (fun h => θ ≤ w h) = positiveHeavyCells I w score δ θ := by
    ext h
    simp only [S, positiveHeavyCells, Finset.mem_filter]
    tauto
  have hh := weighted_good_mass S w (fun h => θ ≤ w h)
    ((δ / 2) * ∑ h ∈ I, w h) (I.card * θ) hS hbad
  rw [heq] at hh
  linarith

/-- A cellwise upper mass bound converts retained mass into a lower bound
on the number of usable cell indices. -/
theorem positiveHeavyCells_card (I : Finset ℕ) (w score : ℕ → ℝ) (δ θ M : ℝ)
    (hw : ∀ h ∈ I, 0 ≤ w h) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hscore : ∀ h ∈ I, score h ≤ 1)
    (hbias : δ * (∑ h ∈ I, w h) ≤ ∑ h ∈ I, w h * score h)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ h ∈ I, w h)
    (hcap : ∀ h ∈ I, w h ≤ M) :
    (δ / 4) * (∑ h ∈ I, w h) ≤
      (positiveHeavyCells I w score δ θ).card * M := by
  apply (positiveHeavyCells_mass I w score δ θ hw hδ hθ hscore hbias hthin).trans
  calc
    _ ≤ ∑ _h ∈ positiveHeavyCells I w score δ θ, M := by
      apply Finset.sum_le_sum
      intro h hh
      exact hcap h (Finset.mem_filter.mp hh).1
    _ = _ := by simp

/-- An arbitrary dense set of cell indices has the required target words;
its minimum and maximum need not be chosen in advance. -/
theorem dense_index_target (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Finset ℕ) (B : ℕ),
      (∀ x ∈ I, x ≤ B) → δ * B + 2 ≤ I.card → ∀ T : ℝ,
      C * B ≤ T → ∃ (n : ℕ) (w : List ℕ),
      w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧ |(w.sum : ℝ) - T| < δ⁻¹ ∧
      (n : ℝ) * B ≤ 2 * T / δ ∧ T < (n + 1 : ℕ) * B := by
  obtain ⟨C, hC, htarget⟩ := dense_cell_large_target δ hδ
  refine ⟨C, hC, ?_⟩
  intro I B hbound hdensity T hT
  have hcard : 2 ≤ I.card := by
    have hnon : (0 : ℝ) ≤ δ * B := mul_nonneg hδ.le (Nat.cast_nonneg _)
    have : (2 : ℝ) ≤ I.card := by linarith
    exact_mod_cast this
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  let a := I.min' hne
  let b := I.max' hne
  have ha : a ∈ I := Finset.min'_mem _ _
  have hb : b ∈ I := Finset.max'_mem _ _
  have hminmax : ∀ x ∈ I, a ≤ x ∧ x ≤ b := fun x hx =>
    ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  have hab : a < b := by
    have hab' : a ≤ b := (hminmax a ha).2
    by_contra! h
    have heq : a = b := le_antisymm hab' h
    have hsub : I ⊆ {a} := by
      intro x hx
      have hh := hminmax x hx
      simp only [Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hbB : b ≤ B := hbound b hb
  have hd : δ * b + 2 ≤ I.card := by
    have hh : (b : ℝ) ≤ B := by exact_mod_cast hbB
    nlinarith
  have hc : I.card ≤ b + 1 := by
    have hh := Finset.card_le_card (show I ⊆ Finset.range (b + 1) from
      fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (hminmax x hx).2))
    simpa only [Finset.card_range] using hh
  have hδB : δ * B ≤ b := by
    have hh : (I.card : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast hc
    linarith
  obtain ⟨n, w, hwlen, hwmem, hwerr, hn, hn'⟩ := htarget I a b hab ha hb hminmax hd T
    ((mul_le_mul_of_nonneg_left (by exact_mod_cast hbB) hC.le).trans hT)
  refine ⟨n, w, hwlen, hwmem, hwerr, ?_, ?_⟩
  · apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hδB (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  · exact hn'.trans_le (mul_le_mul_of_nonneg_left (by exact_mod_cast hbB) (by positivity))

end Ostmann

end OAI
