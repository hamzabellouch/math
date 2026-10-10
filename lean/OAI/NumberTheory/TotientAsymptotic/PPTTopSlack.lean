import OAI.NumberTheory.TotientAsymptotic.PPTSurvivingSlack

namespace OAI

/-!
The comparison exponent for the original large head.  Here the remaining
surviving coordinates come from the entire geometric tail, so the top
simplex budget replaces the row at a later prime.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma ppt_top_embedding_index {k n : ℕ} (ι : Fin k ↪o Fin n)
    (r : Fin k) : r.val ≤ (ι r).val := by
  have hall : ∀ j (hj : j < k), j ≤ (ι ⟨j,hj⟩).val := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hj' : j < k := by omega
      have hp := ih hj'
      have hs := ι.strictMono
        (show (⟨j,hj'⟩ : Fin k) < ⟨j+1,hj⟩ from Nat.lt_succ_self j)
      change (ι ⟨j,hj'⟩).val < (ι ⟨j+1,hj⟩).val at hs
      omega
  exact hall r.val r.isLt

private lemma ppt_sum_shifted_fin_indices (k : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 k, f r) = ∑ r : Fin k, f (r.val+1) := by
  symm
  apply Finset.sum_bij (fun r _ => r.val+1)
  · intro r hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro r hr s hs hrs
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjk : j-1 < k := by omega
    refine ⟨⟨j-1,hjk⟩, Finset.mem_univ _, ?_⟩
    dsimp only
    omega
  · intro r hr
    rfl

/-- Deletion of arbitrary ordered tail coordinates does not increase the
top simplex sum, including when no tail coordinate survives. -/
lemma ppt_surviving_top_sum_le {k n : ℕ} (ι : Fin k ↪o Fin n)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) :
    (∑ r : Fin k, a (r.val+1)*v (ι r)) ≤
      ∑ j : Fin n, a (j.val+1)*v j := by
  classical
  calc
    _ ≤ ∑ r : Fin k, a ((ι r).val+1)*v (ι r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (a_monotone_positive (by omega)
          (Nat.add_le_add_right (ppt_top_embedding_index ι r) 1)) (hv (ι r))
    _ = ∑ j ∈ Finset.univ.image ι, a (j.val+1)*v j := by
      rw [Finset.sum_image]
      exact fun r _ s _ hrs => ι.injective hrs
    _ ≤ ∑ j : Fin n, a (j.val+1)*v j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j hj hj'
      exact mul_nonneg (a_pos (by omega)).le (hv j)

lemma ppt_gridded_surviving_top {k n : ℕ} (ι : Fin k ↪o Fin n)
    (v : Fin n → ℝ) (ν : ℕ → ℝ) {T σ e : ℝ}
    (hT : 0 < T) (hv : ∀ j, 0 ≤ v j)
    (htop : (∑ j : Fin n, a (j.val+1)*v j) ≤ (1-σ)*T)
    (hgrid : ∀ r : Fin k, ν (r.val+1) ≤ v (ι r)/T+e) :
    (∑ r ∈ Finset.Icc 1 k, a r*ν r) ≤
      1-σ+e*(∑ r ∈ Finset.Icc 1 k, a r) := by
  rw [ppt_sum_shifted_fin_indices, ppt_sum_shifted_fin_indices]
  have hmass := (ppt_surviving_top_sum_le ι v hv).trans htop
  calc
    _ ≤ ∑ r : Fin k, a (r.val+1)*(v (ι r)/T+e) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hgrid r) (a_pos (by omega)).le
    _ = (∑ r : Fin k, a (r.val+1)*v (ι r))/T+
        e*(∑ r : Fin k, a (r.val+1)) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ _ := by
      have hh := (div_le_iff₀ hT).mpr hmass
      linarith only [hh]

/-- The large-head branch uses the original top budget, with the exact
same inverse-cube loss after the head normalization error. -/
theorem ppt_relaxed_surviving_top_slack {m n k : ℕ} {budget c T headError e : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n budget c)
    (ι : Fin k ↪o Fin n) (ν : ℕ → ℝ)
    (hT : 0 < T) (hhead : budget ≤ T+headError)
    (herr : 4*headError ≤ (rowContractionError m/2)*T)
    (hgrid : ∀ r : Fin k, ν (r.val+1) ≤ v (ι r)/T+e) :
    (∑ r ∈ Finset.Icc 1 k, a r*ν r) ≤
      1-rowContractionError m/8+e*(∑ r ∈ Finset.Icc 1 k, a r) := by
  have hω := ppt_half_row_error_bounds m
  have htop := ppt_row_budget_after_head_error hT hω.1 hω.2
    hv.1.2.2.2 hhead herr
  apply ppt_gridded_surviving_top ι v ν hT hv.1.1 _ hgrid
  convert htop using 1
  ring

/-- This is the exact published exponent for a surviving head outside the
tail vector; `b = 1` is allowed and has an empty weighted sum. -/
theorem ppt_relaxed_surviving_top_exponent {m n b : ℕ}
    {budget c T headError e w S z : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ relaxedGeometricFamily m n budget c)
    (ι : Fin (b-1) ↪o Fin n) (ν μ : ℕ → ℝ)
    (hT : 0 < T) (hBz : B z ≠ 0) (hhead : budget ≤ T+headError)
    (herr : 4*headError ≤ (rowContractionError m/2)*T)
    (hgrid : ∀ r : Fin (b-1), ν (r.val+1) ≤ v (ι r)/T+e)
    (hwidth : ∀ r ∈ Finset.Icc 1 (b-1), ν r-μ r ≤ w)
    (herror : e*(∑ r ∈ Finset.Icc 1 (b-1), a r)+2*(b-1 : ℕ)*w+
      Real.sqrt (B S/B z)*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
        rowContractionError m/16) :
    -2+(∑ r ∈ Finset.Icc 1 (b-1),
      a r*(B (comparisonCutoffs z ν r)/B z))+
      comparisonError b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ) ≤
        -1-rowContractionError m/16 := by
  have hslack := ppt_relaxed_surviving_top_slack hv ι ν hT hhead herr hgrid
  have hh := comparisonExponent_le b z S (comparisonCutoffs z ν) (comparisonCutoffs z μ)
    (rowContractionError m/8) e w
    (by simpa only [comparisonCutoffs_doubleLog hBz] using hslack)
    (by simpa only [comparisonCutoffs_doubleLog hBz] using hwidth)
    (by
      convert herror using 1
      ring)
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
