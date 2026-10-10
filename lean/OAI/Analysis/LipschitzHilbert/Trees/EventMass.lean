import OAI.Analysis.LipschitzHilbert.Fourier.Projection

namespace OAI

/-!
# The quantile event has a positive deficit

Finite sums implement the event calculation in the proof of
`phase:quantile-gap`. The only geometric condition is the explicitly
proved fact that a resonant completion of the event lies below its
chosen central interval.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

def rectangularEvent (I K L : Finset ι) : Finset (Triple ι) := I ×ˢ (K ×ˢ L)

omit [Fintype ι] in
theorem independent_rectangular_event (x : ι → ℝ) (I K L : Finset ι) :
    (∑ q ∈ rectangularEvent I K L, independentMass x q) =
      (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ l ∈ L, x l) := by
  simp only [rectangularEvent, Finset.sum_product, independentMass]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem restricted_marginal_sum_le {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i j k : ι) (L : Finset ι) :
    (∑ l ∈ L, marginal frequency gap x (i, j, k, l)) ≤ x i * x j * x k := by
  calc
    _ ≤ ∑ l, marginal frequency gap x (i, j, k, l) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
        (fun _ _ _ => marginal_nonneg hx _)
    _ ≤ _ := sum_completions_le hgap hsep i j k _
      (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k))

/-- Forcing the missing coordinate into `J` bounds the projected event
by the independent mass of `I × K × J`. -/
theorem projected_rectangular_event_le {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (I K L J : Finset ι)
    (hcompletion : ∀ i ∈ I, ∀ k ∈ K, ∀ l ∈ L, ∀ j,
      Resonant frequency gap i j k l → j ∈ J) :
    (∑ q ∈ rectangularEvent I K L, projectedMass frequency gap x q) ≤
      (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ j ∈ J, x j) := by
  classical
  simp only [rectangularEvent, Finset.sum_product, projectedMass]
  calc
    _ ≤ ∑ i ∈ I, ∑ k ∈ K, ∑ j ∈ J, x i * x j * x k := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ j, if j ∈ J then x i * x j * x k else 0 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j ∈ J
          · simpa only [hj, ite_true] using restricted_marginal_sum_le hgap hsep x hx i j k L
          · simp only [hj, ite_false]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro l hl
            have hn : ¬ Resonant frequency gap i j k l :=
              fun hr => hj (hcompletion i hi k hk l hl j hr)
            simp [marginal, hn]
        _ = _ := by simp
    _ = _ := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- When `J ⊆ L`, the independent mass in `L \ J` is a definite event
deficit. This is the exact finite form of the manuscript's calculation. -/
theorem rectangular_event_deficit {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (I K L J : Finset ι) (hJL : J ⊆ L)
    (hcompletion : ∀ i ∈ I, ∀ k ∈ K, ∀ l ∈ L, ∀ j,
      Resonant frequency gap i j k l → j ∈ J) :
    (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ l ∈ L \ J, x l) ≤
      ∑ q ∈ rectangularEvent I K L,
        (independentMass x q - projectedMass frequency gap x q) := by
  have hp := projected_rectangular_event_le hgap hsep x hx I K L J hcompletion
  have hs : (∑ l ∈ L \ J, x l) = (∑ l ∈ L, x l) - (∑ j ∈ J, x j) :=
    eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hJL)
  rw [Finset.sum_sub_distrib, independent_rectangular_event, hs, mul_sub]
  exact sub_le_sub_left hp _

/-- The source's frequency-threshold event satisfies the preceding completion
condition. Strict inequality on `J` leaves both endpoints of `[e,h]` in `L \ J`. -/
theorem threshold_event_completion {frequency : ι → ℝ} {gap a b e h : ℝ}
    (hgap : 0 < gap) (hab : gap ≤ b - a) (heh : h - e ≤ (b - a) / 2) :
    ∀ i ∈ Finset.univ.filter (fun i => b ≤ frequency i),
      ∀ k ∈ Finset.univ.filter (fun k => frequency k ≤ a),
      ∀ l ∈ Finset.univ.filter (fun l => frequency l ≤ h), ∀ j,
        Resonant frequency gap i j k l →
          j ∈ Finset.univ.filter (fun j => frequency j < e) := by
  intro i hi k hk l hl j hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hk hl ⊢
  exact resonant_event_completion_lt hgap hab heh hr hi hk hl

/-- The exact quantitative constant obtained from two quarter-tail masses
and a half of the central mass. Quantile existence supplies these hypotheses. -/
theorem quantitative_gap_of_event_mass_bounds {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (I K L J : Finset ι) (hJL : J ⊆ L)
    (hcompletion : ∀ i ∈ I, ∀ k ∈ K, ∀ l ∈ L, ∀ j,
      Resonant frequency gap i j k l → j ∈ J)
    (hI : κ / 4 ≤ ∑ i ∈ I, x i) (hK : κ / 4 ≤ ∑ k ∈ K, x k)
    (hcentral : (1 - κ / 2) / 2 ≤ ∑ l ∈ L \ J, x l) :
    resonanceSum frequency gap x ≤ 1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096 := by
  have hI0 : 0 ≤ ∑ i ∈ I, x i := Finset.sum_nonneg fun i _ => hx i
  have hK0 : 0 ≤ ∑ k ∈ K, x k := Finset.sum_nonneg fun k _ => hx k
  have hIK : (κ / 4) * (κ / 4) ≤ (∑ i ∈ I, x i) * (∑ k ∈ K, x k) :=
    mul_le_mul hI hK (by linarith) hI0
  have hproduct : κ ^ 2 * (1 - κ / 2) / 32 ≤
      (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ l ∈ L \ J, x l) := by
    calc
      _ = (κ / 4) * (κ / 4) * ((1 - κ / 2) / 2) := by ring
      _ ≤ _ := mul_le_mul hIK hcentral (by linarith) (mul_nonneg hI0 hK0)
  have hdeficit := hproduct.trans
    (rectangular_event_deficit hgap hsep x hx I K L J hJL hcompletion)
  have hg : 0 ≤ κ ^ 2 * (1 - κ / 2) / 32 :=
    div_nonneg (mul_nonneg (sq_nonneg κ) (by linarith)) (by norm_num)
  calc
    resonanceSum frequency gap x ≤ 1 - (κ ^ 2 * (1 - κ / 2) / 32) ^ 2 / 4 :=
      resonanceSum_gap_of_event_deficit hgap hsep x hx hsum
        (rectangularEvent I K L) hg hdeficit
    _ = _ := by ring

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
