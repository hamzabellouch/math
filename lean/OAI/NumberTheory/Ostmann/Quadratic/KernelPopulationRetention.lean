import OAI.NumberTheory.Ostmann.QuadraticCenter.LargeKernelPopulationDecay
import OAI.NumberTheory.Ostmann.QuadraticCenter.PopulatedKernelSelection
import OAI.NumberTheory.Ostmann.Quadratic.KernelPrimeCutoffs

namespace OAI

/-! # Quantitative retention of small, populated kernel fibers -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_small_kernel_fibers_decay (η ε a : ℝ)
    (hη : 0 < η) (hεη : ε ≤ η / 100) (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℤ) (f : ℤ → ℤ),
      ((S.image f).card : ℝ) ≤ Real.exp (3 * ε * L) →
      ((S.filter fun x => (S.filter fun y => f y = f x).card <
        kernelSplitCutoff η L).card : ℝ) ≤ a * Real.exp (L / 2) / L ^ 6 := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 6 hη).const_mul_left (1 / a)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL S f hcount
  have hLp : 0 < L := by linarith
  have hQ : (kernelSplitCutoff η L : ℝ) ≤ Real.exp ((1 / 2 - 5 * η) * L) :=
    Nat.floor_le (Real.exp_nonneg _)
  have he : Real.exp (3 * ε * L) * Real.exp ((1 / 2 - 5 * η) * L) ≤
      Real.exp ((1 / 2 - η) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ η / 100 - ε by linarith) hLp.le]
  have hp' : L ^ 6 / a ≤ Real.exp (η * L) := by
    simpa only [Real.norm_eq_abs, one_div_mul_eq_div, abs_of_nonneg (by positivity : 0 ≤ L ^ 6 / a),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hdecay : Real.exp ((1 / 2 - η) * L) ≤ a * Real.exp (L / 2) / L ^ 6 := by
    apply (le_div_iff₀ (pow_pos hLp 6)).mpr
    have hh : L ^ 6 ≤ a * Real.exp (η * L)  := by
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hp'
    have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg ((1 / 2 - η) * L))
    have hexp : Real.exp ((1 / 2 - η) * L) * Real.exp (η * L) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ ≤ Real.exp ((1 / 2 - η) * L) * (a * Real.exp (η * L)) := hmul
      _ = _ := by rw [mul_left_comm, hexp]
  calc
    _ ≤ (S.image f).card * (kernelSplitCutoff η L : ℝ) := by
      exact_mod_cast small_kernel_fibers_card S f (kernelSplitCutoff η L)
    _ ≤ Real.exp (3 * ε * L) * Real.exp ((1 / 2 - 5 * η) * L) :=
      mul_le_mul hcount hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ ≤ _ := he.trans hdecay

/-- At least half the original population remains in entire fibers whose
kernels are small and whose individual sizes reach the split-prime cutoff. -/
theorem eventual_populated_kernel_retention (η ε a : ℝ)
    (hη : 0 < η) (hηU : η ≤ 1 / 1000) (hε : 0 ≤ ε) (hεη : ε ≤ η / 100)
    (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℤ) (f : ℤ → ℤ) (root : ℤ → ℕ)
      (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
      ((S.image f).card : ℝ) ≤ Real.exp (3 * ε * L) →
      (∀ x ∈ S, f x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      a * Real.exp (L / 2) / L ^ 6 ≤ S.card →
      (a / 2) * Real.exp (L / 2) / L ^ 6 ≤
        (populatedKernelPoints S f (fun u => |(u : ℝ)| ≤ Real.exp (η * L))
          (kernelSplitCutoff η L)).card := by
  filter_upwards [eventual_large_kernel_population_decay η ε (a / 4) hη hηU hε hεη (by positivity),
    eventual_small_kernel_fibers_decay η ε (a / 4) hη hεη (by positivity)] with L hbig hsmall
  intro S f root m h hm hmU hred hcount hroot hspan hsize
  have hb := hbig S f root m h hm hmU hred hcount hroot hspan
  have hs := hsmall S f hcount
  let R := populatedKernelPoints S f (fun u => |(u : ℝ)| ≤ Real.exp (η * L))
    (kernelSplitCutoff η L)
  have hcover : S ⊆ R ∪ (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|) ∪
      (S.filter fun x => (S.filter fun y => f y = f x).card < kernelSplitCutoff η L) := by
    intro x hx
    by_cases ha : |(f x : ℝ)| ≤ Real.exp (η * L)
    · by_cases hq : kernelSplitCutoff η L ≤ (S.filter fun y => f y = f x).card
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, ha, hq⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, Nat.lt_of_not_ge hq⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge ha⟩))
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hc' := Finset.card_union_le R (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|)
  have hsum : (S.card : ℝ) ≤ R.card +
      (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|).card +
      (S.filter fun x => (S.filter fun y => f y = f x).card < kernelSplitCutoff η L).card := by
    exact_mod_cast (by omega : S.card ≤ R.card +
      (S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|).card +
      (S.filter fun x => (S.filter fun y => f y = f x).card < kernelSplitCutoff η L).card)
  change (a / 2) * Real.exp (L / 2) / L ^ 6 ≤ (R.card : ℝ)
  ring_nf at hb hs hsize ⊢
  linarith only [hsize, hsum, hb, hs]

end Ostmann

end OAI
