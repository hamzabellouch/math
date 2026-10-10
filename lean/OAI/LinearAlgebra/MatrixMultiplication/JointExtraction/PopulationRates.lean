import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.Population
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.TypeCounts
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexSeparationAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

theorem tendsto_log_multinomial_div_of_total_div_zero
    {A : Type*} [Fintype A] [DecidableEq A] (counts : ℕ → A → ℕ)
    (hratio : Tendsto
      (fun n : ℕ => ((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hupperlim : Tendsto
      (fun n : ℕ => (((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ)) *
        Real.log (Fintype.card A : ℝ)) atTop (𝓝 0) := by
    simpa using hratio.mul_const (Real.log (Fintype.card A : ℝ))
  refine squeeze_zero ?_ ?_ hupperlim
  · intro n
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (Nat.succ_le_of_lt (Nat.multinomial_pos Finset.univ (counts n)))
    · exact Nat.cast_nonneg n
  · intro n
    have hcardNat : Nat.multinomial Finset.univ (counts n) ≤
        (Fintype.card A) ^ (∑ a, counts n a) := by
      simpa only [exactWords_card] using exactWords_card_le (counts n)
    have hcard : (Nat.multinomial Finset.univ (counts n) : ℝ) ≤
        (Fintype.card A : ℝ) ^ (∑ a, counts n a) := by
      exact_mod_cast hcardNat
    have hlog : Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) ≤
        ((∑ a, counts n a : ℕ) : ℝ) * Real.log (Fintype.card A : ℝ) := by
      simpa only [Real.log_pow] using
        Real.log_le_log (Nat.cast_pos.mpr (Nat.multinomial_pos Finset.univ (counts n))) hcard
    calc
      Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) / (n : ℝ) ≤
          (((∑ a, counts n a : ℕ) : ℝ) * Real.log (Fintype.card A : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      _ = (((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ)) *
          Real.log (Fintype.card A : ℝ) := by ring

theorem tendsto_log_multinomial_div_of_mass
    {A : Type*} [Fintype A] [DecidableEq A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hmass : 0 ≤ mass)
    (htotal : Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ))
      atTop (𝓝 mass))
    (hempirical : 0 < mass → ∀ a, Tendsto
      (fun n : ℕ => (counts n a : ℝ) / (∑ a, counts n a : ℕ)) atTop (𝓝 (p a))) :
    Tendsto (fun n : ℕ => Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) /
      (n : ℝ)) atTop (𝓝 (mass * finiteEntropy p)) := by
  by_cases hzero : mass = 0
  · subst mass
    simpa only [zero_mul] using tendsto_log_multinomial_div_of_total_div_zero counts htotal
  have hpos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hzero)
  have htop : Tendsto (fun n => ∑ a, counts n a) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).mp
      (Tendsto.num (tendsto_natCast_atTop_atTop (R := ℝ)) hpos htotal)
  have hlog := tendsto_log_multinomial_of_empirical_tendsto counts p htop (hempirical hpos)
  apply (htotal.mul hlog).congr'
  filter_upwards [htop.eventually (eventually_gt_atTop (0 : ℕ))] with n hn
  have hn' : ((∑ a, counts n a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [div_mul_div_comm,
    mul_comm (n : ℝ) ((∑ a, counts n a : ℕ) : ℝ), mul_div_mul_left _ _ hn']

theorem tendsto_total_div_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ)) atTop (𝓝 mass) := by
  have h := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [← Finset.sum_div, ← Nat.cast_sum, ← Finset.mul_sum, hp, mul_one] using h

theorem tendsto_empirical_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hmass : 0 < mass) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) (a : A) :
    Tendsto (fun n : ℕ => (counts n a : ℝ) / (∑ a, counts n a : ℕ))
      atTop (𝓝 (p a)) := by
  have htotal := tendsto_total_div_of_coordinate_rates counts mass p hp hcounts
  have h := (hcounts a).div htotal hmass.ne'
  rw [mul_div_cancel_left₀ _ hmass.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

theorem finiteEntropy_scalar {A : Type*} [Fintype A]
    (p : A → ℝ) (mass : ℝ) (hp : ∑ a, p a = 1) :
    finiteEntropy (fun a => mass * p a) = entropyTerm mass + mass * finiteEntropy p := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, one_mul]

theorem weighted_empirical_entropy_eq {A : Type*} [Fintype A]
    (counts : A → ℕ) (scale : ℝ) :
    ((∑ a, counts a : ℕ) / scale) *
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
        finiteEntropy (fun a => (counts a : ℝ) / scale) -
          entropyTerm ((∑ a, counts a : ℕ) / scale) := by
  by_cases hzero : (∑ a, counts a) = 0
  · have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, finiteEntropy]
  have hD : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
  have hsum : (∑ a, (counts a : ℝ) / (∑ a, counts a : ℕ)) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hD]
  have hfac (a : A) : (counts a : ℝ) / scale =
      ((∑ a, counts a : ℕ) / scale) * ((counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    rw [div_mul_div_comm,
      mul_comm ((∑ a, counts a : ℕ) : ℝ) (counts a : ℝ), mul_div_mul_right _ _ hD]
  have h := finiteEntropy_scalar
    (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))
    ((∑ a, counts a : ℕ) / scale) hsum
  simp_rw [← hfac] at h
  linarith

theorem tendsto_weighted_empirical_entropy_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => ((∑ a, counts n a : ℕ) / (n : ℝ)) *
      finiteEntropy (fun a => (counts n a : ℝ) / (∑ a, counts n a : ℕ)))
      atTop (𝓝 (mass * finiteEntropy p)) := by
  have htotal := tendsto_total_div_of_coordinate_rates counts mass p hp hcounts
  have h := (tendsto_finiteEntropy_of_tendsto hcounts).sub (tendsto_entropyTerm htotal)
  rw [finiteEntropy_scalar p mass hp, add_sub_cancel_left] at h
  simpa only [weighted_empirical_entropy_eq] using h

def sideCounts (counts : Shape → ℕ) (s : Fin 3) (a : Fin 17) : ℕ :=
  ∑ u, if shapeSide s u = a then counts u else 0

def sideMass (p : Shape → ℝ) (s : Fin 3) (a : Fin 17) : ℝ :=
  ∑ u, if shapeSide s u = a then p u else 0

theorem sideCounts_total (counts : Shape → ℕ) (s : Fin 3) :
    (∑ a, sideCounts counts s a) = ∑ u, counts u := by
  unfold sideCounts
  rw [Finset.sum_comm]
  simp

theorem sideMass_total (p : Shape → ℝ) (s : Fin 3) :
    (∑ a, sideMass p s a) = ∑ u, p u := by
  unfold sideMass
  rw [Finset.sum_comm]
  simp

theorem tendsto_sideCounts_div_of_coordinate_rates
    (counts : ℕ → Shape → ℕ) (mass : ℝ) (p : Shape → ℝ)
    (hcounts : ∀ u, Tendsto (fun n : ℕ => (counts n u : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p u))) (s : Fin 3) (a : Fin 17) :
    Tendsto (fun n : ℕ => (sideCounts (counts n) s a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * sideMass p s a)) := by
  have hfun (n : ℕ) : (sideCounts (counts n) s a : ℝ) / (n : ℝ) =
      ∑ u, if shapeSide s u = a then (counts n u : ℝ) / (n : ℝ) else 0 := by
    unfold sideCounts
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : shapeSide s u = a <;> simp [h]
  simp_rw [hfun]
  rw [sideMass, Finset.mul_sum]
  apply tendsto_finsetSum
  intro u _
  by_cases h : shapeSide s u = a
  · simpa only [h, ite_true] using hcounts u
  · simp only [h, ite_false, mul_zero]
    exact tendsto_const_nhds

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem target_side_population (counts : H → Shape → ℕ)
    (e : Target counts) (h : H) (s : Fin 3) (a : Fin 17) :
    wordPopulation (sideWord counts s (triple counts e) h) a = sideCounts (counts h) s a := by
  let w : JointTypeCounts.FixedCoarseWords (counts h) (shapeSide s)
      (sideWord counts s (triple counts e) h) :=
    ⟨(e h).val, (e h).property, fun _ => rfl⟩
  exact ((conditionalWords_nonempty_iff
    (sideWord counts s (triple counts e) h)
    (fun b u => if shapeSide s u = b then counts h u else 0)).mp
      ⟨JointTypeCounts.fixedCoarseWordsEquiv _ _ _ w⟩) a

omit [Fintype H] [DecidableEq H] in
theorem tendsto_weighted_target_side_entropy
    (counts : ℕ → H → Shape → ℕ) (e : ∀ n, Target (counts n))
    (mass : H → ℝ) (p : H → Shape → ℝ) (hp : ∀ h, ∑ u, p h u = 1)
    (hcounts : ∀ h u, Tendsto (fun n : ℕ => (counts n h u : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h u))) (h : H) (s : Fin 3) :
    Tendsto (fun n : ℕ => ((∑ u, counts n h u : ℕ) / (n : ℝ)) *
      finiteEntropy (fun a =>
        (wordPopulation (sideWord (counts n) s (triple (counts n) (e n)) h) a : ℝ) /
          (∑ u, counts n h u : ℕ)))
      atTop (𝓝 (mass h * finiteEntropy (sideMass (p h) s))) := by
  have hside := tendsto_weighted_empirical_entropy_of_coordinate_rates
    (fun n => sideCounts (counts n h) s) (mass h) (sideMass (p h) s)
    ((sideMass_total (p h) s).trans (hp h))
    (tendsto_sideCounts_div_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) (hcounts h) s)
  simpa only [target_side_population, sideCounts_total] using hside

theorem tendsto_log_target_card_div
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (htotal : ∀ h, Tendsto (fun n : ℕ => (∑ a, counts n h a : ℕ) / (n : ℝ))
      atTop (𝓝 (mass h)))
    (hempirical : ∀ h, 0 < mass h → ∀ a, Tendsto
      (fun n : ℕ => (counts n h a : ℝ) / (∑ a, counts n h a : ℕ))
        atTop (𝓝 (p h a))) :
    Tendsto (fun n : ℕ => Real.log (Fintype.card (Target (counts n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  simp_rw [target_card]
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun h _ n => Nat.multinomial_pos _ _)
    (fun h _ => tendsto_log_multinomial_div_of_mass
      (fun n => counts n h) (mass h) (p h) (hmass h) (htotal h) (hempirical h))

theorem tendsto_log_target_card_div_of_coordinate_rates
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h) (hp : ∀ h, ∑ a, p h a = 1)
    (hcounts : ∀ h a, Tendsto (fun n : ℕ => (counts n h a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h a))) :
    Tendsto (fun n : ℕ => Real.log (Fintype.card (Target (counts n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  apply tendsto_log_target_card_div counts mass p hmass
  · intro h
    exact tendsto_total_div_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) (hp h) (hcounts h)
  · intro h hpos a
    exact tendsto_empirical_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) hpos (hp h) (hcounts h) a

theorem tendsto_log_targetSet_card_div_of_coordinate_rates
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h) (hp : ∀ h, ∑ a, p h a = 1)
    (hcounts : ∀ h a, Tendsto (fun n : ℕ => (counts n h a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h a))) :
    Tendsto (fun n : ℕ => Real.log ((targetSet (counts n)).card : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  simpa only [target_card, targetSet_card] using
    tendsto_log_target_card_div_of_coordinate_rates counts mass p hmass hp hcounts

end MatrixMultiplication.JointPopulationRates

end

end OAI
