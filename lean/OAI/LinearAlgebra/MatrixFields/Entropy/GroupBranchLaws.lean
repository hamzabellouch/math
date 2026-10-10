import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointCompatibilityScaling
import OAI.LinearAlgebra.MatrixFields.Construction.PairMarginals
import OAI.LinearAlgebra.MatrixFields.Parameters.ParametersHalfComplement

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def branchProbability {K : ℕ} (w : Work K) (b : w.Branch) : ℚ :=
  match w with
  | .stageA h => stageALaw (initialShape h.val) (aSplit ⟨h, b, false⟩)
  | .stageB h => stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩)
  | .stageC h => stageCWeight (cParameterParent h) (cShapeParent h) b

theorem branchProbability_nonneg {K : ℕ} (w : Work K) (b : w.Branch) :
    0 ≤ branchProbability w b := by
  cases w with
  | stageA h => exact (stageALaw_positive _ _ (aSplit_mem ⟨h, b, false⟩)).le
  | stageB h => exact (stageBLaw_positive _ _ (bSplit_mem ⟨h, b, false⟩)).le
  | stageC h => exact stageCWeight_nonnegative _ _ b

theorem branchProbability_total {K : ℕ} (w : Work K) :
    ∑ b : w.Branch, branchProbability w b = 1 := by
  cases w with
  | stageA h =>
      change (∑ b : ASplit h,
        stageALaw (initialShape h.val) (below (initialShape h.val))[b.val]) = 1
      rw [Fin.sum_univ_fun_getElem]
      exact stageALaw_normalized _ h.property
  | stageB h =>
      change (∑ b : BSplit h,
        stageBLaw (aShape h.val) (below (aShape h.val))[b.val]) = 1
      rw [Fin.sum_univ_fun_getElem]
      exact stageBLaw_normalized _ h.property
  | stageC h => exact stageCWeight_normalized _ _

def branchLaw {K : ℕ} (w : Work K) : FiniteLaw w.Branch where
  mass b := (branchProbability w b : ℝ)
  nonneg b := by exact_mod_cast branchProbability_nonneg w b
  total := by exact_mod_cast branchProbability_total w

@[simp] theorem branchLaw_mass {K : ℕ} (w : Work K) (b : w.Branch) :
    (branchLaw w).mass b = (branchProbability w b : ℝ) := rfl

def placedLaw {K : ℕ} (w : PlacedWork K) : FiniteLaw JointPopulation.Shape :=
  (branchLaw w.1).map (branchShape w)

@[simp] theorem placedLaw_mass {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) :
    (placedLaw w).mass u =
      ∑ b : w.1.Branch, if branchShape w b = u then
        (branchProbability w.1 b : ℝ) else 0 := by
  simp only [placedLaw, FiniteLaw.map_mass, branchLaw_mass]

theorem placedLaw_mass_branch {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) :
    (placedLaw w).mass (branchShape w b) = (branchProbability w.1 b : ℝ) :=
  FiniteLaw.map_mass_apply _ _ (branchShape_injective w) b

theorem placedLaw_entropy {K : ℕ} (w : PlacedWork K) :
    finiteEntropy (placedLaw w).mass = finiteEntropy (branchLaw w.1).mass :=
  FiniteLaw.map_entropy_of_injective _ _ (branchShape_injective w)

theorem placedLaw_sideMass {K : ℕ} (w : PlacedWork K) (s : Fin 3)
    (k : Fin 17) :
    JointPopulationRates.sideMass (placedLaw w).mass s k =
      ∑ b : w.1.Branch, if JointPopulation.shapeSide s (branchShape w b) = k
        then (branchProbability w.1 b : ℝ) else 0 := by
  unfold JointPopulationRates.sideMass
  simp only [placedLaw_mass]
  calc
    _ = ∑ u : JointPopulation.Shape, ∑ b : w.1.Branch,
        if branchShape w b = u then
          if JointPopulation.shapeSide s u = k then (branchProbability w.1 b : ℝ) else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : JointPopulation.shapeSide s u = k <;> simp [hu]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem branchPopulation_cast_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℚ) =
      (population allocation dilation (w.1.source, w.2) : ℚ) *
        branchProbability w.1 b := by
  rcases w with ⟨w, phi⟩
  cases w <;>
    simp only [branchPopulation, Work.child, Work.source, population_cast,
      amount, canonicalAmount, aAmount, bAmount, cAmount, branchProbability] <;> ring

theorem branchPopulation_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (branchLaw w.1).mass b := by
  rw [branchLaw_mass]
  exact_mod_cast branchPopulation_cast_rat allocation dilation w b

theorem jointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (placedLaw w).mass u := by
  simp only [jointCounts, shapeCounts, Nat.cast_sum, placedLaw_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : branchShape w b = u
  · simp only [hb, ite_true, branchPopulation_cast, branchLaw_mass]
  · simp [hb]

theorem jointCounts_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) /
      population allocation dilation (w.1.source, w.2) = (placedLaw w).mass u := by
  rw [jointCounts_cast]
  have hp : (population allocation dilation (w.1.source, w.2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (work_source_population_pos allocation hd w)
  exact mul_div_cancel_left₀ _ hp

theorem jointCounts_normalized {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) :
    (∑ u, (jointCounts allocation dilation w u : ℝ) /
      population allocation dilation (w.1.source, w.2)) = 1 := by
  simp only [jointCounts_ratio allocation hd]
  exact (placedLaw w).total

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

theorem jointCounts_source_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ((amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u) := by
  rw [jointCounts_cast, population_cast_real, mul_assoc]

theorem jointCounts_source_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) /
      populationLength (K := K) allocation dilation =
        (amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u := by
  rw [jointCounts_source_cast]
  have hp : (populationLength (K := K) allocation dilation : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) hd)
  exact mul_div_cancel_left₀ _ hp

theorem jointCounts_source_rate {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (jointCounts allocation dilation w u : ℝ) /
      populationLength (K := K) allocation dilation) atTop
      (𝓝 ((amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (jointCounts_source_ratio allocation hd w u).symm

theorem populationLength_dilation {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    populationLength (K := K) allocation dilation =
      dilation * populationLength (K := K) allocation 1 := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, one_mul]

theorem jointCounts_dilation_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) / (dilation : ℝ) =
      ((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u := by
  rw [jointCounts_source_cast, populationLength_dilation, Nat.cast_mul]
  have hd' : (dilation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  field_simp [hd']

theorem jointCounts_dilation_rate {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (jointCounts allocation dilation w u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (jointCounts_dilation_ratio allocation hd w u).symm

def orderLaw {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma) :
    FiniteLaw JointPopulation.Shape := placedLaw h.val.val

def orderMass {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (h : ActiveOrder K tick sigma) : ℝ :=
  amount allocation (h.val.val.1.source, h.val.val.2)

def orderCounts {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (dilation : ℕ) (h : ActiveOrder K tick sigma) : JointPopulation.Shape → ℕ :=
  activeCounts allocation dilation h.val

theorem orderMass_nonneg {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (h : ActiveOrder K tick sigma) : 0 ≤ orderMass allocation h := by
  unfold orderMass
  exact_mod_cast amount_nonneg allocation (h.val.val.1.source, h.val.val.2)

theorem orderCounts_source_cast {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (dilation : ℕ) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) :
    (orderCounts allocation dilation h u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        (orderMass allocation h * (orderLaw h).mass u) :=
  jointCounts_source_cast allocation dilation h.val.val u

theorem orderCounts_source_rate {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (orderCounts allocation dilation h u : ℝ) /
      populationLength (K := K) allocation dilation) atTop
      (𝓝 (orderMass allocation h * (orderLaw h).mass u)) :=
  jointCounts_source_rate allocation h.val.val u

theorem orderCounts_dilation_rate {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (orderCounts allocation dilation h u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
        (orderLaw h).mass u)) :=
  jointCounts_dilation_rate allocation h.val.val u

end MatrixMultiplication.AllFieldActiveLaws






namespace MatrixMultiplication.AllFieldGroupTargetRate

open AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem source_unit_pos (allocation : Allocation) :
    0 < populationLength (K := K) allocation 1 :=
  AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) (by decide)

theorem source_length_dilation (allocation : Allocation) (m : ℕ) :
    populationLength (K := K) allocation m =
      m * populationLength (K := K) allocation 1 :=
  populationLength_dilation allocation m

theorem orderCounts_dilation (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    orderCounts allocation m h u = m * orderCounts allocation 1 h u := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_mul, orderCounts_source_cast, orderCounts_source_cast,
    populationLength_dilation, Nat.cast_mul]
  ring

theorem orderCounts_dilation_fun (allocation : Allocation) (m : ℕ) :
    orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m =
      fun h u => m * orderCounts allocation 1 h u := by
  funext h u
  exact orderCounts_dilation allocation m h u

theorem orderCounts_sum (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    (∑ u, orderCounts allocation m h u) =
      population allocation m (h.val.val.1.source, h.val.val.2) :=
  jointCounts_sum allocation m h.val.val

theorem baseSize_eq_population (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    JointCompatibilityScaling.baseSize (orderCounts allocation m) h =
      population allocation m (h.val.val.1.source, h.val.val.2) :=
  orderCounts_sum allocation m h

theorem baseSize_dilation (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    JointCompatibilityScaling.baseSize (orderCounts allocation m) h =
      m * JointCompatibilityScaling.baseSize (orderCounts allocation 1) h := by
  simp only [JointCompatibilityScaling.baseSize]
  simp_rw [orderCounts_dilation allocation m]
  exact (Finset.mul_sum Finset.univ _ m).symm

theorem baseSize_cast_real (allocation : Allocation)
    (h : ActiveOrder K tick sigma) :
    (JointCompatibilityScaling.baseSize (orderCounts allocation 1) h : ℝ) =
      (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h := by
  rw [baseSize_eq_population, population_cast_real]
  rfl

theorem baseSize_pos (allocation : Allocation)
    (h : ActiveOrder K tick sigma) :
    0 < JointCompatibilityScaling.baseSize (orderCounts allocation 1) h := by
  rw [baseSize_eq_population]
  exact work_source_population_pos allocation (by decide) h.val.val

theorem base_empirical_eq (allocation : Allocation)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    (orderCounts allocation 1 h u : ℝ) /
      JointCompatibilityScaling.baseSize (orderCounts allocation 1) h =
        (orderLaw h).mass u := by
  rw [baseSize_eq_population]
  exact jointCounts_ratio allocation (by decide) h.val.val u

def groupEntropyRate (allocation : Allocation) : ℝ :=
  ∑ h : ActiveOrder K tick sigma,
    ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass

theorem groupEntropyRate_nonneg (allocation : Allocation) :
    0 ≤ groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h))
    (FiniteLaw.entropy_nonneg (orderLaw h))

theorem baseEntropy_eq_groupEntropyRate (allocation : Allocation) :
    JointCompatibilityScaling.baseEntropy
      (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation 1) =
        groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation := by
  simp only [JointCompatibilityScaling.baseEntropy, groupEntropyRate]
  simp only [base_empirical_eq]
  simp only [baseSize_cast_real]

theorem target_card_pos (allocation : Allocation) (m : ℕ) :
    0 < Fintype.card (JointPopulation.Target
      (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)) :=
  Fintype.card_pos_iff.mpr (JointPopulation.target_nonempty _)

theorem tendsto_log_target_card_div (allocation : Allocation) :
    Tendsto (fun m : ℕ =>
      Real.log (Fintype.card (JointPopulation.Target
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)) : ℝ) /
          (m : ℝ)) atTop
      (𝓝 (groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation)) := by
  apply JointPopulationRates.tendsto_log_target_card_div_of_coordinate_rates
    (fun m => orderCounts allocation m)
    (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
    (fun h => (orderLaw h).mass)
  · intro h
    exact mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h)
  · intro h
    exact (orderLaw h).total
  · exact orderCounts_dilation_rate allocation

theorem tendsto_log_targetSet_card_div (allocation : Allocation) :
    Tendsto (fun m : ℕ =>
      Real.log ((JointPopulation.targetSet
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)).card : ℝ) /
          (m : ℝ)) atTop
      (𝓝 (groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation)) := by
  simpa only [JointPopulation.target_card, JointPopulation.targetSet_card] using
    tendsto_log_target_card_div (K := K) (tick := tick) (sigma := sigma) allocation

end MatrixMultiplication.AllFieldGroupTargetRate






namespace MatrixMultiplication.AllFieldPairConditionalEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldPairMarginals
open scoped BigOperators

theorem entropy_sub_eq_conditional_sum
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (q : FiniteLaw B) (m : FiniteLaw C)
    (f : A → C) (g : B → C) (hp : p.map f = m) (hq : q.map g = m) :
    finiteEntropy p.mass - finiteEntropy q.mass =
      ∑ k, m.mass k * (finiteEntropy (p.conditional f k).mass -
        finiteEntropy (q.conditional g k).mass) := by
  rw [p.entropy_eq_map_add_conditional f, q.entropy_eq_map_add_conditional g, hp, hq]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

def stageASplitWeight (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    Fin (below g).length → Fin 17 :=
  fun j => ⟨(below g).get j side,
    Nat.lt_succ_of_le ((below_le (List.get_mem _ _) side).trans
      ((positiveInitial_shape_spec g hg).1 side))⟩

def stageBSplitWeight (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    Fin (below t).length → Fin 17 :=
  fun j => ⟨(below t).get j side,
    Nat.lt_succ_of_le ((below_le (List.get_mem _ _) side).trans
      ((positiveSecond_shape_spec t ht).1 side))⟩

theorem stageASplitLaw_ownWeight_marginal (g : Shape) (hg : g ∈ positiveInitial)
    (side : Fin 3) :
    (stageASplitLaw g hg).map (stageASplitWeight g hg side) =
      stageAMarginalLaw g hg side := rfl

theorem stageBSplitLaw_ownWeight_marginal (t : Shape) (ht : t ∈ positiveSecond)
    (side : Fin 3) :
    (stageBSplitLaw t ht).map (stageBSplitWeight t ht side) =
      stageBMarginalLaw t ht side := rfl

theorem stageA_entropy_sub_pair_eq_conditional_sum
    (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    finiteEntropy (stageASplitLaw g hg).mass -
      finiteEntropy (stageAPairLaw g hg side).mass =
      ∑ k, (stageAMarginalLaw g hg side).mass k *
        (finiteEntropy ((stageASplitLaw g hg).conditional
            (stageASplitWeight g hg side) k).mass -
          finiteEntropy ((stageAPairLaw g hg side).conditional
            (fun ij => halfWeightCode ij.1) k).mass) :=
  entropy_sub_eq_conditional_sum _ _ _ _ _
    (stageASplitLaw_ownWeight_marginal g hg side)
    (stageAPairLaw_leftWeight_marginal g hg side)

theorem stageB_entropy_sub_pair_eq_conditional_sum
    (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    finiteEntropy (stageBSplitLaw t ht).mass -
      finiteEntropy (stageBPairLaw t ht side).mass =
      ∑ k, (stageBMarginalLaw t ht side).mass k *
        (finiteEntropy ((stageBSplitLaw t ht).conditional
            (stageBSplitWeight t ht side) k).mass -
          finiteEntropy ((stageBPairLaw t ht side).conditional
            (fun ij => statisticWeightCode ij.1) k).mass) :=
  entropy_sub_eq_conditional_sum _ _ _ _ _
    (stageBSplitLaw_ownWeight_marginal t ht side)
    (stageBPairLaw_leftWeight_marginal t ht side)

end MatrixMultiplication.AllFieldPairConditionalEntropy






namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity AllFieldPairMarginals AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def statisticComplement {K : ℕ} (w : Work K) : w.Statistic ≃ w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.orderedComplementStatistic
  | .stageB _ => CWCompleteStatistics.complementStatistic
  | .stageC _ => Equiv.refl _

theorem childLaw_complementary_sides {K : ℕ} (w : Work K)
    (u : Shape) (hu : u ∈ shapes (2 * w.halfLength))
    (source target : Fin 3) (hne : source ≠ target)
    (hsum : u source + u target = 2 * w.halfLength) (a : w.Statistic) :
    w.childLaw u source ((statisticComplement w).symm a) = w.childLaw u target a := by
  cases w with
  | stageA h => exact halfLaw_complementary_sides u hu source target hne hsum a
  | stageB h =>
      exact littleLaw_complement (aShape h.val) u source target
        (lt_of_le_of_lt (mem_shapes_bound hu source) (by norm_num [Work.halfLength]))
        (lt_of_le_of_lt (mem_shapes_bound hu target) (by norm_num [Work.halfLength]))
        hsum a
  | stageC h => rfl

def halfLawAt {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) : Statistic h → ℝ :=
  if right then rightLaw h u side else leftLaw h u side

def childWeight {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) : ℕ :=
  if right then activeParentShape h side - (JointPopulation.shapeSide side u).val
  else (JointPopulation.shapeSide side u).val

theorem halfLawAt_eq {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    halfLawAt right h u side a =
      (h.val.1.childLaw
        (halfShape h.val.1.parentShape (canonicalChildShape h.val u) right)
        (h.val.2.symm side) a : ℝ) := by
  cases right <;> rfl

theorem halfLawAt_nonnegative {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    0 ≤ halfLawAt right h u side a := by
  cases right
  · exact leftLaw_nonnegative h u side a
  · exact rightLaw_nonnegative h u side a

theorem halfLawAt_normalized {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    ∑ a, halfLawAt right h u side a = 1 := by
  cases right
  · exact leftLaw_normalized allocation m h u hu side
  · exact rightLaw_normalized allocation m h u hu side

theorem halfLawAt_le_one_of_counts_pos {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) (a : Statistic h) :
    halfLawAt right h u side a ≤ 1 := by
  have hle := Finset.single_le_sum
    (fun b (_ : b ∈ Finset.univ) => halfLawAt_nonnegative right h u side b)
    (Finset.mem_univ a)
  rw [halfLawAt_normalized allocation m right h u hu side] at hle
  exact hle

def supportedHalfLaw {K tick : ℕ} (allocation : Allocation) (right : Bool)
    (h : Active K tick) (u : JointPopulation.Shape) (side : Fin 3) : Statistic h → ℝ :=
  if 0 < activeCounts allocation 1 h u then halfLawAt right h u side else fun _ => 0

theorem supportedHalfLaw_bounds {K tick : ℕ} (allocation : Allocation) (right : Bool)
    (h : Active K tick) (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    0 ≤ supportedHalfLaw allocation right h u side a ∧
      supportedHalfLaw allocation right h u side a ≤ 1 := by
  unfold supportedHalfLaw
  split_ifs with hu
  · exact ⟨halfLawAt_nonnegative right h u side a,
      halfLawAt_le_one_of_counts_pos allocation 1 right h u hu side a⟩
  · norm_num

theorem supportedHalfLaw_eq_of_counts_pos {K tick : ℕ} (allocation : Allocation)
    (m : ℕ) (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    supportedHalfLaw allocation right h u side = halfLawAt right h u side := by
  have hbase : 0 < activeCounts allocation 1 h u := by
    rw [AllFieldHistorySupport.activeCounts_dilation] at hu
    exact Nat.pos_of_mul_pos_left hu
  simp only [supportedHalfLaw, hbase, ite_true]

theorem placedLaw_mass_zero_of_count_zero {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : jointCounts allocation 1 w u = 0) : (placedLaw w).mass u = 0 := by
  have hp : (population allocation 1 (w.1.source, w.2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (AllFieldHistory.work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) w)
  have he := jointCounts_cast allocation 1 w u
  rw [hu, Nat.cast_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hp

theorem halfShape_childWeight {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) :
    (halfShape h.val.1.parentShape (canonicalChildShape h.val u) right)
      (h.val.2.symm side) = childWeight right h u side := by
  cases right <;>
    simp [halfShape, canonicalChildShape, childWeight, activeParentShape,
      physicalShape, decodeShape, AllFieldParameters.complement]

theorem halfShape_mem_of_counts_pos {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) :
    halfShape h.val.1.parentShape (canonicalChildShape h.val u) right ∈
      shapes (2 * h.val.1.halfLength) := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  rw [canonicalChildShape_branchShape]
  exact h.val.1.halfShape_mem b right

theorem childWeight_sum {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (sigma : Placement) :
    childWeight right h u (sigma 0) + childWeight right h u (sigma 1) +
      childWeight right h u (sigma 2) = 2 * h.val.1.halfLength := by
  let v := halfShape h.val.1.parentShape (canonicalChildShape h.val u) right
  have ht := mem_shapes_total (halfShape_mem_of_counts_pos allocation m right h u hu)
  have hp := Equiv.sum_comp (sigma.trans h.val.2.symm) v
  have he : (∑ i : Fin 3, v (h.val.2.symm (sigma i))) = 2 * h.val.1.halfLength := by
    calc
      _ = ∑ i : Fin 3, v i := hp
      _ = _ := by simpa [v, shapeTotal, Fin.sum_univ_succ, Nat.add_assoc] using ht
  simpa [v, halfShape_childWeight, Fin.sum_univ_succ, Nat.add_assoc] using he

theorem designated_source_geometry (weight : Fin 3 → ℕ) (total : ℕ)
    (htotal : weight 0 + weight 1 + weight 2 = total) (side : Fin 3)
    (hd : if side = 1 then weight 2 = 0
      else if side = 2 then weight 0 * weight 1 = 0 else False) :
    let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then 1 else 0
    source ≠ side ∧ weight source + weight side = total := by
  fin_cases side
  · simp at hd
  · simp at hd ⊢
    omega
  · by_cases hzero : weight 1 = 0
    · simp [hzero] at hd ⊢
      omega
    · have hz : weight 0 = 0 := by simpa [hzero] using hd
      simp [hzero]
      omega

theorem compatibilityLaw_eq {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (sigma : Placement) (right : Bool) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u)
    (hd : designated right side sigma h u) :
    compatibilityLaw right side sigma h u =
      if right then rightLaw h.val u (sigma side) else leftLaw h.val u (sigma side) := by
  let weight : Fin 3 → ℕ := fun i => childWeight right h.val u (sigma i)
  let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then 1 else 0
  have hdesignated : if side = 1 then weight 2 = 0
      else if side = 2 then weight 0 * weight 1 = 0 else False := by
    simpa only [AllFieldGroupOrbitData.designated, weight, childWeight] using hd.2
  have hgeom := designated_source_geometry weight (2 * h.val.val.1.halfLength)
    (childWeight_sum allocation m right h.val u hu sigma) side hdesignated
  have hsource : (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0) = sigma source := by
    dsimp only [source]
    split_ifs <;> rfl
  have hne : h.val.val.2.symm (sigma source) ≠ h.val.val.2.symm (sigma side) := by
    intro heq
    exact hgeom.1 (sigma.injective (h.val.val.2.symm.injective heq))
  have hsum :
      (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
          (h.val.val.2.symm (sigma source)) +
        (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
          (h.val.val.2.symm (sigma side)) = 2 * h.val.val.1.halfLength := by
    simpa only [halfShape_childWeight] using hgeom.2
  funext a
  have hlaw := childLaw_complementary_sides h.val.val.1
    (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
    (halfShape_mem_of_counts_pos allocation m right h.val u hu)
    (h.val.val.2.symm (sigma source)) (h.val.val.2.symm (sigma side)) hne hsum a
  have hre : halfLawAt right h.val u (sigma source)
      ((statisticComplement h.val.val.1).symm a) =
        halfLawAt right h.val u (sigma side) a := by
    rw [halfLawAt_eq, halfLawAt_eq]
    exact_mod_cast hlaw
  change ((if right then rightLaw h.val u
      (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0)
    else leftLaw h.val u
      (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0))
      ((statisticComplement h.val.val.1).symm a)) = _
  rw [hsource]
  exact hre

def nativePairLaw {K : ℕ} (w : Work K) (side : Fin 3) :
    FiniteLaw (w.Statistic × w.Statistic) :=
  match w with
  | .stageA h => stageAPairLaw (initialShape h.val) h.property side
  | .stageB h => stageBPairLaw (aShape h.val) h.property side
  | .stageC parent =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          let : Unique (Work.stageC parent).Statistic := inferInstanceAs (Unique PUnit)
          simp }

theorem placedLaw_sum_mul {K : ℕ} (w : PlacedWork K)
    (f : JointPopulation.Shape → ℝ) :
    (∑ u, (placedLaw w).mass u * f u) =
      ∑ b : w.1.Branch, (branchLaw w.1).mass b * f (branchShape w b) := by
  exact (JointEntropyMax.sum_mass_mul_coordinate
    (branchLaw w.1) (branchShape w) f).symm

theorem childLaw_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (a : w.1.Statistic) :
    childLaw w (branchShape w b) side a =
      (w.1.childLaw (w.1.splitShape b) (w.2.symm side) a : ℝ) := by
  change (w.1.childLaw (canonicalChildShape w (branchShape w b))
    (w.2.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape]

theorem rightChildLaw_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (a : w.1.Statistic) :
    rightChildLaw w (branchShape w b) side a =
      (w.1.childLaw (AllFieldParameters.complement w.1.parentShape (w.1.splitShape b))
        (w.2.symm side) a : ℝ) := by
  change (w.1.childLaw
    (AllFieldParameters.complement w.1.parentShape (canonicalChildShape w (branchShape w b)))
    (w.2.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape]

theorem branchPairMixture_eq_native {K : ℕ} (w : Work K) (side : Fin 3)
    (a : w.Statistic × w.Statistic) :
    (∑ b : w.Branch, (branchLaw w).mass b *
      (w.childLaw (w.splitShape b) side a.1 : ℝ) *
      (w.childLaw (AllFieldParameters.complement w.parentShape (w.splitShape b)) side a.2 : ℝ)) =
      (nativePairLaw w side).mass a := by
  cases w with
  | stageA h =>
      change (∑ b : Fin (below (initialShape h.val)).length,
        (stageALaw (initialShape h.val) (below (initialShape h.val))[b.val] : ℝ) *
          (halfLaw (below (initialShape h.val))[b.val] side a.1 : ℝ) *
          (halfLaw (AllFieldParameters.complement (initialShape h.val)
            (below (initialShape h.val))[b.val]) side a.2 : ℝ)) = _
      exact Fin.sum_univ_fun_getElem _ (fun u : Shape =>
        (stageALaw (initialShape h.val) u : ℝ) * (halfLaw u side a.1 : ℝ) *
          (halfLaw (AllFieldParameters.complement (initialShape h.val) u) side a.2 : ℝ))
  | stageB h =>
      change (∑ b : Fin (below (aShape h.val)).length,
        (stageBLaw (aShape h.val) (below (aShape h.val))[b.val] : ℝ) *
          (littleLaw (aShape h.val) (below (aShape h.val))[b.val] side a.1 : ℝ) *
          (littleLaw (aShape h.val) (AllFieldParameters.complement (aShape h.val)
            (below (aShape h.val))[b.val]) side a.2 : ℝ)) = _
      exact Fin.sum_univ_fun_getElem _ (fun u : Shape =>
        (stageBLaw (aShape h.val) u : ℝ) *
          (littleLaw (aShape h.val) u side a.1 : ℝ) *
          (littleLaw (aShape h.val) (AllFieldParameters.complement (aShape h.val) u) side a.2 : ℝ))
  | stageC h =>
      simpa only [Work.childLaw, Rat.cast_one, mul_one, nativePairLaw] using
        (branchLaw (Work.stageC h)).total

def placedPairMixture {K : ℕ} (w : PlacedWork K) (side : Fin 3)
    (a : w.1.Statistic × w.1.Statistic) : ℝ :=
  ∑ u, (placedLaw w).mass u * childLaw w u side a.1 * rightChildLaw w u side a.2

theorem placedPairMixture_eq_native {K : ℕ} (w : PlacedWork K) (side : Fin 3)
    (a : w.1.Statistic × w.1.Statistic) :
    placedPairMixture w side a = (nativePairLaw w.1 (w.2.symm side)).mass a := by
  simp only [placedPairMixture, mul_assoc]
  rw [placedLaw_sum_mul]
  simpa only [childLaw_branchShape, rightChildLaw_branchShape, mul_assoc] using
    branchPairMixture_eq_native w.1 (w.2.symm side) a

theorem placement_symm_order_side {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    h.val.val.2.symm (sigma side) = h.val.val.1.priority side := by
  have hs : h.val.val.2 (h.val.val.1.priority side) = sigma side :=
    Equiv.congr_fun h.property side
  rw [← hs, Equiv.symm_apply_apply]

def orderPairMixture {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) : ℝ :=
  ∑ u, (orderLaw h).mass u * leftLaw h.val u (sigma side) a.1 *
    rightLaw h.val u (sigma side) a.2

theorem orderPairMixture_eq_native {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) :
    orderPairMixture h side a =
      (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass a := by
  change placedPairMixture h.val.val (sigma side) a = _
  rw [placedPairMixture_eq_native, placement_symm_order_side]

theorem orderPairMixture_supported {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) :
    (∑ u, (orderLaw h).mass u *
      supportedHalfLaw allocation false h.val u (sigma side) a.1 *
      supportedHalfLaw allocation true h.val u (sigma side) a.2) =
        (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass a := by
  rw [← orderPairMixture_eq_native]
  unfold orderPairMixture
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · simp [supportedHalfLaw, hu, halfLawAt]
  · have hz : (orderLaw h).mass u = 0 :=
      placedLaw_mass_zero_of_count_zero allocation h.val.val u (Nat.eq_zero_of_not_pos hu)
    simp only [hz, zero_mul]

theorem orderPairMixture_nonneg {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) : 0 ≤ orderPairMixture h side a := by
  rw [orderPairMixture_eq_native]
  exact (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).nonneg a

theorem orderPairMixture_total {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    ∑ a, orderPairMixture h side a = 1 := by
  simp_rw [orderPairMixture_eq_native]
  exact (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).total

theorem orderPairMixture_entropy {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    finiteEntropy (orderPairMixture h side) =
      finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass := by
  have hm : orderPairMixture h side =
      (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass :=
    funext (orderPairMixture_eq_native h side)
  rw [hm]

def nativeStatisticWeightCode {K : ℕ} (w : Work K) : w.Statistic → Fin 17 :=
  match w with
  | .stageA _ => halfWeightCode
  | .stageB _ => statisticWeightCode
  | .stageC _ => fun _ => 0

def nativeSplitWeightCode {K : ℕ} (w : Work K) (side : Fin 3)
    (b : w.Branch) : Fin 17 :=
  ⟨w.splitShape b side, Nat.lt_succ_of_le ((w.splitShape_spec b).1 side)⟩

@[simp] theorem nativeSplitWeightCode_val {K : ℕ} (w : Work K) (side : Fin 3)
    (b : w.Branch) : (nativeSplitWeightCode w side b).val = w.splitShape b side := rfl

theorem nativePairLaw_weight_marginal {K : ℕ} (w : Work K) (side : Fin 3)
    (hstage : w.stage ≠ 2) :
    (nativePairLaw w side).map (fun a => nativeStatisticWeightCode w a.1) =
      (branchLaw w).map (nativeSplitWeightCode w side) := by
  cases w with
  | stageA h =>
      change (stageAPairLaw (initialShape h.val) h.property side).map
        (fun a => halfWeightCode a.1) =
          (stageASplitLaw (initialShape h.val) h.property).map
            (stageASplitWeight (initialShape h.val) h.property side)
      rw [stageAPairLaw_leftWeight_marginal, stageASplitLaw_ownWeight_marginal]
  | stageB h =>
      change (stageBPairLaw (aShape h.val) h.property side).map
        (fun a => statisticWeightCode a.1) =
          (stageBSplitLaw (aShape h.val) h.property).map
            (stageBSplitWeight (aShape h.val) h.property side)
      rw [stageBPairLaw_leftWeight_marginal, stageBSplitLaw_ownWeight_marginal]
  | stageC h => exact False.elim (hstage rfl)

private theorem commonWeight_law_ext {A : Type*} [Fintype A]
    (p q : FiniteLaw A) (hmass : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with
  | mk p hp htotal =>
      cases q with
      | mk q hq hqtotal =>
          have heq : p = q := funext hmass
          subst q
          rfl

theorem order_branch_weight {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) (b : h.val.val.1.Branch) :
    JointPopulation.shapeSide (sigma side) (branchShape h.val.val b) =
      nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b := by
  apply Fin.ext
  rw [branchShape, encodePhysicalShape_side, nativeSplitWeightCode_val,
    placement_symm_order_side]

theorem orderLaw_weight_marginal {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    (orderLaw h).map (JointPopulation.shapeSide (sigma side)) =
      (branchLaw h.val.val.1).map
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) := by
  apply commonWeight_law_ext
  intro k
  have hm : ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass k =
      JointPopulationRates.sideMass (placedLaw h.val.val).mass (sigma side) k := by
    rw [FiniteLaw.map_mass]
    unfold JointPopulationRates.sideMass
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k <;> simp [hu, orderLaw]
  rw [hm, placedLaw_sideMass, FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro b _
  simp only [order_branch_weight, branchLaw_mass]

theorem orderPairLaw_common_weight {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) (hstage : h.val.val.1.stage ≠ 2) :
    (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).map
        (fun a => nativeStatisticWeightCode h.val.val.1 a.1) =
      (orderLaw h).map (JointPopulation.shapeSide (sigma side)) := by
  rw [nativePairLaw_weight_marginal _ _ hstage, orderLaw_weight_marginal]

theorem order_entropy_sub_pair_eq_conditional_sum
    {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hstage : h.val.val.1.stage ≠ 2) :
    finiteEntropy (orderLaw h).mass -
        finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass =
      ∑ k, ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass k *
        (finiteEntropy ((orderLaw h).conditional
            (JointPopulation.shapeSide (sigma side)) k).mass -
          finiteEntropy ((nativePairLaw h.val.val.1 (h.val.val.1.priority side)).conditional
            (fun a => nativeStatisticWeightCode h.val.val.1 a.1) k).mass) :=
  entropy_sub_eq_conditional_sum _ _ _ _ _ rfl (orderPairLaw_common_weight h side hstage)

theorem order_entropy_sub_mixture_eq_conditional_sum
    {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hstage : h.val.val.1.stage ≠ 2) :
    finiteEntropy (orderLaw h).mass - finiteEntropy (orderPairMixture h side) =
      ∑ k, ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass k *
        (finiteEntropy ((orderLaw h).conditional
            (JointPopulation.shapeSide (sigma side)) k).mass -
          finiteEntropy ((nativePairLaw h.val.val.1 (h.val.val.1.priority side)).conditional
            (fun a => nativeStatisticWeightCode h.val.val.1 a.1) k).mass) := by
  rw [orderPairMixture_entropy]
  exact order_entropy_sub_pair_eq_conditional_sum h side hstage

end MatrixMultiplication.AllFieldGroupNativeLaws






namespace MatrixMultiplication.JointConditionalCountEntropy

open MatrixMultiplication.Foundation JointPopulationRates
open scoped BigOperators

variable {U A : Type*} [Fintype U] [Fintype A]

attribute [local instance] Classical.propDecidable

def classCounts (n : U → ℕ) (f : U → A) (a : A) (u : U) : ℕ :=
  if f u = a then n u else 0

def classSize (n : U → ℕ) (f : U → A) (a : A) : ℕ :=
  ∑ u, classCounts n f a u

theorem classSize_total (n : U → ℕ) (f : U → A) :
    (∑ a, classSize n f a) = ∑ u, n u := by
  classical
  unfold classSize classCounts
  rw [Finset.sum_comm]
  simp

theorem sum_masked_entropy (p : U → ℝ) (f : U → A) :
    (∑ a, finiteEntropy (fun u => if f u = a then p u else 0)) =
      finiteEntropy p := by
  classical
  have ht (a : A) (u : U) :
      entropyTerm (if f u = a then p u else 0) =
        if f u = a then entropyTerm (p u) else 0 := by
    by_cases h : f u = a <;> simp [h]
  simp only [finiteEntropy, ht]
  rw [Finset.sum_comm]
  simp

theorem sum_classCounts_entropy (n : U → ℕ) (f : U → A) (scale : ℝ) :
    (∑ a, finiteEntropy (fun u => (classCounts n f a u : ℝ) / scale)) =
      finiteEntropy (fun u => (n u : ℝ) / scale) := by
  classical
  have hm (a : A) :
      (fun u => (classCounts n f a u : ℝ) / scale) =
        (fun u => if f u = a then (n u : ℝ) / scale else 0) := by
    funext u
    by_cases h : f u = a <;> simp [classCounts, h]
  simp_rw [hm]
  exact sum_masked_entropy _ f

theorem sum_scaled_class_empirical_entropy (n : U → ℕ) (f : U → A)
    (scale : ℝ) :
    (∑ a, ((classSize n f a : ℝ) / scale) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      finiteEntropy (fun u => (n u : ℝ) / scale) -
        finiteEntropy (fun a => (classSize n f a : ℝ) / scale) := by
  calc
    _ = ∑ a, (finiteEntropy (fun u => (classCounts n f a u : ℝ) / scale) -
        entropyTerm ((classSize n f a : ℝ) / scale)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact weighted_empirical_entropy_eq (classCounts n f a) scale
    _ = _ := by
      rw [Finset.sum_sub_distrib, sum_classCounts_entropy]
      rfl

theorem sum_classSize_mul_empirical_entropy (n : U → ℕ) (f : U → A) :
    (∑ a, (classSize n f a : ℝ) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      (∑ u, n u : ℕ) *
        (finiteEntropy (fun u => (n u : ℝ) / (∑ v, n v : ℕ)) -
          finiteEntropy (fun a => (classSize n f a : ℝ) / (∑ v, n v : ℕ))) := by
  have hclasses := sum_scaled_class_empirical_entropy n f 1
  have hjoint := weighted_empirical_entropy_eq n 1
  have hmarginal := weighted_empirical_entropy_eq (classSize n f) 1
  simp only [div_one] at hclasses hjoint hmarginal
  rw [classSize_total] at hmarginal
  rw [hclasses, mul_sub, hjoint, hmarginal]
  ring

theorem sum_classSize_mul_entropy_of_law (n : U → ℕ) (f : U → A)
    (p : FiniteLaw U) (scale : ℝ)
    (hn : ∀ u, (n u : ℝ) = scale * p.mass u) :
    (∑ a, (classSize n f a : ℝ) *
      finiteEntropy (fun u =>
        (classCounts n f a u : ℝ) / (classSize n f a : ℝ))) =
      scale * (finiteEntropy p.mass - finiteEntropy (p.map f).mass) := by
  classical
  have hclass (a : A) : (classSize n f a : ℝ) = scale * (p.map f).mass a := by
    rw [classSize, Nat.cast_sum, FiniteLaw.map_mass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : f u = a <;> simp [classCounts, h, hn]
  have h := sum_scaled_class_empirical_entropy n f 1
  simp only [div_one] at h
  rw [h]
  simp_rw [hn, hclass]
  rw [finiteEntropy_scalar p.mass scale p.total,
    finiteEntropy_scalar (p.map f).mass scale (p.map f).total]
  ring

end MatrixMultiplication.JointConditionalCountEntropy






namespace MatrixMultiplication.AllFieldGroupBranchLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldGroupNativeLaws
attribute [local instance] Classical.propDecidable Classical.decEq

theorem jointCounts_branch_pos {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (b : w.1.Branch)
    (hb : 0 < (branchLaw w.1).mass b) :
    0 < jointCounts allocation dilation w (branchShape w b) := by
  have hp : 0 < (population allocation dilation (w.1.source, w.2) : ℝ) := by
    exact_mod_cast work_source_population_pos allocation hd w
  have hc : 0 < (jointCounts allocation dilation w (branchShape w b) : ℝ) := by
    rw [jointCounts_cast, placedLaw_mass_branch]
    exact mul_pos hp hb
  exact_mod_cast hc

theorem branchLaw_stageA_mass_pos {K : ℕ} (h : InitialPositive K)
    (b : (Work.stageA h).Branch) :
    0 < (branchLaw (Work.stageA h)).mass b := by
  change 0 < (stageALaw (initialShape h.val) (aSplit ⟨h, b, false⟩) : ℝ)
  exact_mod_cast stageALaw_positive _ _ (aSplit_mem ⟨h, b, false⟩)

theorem branchLaw_stageB_mass_pos {K : ℕ} (h : APositive K)
    (b : (Work.stageB h).Branch) :
    0 < (branchLaw (Work.stageB h)).mass b := by
  change 0 < (stageBLaw (aShape h.val) (bSplit ⟨h, b, false⟩) : ℝ)
  exact_mod_cast stageBLaw_positive _ _ (bSplit_mem ⟨h, b, false⟩)

theorem supportedHalfLaw_branchShape_of_mass_pos {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (right : Bool) (h : ActiveOrder K tick sigma)
    (b : h.val.val.1.Branch) (hb : 0 < (branchLaw h.val.val.1).mass b)
    (side : Fin 3) :
    supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) =
      fun a => (h.val.val.1.childLaw
        (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) a : ℝ) := by
  have hc : 0 < activeCounts allocation 1 h.val (branchShape h.val.val b) :=
    jointCounts_branch_pos allocation (by decide) h.val.val b hb
  rw [supportedHalfLaw_eq_of_counts_pos allocation 1 right h.val _ hc]
  funext a
  rw [halfLawAt_eq, canonicalChildShape_branchShape, placement_symm_order_side]

theorem supportedHalfLaw_branchShape_of_mass_ne_zero {K tick : ℕ}
    {sigma : Placement} (allocation : Allocation) (right : Bool)
    (h : ActiveOrder K tick sigma) (b : h.val.val.1.Branch)
    (hb : (branchLaw h.val.val.1).mass b ≠ 0) (side : Fin 3) :
    supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) =
      fun a => (h.val.val.1.childLaw
        (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
        (h.val.val.1.priority side) a : ℝ) := by
  exact supportedHalfLaw_branchShape_of_mass_pos allocation right h b
    (lt_of_le_of_ne ((branchLaw h.val.val.1).nonneg b) (Ne.symm hb)) side

theorem weighted_supportedHalfLaw_branchShape {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (right : Bool) (h : ActiveOrder K tick sigma)
    (b : h.val.val.1.Branch) (side : Fin 3) (a : Statistic h.val) :
    (branchLaw h.val.val.1).mass b *
        supportedHalfLaw allocation right h.val (branchShape h.val.val b) (sigma side) a =
      (branchLaw h.val.val.1).mass b *
        (h.val.val.1.childLaw
          (halfShape h.val.val.1.parentShape (h.val.val.1.splitShape b) right)
          (h.val.val.1.priority side) a : ℝ) := by
  by_cases hb : (branchLaw h.val.val.1).mass b = 0
  · simp only [hb, zero_mul]
  · rw [supportedHalfLaw_branchShape_of_mass_ne_zero allocation right h b hb side]

end MatrixMultiplication.AllFieldGroupBranchLaws

end
end

end MatrixAllFields

end OAI
