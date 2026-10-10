import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Weighted estimates for the finite higher-jet monomials in paper 094-01.
The loss exponent adds under products and is unchanged when the output
order increases; only the multiplicative constant depends on that order. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma weightedBound_const (U : Set A) (s : ℝ) (m : ℕ) (c : E) :
    WeightedBound U s m ‖c‖ (fun _ => c) := by
  intro j _ x _
  by_cases hj : j = 0
  · subst j
    simp only [pow_zero, one_mul, norm_iteratedFDerivWithin_zero]
    exact le_rfl
  · rw [iteratedFDerivWithin_const_of_ne hj]
    simp [norm_nonneg c]

lemma WeightedBound.smul_real {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {c : A → ℝ} {f : A → E}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ContDiffOn ℝ ∞ c U) (hf : ContDiffOn ℝ ∞ f U)
    (hbc : WeightedBound U s m C c) (hbf : WeightedBound U s m D f) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => c x • f x) := by
  have h := hbc.bilinear hU hs hC hD hc hf hbf (ContinuousLinearMap.lsmul ℝ ℝ)
  apply h.mono_const
  exact mul_le_of_le_one_left (by positivity) ContinuousLinearMap.opNorm_lsmul_le

lemma WeightedBound.mul_real {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s C D : ℝ} {m : ℕ} {f g : A → ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (2 ^ m * C * D) (fun x => f x * g x) :=
  hbf.smul_real hU hs hC hD hf hg hbg

/-- A finite product pays only the sum of the factor losses in the scale. -/
lemma WeightedBound.finset_prod {ι : Type*} {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} {m : ℕ} (hs : 0 ≤ s) (a : Finset ι) (C : ι → ℝ) (f : ι → A → ℝ)
    (hC : ∀ i ∈ a, 0 ≤ C i) (hf : ∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U)
    (hb : ∀ i ∈ a, WeightedBound U s m (C i) (f i)) :
    WeightedBound U s m ((2 ^ m) ^ a.card * ∏ i ∈ a, C i) (fun x => ∏ i ∈ a, f i x) := by
  classical
  induction a using Finset.induction_on with
  | empty => simpa using weightedBound_const U s m (1 : ℝ)
  | @insert i a hi ih =>
    have hCa : ∀ j ∈ a, 0 ≤ C j := fun j hj => hC j (Finset.mem_insert_of_mem hj)
    have hfa : ∀ j ∈ a, ContDiffOn ℝ ∞ (f j) U :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hba : ∀ j ∈ a, WeightedBound U s m (C j) (f j) :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hh := (hb i (Finset.mem_insert_self i a)).mul_real hU hs
      (hC i (Finset.mem_insert_self i a))
      (mul_nonneg (by positivity) (Finset.prod_nonneg hCa))
      (hf i (Finset.mem_insert_self i a)) (contDiffOn_prod hfa) (ih hCa hfa hba)
    have he : 2 ^ m * C i * ((2 ^ m) ^ a.card * ∏ j ∈ a, C j) =
        (2 ^ m) ^ (a.card + 1) * (C i * ∏ j ∈ a, C j) := by rw [pow_succ]; ring
    rw [he] at hh
    simpa only [Finset.card_insert_of_notMem hi, Finset.prod_insert hi] using hh

lemma WeightedBound.finset_prod_losses {ι : Type*} {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} {m : ℕ} (hs : 0 < s) (a : Finset ι) (C : ι → ℝ) (p : ι → ℕ)
    (f : ι → A → ℝ) (hC : ∀ i ∈ a, 0 ≤ C i)
    (hf : ∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U)
    (hb : ∀ i ∈ a, WeightedBound U s m (C i / s ^ p i) (f i)) :
    WeightedBound U s m
      (((2 ^ m) ^ a.card * ∏ i ∈ a, C i) / s ^ (∑ i ∈ a, p i))
      (fun x => ∏ i ∈ a, f i x) := by
  have h := WeightedBound.finset_prod hU hs.le a (fun i => C i / s ^ p i) f
    (fun i hi => div_nonneg (hC i hi) (pow_nonneg hs.le _)) hf hb
  simpa only [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, mul_div_assoc] using h

/-- A common loss bound for a finite polynomial is the maximum of the
monomial losses, independent of the number of output derivatives. -/
lemma WeightedBound.finset_sum_losses {ι : Type*} {U : Set A} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} {m p : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (a : Finset ι)
    (C : ι → ℝ) (loss : ι → ℕ) (f : ι → A → E)
    (hC : ∀ i ∈ a, 0 ≤ C i) (hp : ∀ i ∈ a, loss i ≤ p)
    (hf : ∀ i ∈ a, ContDiffOn ℝ ∞ (f i) U)
    (hb : ∀ i ∈ a, WeightedBound U s m (C i / s ^ loss i) (f i)) :
    WeightedBound U s m ((∑ i ∈ a, C i) / s ^ p) (fun x => ∑ i ∈ a, f i x) := by
  have hm (i : ι) (hi : i ∈ a) : WeightedBound U s m (C i / s ^ p) (f i) := by
    apply (hb i hi).mono_const
    exact div_le_div_of_nonneg_left (hC i hi) (pow_pos hs p)
      (pow_le_pow_of_le_one hs.le hs1 (hp i hi))
  simpa only [Finset.sum_div] using
    WeightedBound.finset_sum hU hs.le a (fun i => C i / s ^ p) f hf hm

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
