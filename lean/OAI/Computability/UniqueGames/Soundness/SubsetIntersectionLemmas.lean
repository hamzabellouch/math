import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Reduction.FinalParametersLemmas
import OAI.Computability.UniqueGames.Soundness.ExpectationComparisonLemmas
import OAI.Computability.UniqueGames.Soundness.LinearMapDensityLemmas
import OAI.Computability.UniqueGames.Soundness.PartnerLinearLemmas

namespace OAI

section

/-!
# Exact overlap bound for independently sampled uniform fixed-size subsets

All expectations below are explicit rational sums over `Finset.powersetCard`.
The marginal inclusion probability is derived from the exact binomial count
of subsets containing a prescribed singleton. No probabilistic estimate is an
assumption. This is the active-set overlap bound used in Lemma 6.3.
-/

namespace UniqueGamesTheorem.Soundness.SubsetIntersection

open scoped BigOperators

/-- The actual finite sample space of all `t`-subsets of `Fin k`. -/
def subsets (k t : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k)).powersetCard t

/-- Uniform expectation, implemented by its normalized finite sum. -/
def uniformMean (k t : ℕ) (f : Finset (Fin k) → ℚ) : ℚ :=
  (∑ a ∈ subsets k t, f a) / (subsets k t).card

/-- Independent draws use the product of the two uniform laws. -/
def independentMean (k t : ℕ) (f : Finset (Fin k) → Finset (Fin k) → ℚ) : ℚ :=
  uniformMean k t fun a => uniformMean k t fun b => f a b

def memberIndicator {k : ℕ} (i : Fin k) (a : Finset (Fin k)) : ℚ :=
  if i ∈ a then 1 else 0

def overlapProbability (k t : ℕ) : ℚ :=
  independentMean k t fun a b => if (a ∩ b).Nonempty then 1 else 0

/-- The nested expectations are exactly the normalized sum on the product
sample space, whose cardinality is the square of the single-draw cardinality. -/
theorem independentMean_eq_double_sum (k t : ℕ)
    (f : Finset (Fin k) → Finset (Fin k) → ℚ) :
    independentMean k t f =
      (∑ a ∈ subsets k t, ∑ b ∈ subsets k t, f a b) / ((subsets k t).card : ℚ)^2 := by
  unfold independentMean uniformMean
  simp only [div_eq_mul_inv, ← Finset.sum_mul, pow_two, mul_inv_rev]
  ring

theorem uniformMean_mul_left (k t : ℕ) (c : ℚ) (f : Finset (Fin k) → ℚ) :
    uniformMean k t (fun a => c * f a) = c * uniformMean k t f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

theorem uniformMean_mul_right (k t : ℕ) (c : ℚ) (f : Finset (Fin k) → ℚ) :
    uniformMean k t (fun a => f a * c) = uniformMean k t f * c := by
  unfold uniformMean
  rw [← Finset.sum_mul]
  ring

/-- Independence is proved from the actual two normalized finite sums. -/
theorem independentMean_product (k t : ℕ) (f g : Finset (Fin k) → ℚ) :
    independentMean k t (fun a b => f a * g b) = uniformMean k t f * uniformMean k t g := by
  simp only [independentMean, uniformMean_mul_left, uniformMean_mul_right]

theorem subsets_card (k t : ℕ) : (subsets k t).card = k.choose t := by
  simp [subsets]

theorem subsets_nonempty {k t : ℕ} (htk : t ≤ k) : (subsets k t).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr
  simpa using htk

theorem subsets_card_ne_zero {k t : ℕ} (htk : t ≤ k) :
    ((subsets k t).card : ℚ) ≠ 0 := by
  exact_mod_cast (Finset.card_ne_zero.mpr (subsets_nonempty htk))

/-- Count the sampled subsets containing one specified coordinate. -/
theorem count_containing {k t : ℕ} (ht : 0 < t) (i : Fin k) :
    ((subsets k t).filter (fun a => i ∈ a)).card =
      (k - 1).choose (t - 1) := by
  simpa [subsets] using
    (Finset.card_filter_powersetCard_subset ({i} : Finset (Fin k)) Finset.univ t
      (by simp) (by simpa using Nat.succ_le_of_lt ht))

theorem choose_predecessor_ratio {k t : ℕ} (hk : 0 < k) (ht : 0 < t) (htk : t ≤ k) :
    ((k - 1).choose (t - 1) : ℚ) / k.choose t = (t : ℚ) / k := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hc0 : (k.choose t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos htk))
  have hrel : k * (k - 1).choose (t - 1) = k.choose t * t := by
    simpa [Nat.sub_add_cancel hk, Nat.sub_add_cancel ht] using
      (Nat.add_one_mul_choose_eq (k - 1) (t - 1))
  apply (div_eq_div_iff hc0 hk0).2
  exact_mod_cast (by simpa [Nat.mul_comm] using hrel)

/-- Exact marginal probability: a coordinate belongs to a uniform `t`-subset
with probability `t / k`. This also includes `t = 0`. -/
theorem inclusion_probability {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) (i : Fin k) :
    uniformMean k t (memberIndicator i) = (t : ℚ) / k := by
  by_cases ht : t = 0
  · subst t
    simp [uniformMean, subsets, memberIndicator]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    unfold uniformMean memberIndicator
    rw [Finset.sum_boole, count_containing htpos i, subsets_card]
    exact choose_predecessor_ratio hk htpos htk

/-- A coordinate belongs to both independent draws with the product probability. -/
theorem independent_inclusion_probability {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) (i : Fin k) :
    independentMean k t (fun a b => memberIndicator i a * memberIndicator i b) =
      ((t : ℚ) / k)^2 := by
  rw [independentMean_product, inclusion_probability hk htk]
  ring

theorem uniformMean_congr {k t : ℕ} {f g : Finset (Fin k) → ℚ}
    (h : ∀ a ∈ subsets k t, f a = g a) : uniformMean k t f = uniformMean k t g := by
  unfold uniformMean
  rw [Finset.sum_congr rfl h]

theorem uniformMean_const {k t : ℕ} (htk : t ≤ k) (c : ℚ) :
    uniformMean k t (fun _ => c) = c := by
  have hn := subsets_card_ne_zero htk
  simp only [uniformMean, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem uniformMean_finset_sum {k t : ℕ} {α : Type*} (s : Finset α)
    (f : α → Finset (Fin k) → ℚ) :
    uniformMean k t (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, uniformMean k t (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem uniformMean_mono {k t : ℕ} {f g : Finset (Fin k) → ℚ}
    (h : ∀ a ∈ subsets k t, f a ≤ g a) : uniformMean k t f ≤ uniformMean k t g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum h)
  exact Nat.cast_nonneg _

theorem independentMean_mono {k t : ℕ} {f g : Finset (Fin k) → Finset (Fin k) → ℚ}
    (h : ∀ a ∈ subsets k t, ∀ b ∈ subsets k t, f a b ≤ g a b) :
    independentMean k t f ≤ independentMean k t g := by
  apply uniformMean_mono
  intro a ha
  apply uniformMean_mono
  exact h a ha

theorem intersection_card_indicator {k : ℕ} (a b : Finset (Fin k)) :
    ((a ∩ b).card : ℚ) = ∑ i ∈ a, memberIndicator i b := by
  simp [memberIndicator]

/-- Conditional expectation against any fixed first set, directly from the
proved marginal inclusion probability of the independent second draw. -/
theorem expected_intersection_fixed {k t : ℕ} (hk : 0 < k) (htk : t ≤ k)
    (a : Finset (Fin k)) :
    uniformMean k t (fun b => ((a ∩ b).card : ℚ)) = a.card * ((t : ℚ) / k) := by
  simp_rw [intersection_card_indicator]
  rw [uniformMean_finset_sum]
  simp [inclusion_probability hk htk, nsmul_eq_mul]

/-- Exact expected intersection size for independent uniform `t`-subsets. -/
theorem expected_intersection {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    independentMean k t (fun a b => ((a ∩ b).card : ℚ)) = (t : ℚ)^2 / k := by
  unfold independentMean
  simp_rw [expected_intersection_fixed hk htk]
  calc
    uniformMean k t (fun a => a.card * ((t : ℚ) / k)) =
        uniformMean k t (fun _ => (t : ℚ) * ((t : ℚ) / k)) := by
      apply uniformMean_congr
      intro a ha
      have hcard : a.card = t := (Finset.mem_powersetCard.mp ha).2
      rw [hcard]
    _ = (t : ℚ) * ((t : ℚ) / k) := uniformMean_const htk _
    _ = (t : ℚ)^2 / k := by ring

/-- The pointwise first-moment bound for a nonempty intersection. -/
theorem nonempty_indicator_le_card {k : ℕ} (a b : Finset (Fin k)) :
    (if (a ∩ b).Nonempty then (1 : ℚ) else 0) ≤ (a ∩ b).card := by
  split_ifs with h
  · exact_mod_cast (Finset.card_pos.mpr h)
  · exact Nat.cast_nonneg _

/-- The uniform-subset overlap bound used in the map-law comparison. -/
theorem overlap_probability_le {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    overlapProbability k t ≤ (t : ℚ)^2 / k := by
  calc
    overlapProbability k t ≤ independentMean k t (fun a b => ((a ∩ b).card : ℚ)) :=
      independentMean_mono (fun a _ b _ => nonempty_indicator_le_card a b)
    _ = (t : ℚ)^2 / k := expected_intersection hk htk

end UniqueGamesTheorem.Soundness.SubsetIntersection

end

section

namespace UniqueGamesTheorem.Soundness.PartnerSampling

open scoped BigOperators
open SubsetIntersection (subsets)

/-- The literal support of the uniform active-set sample. -/
abbrev ActiveSet (k t : ℕ) := ↥(subsets k t)

/-- Each retained coordinate receives an independent slot in `Fin 3`. -/
abbrev Partner (k t : ℕ) := Σ a : ActiveSet k t, (↥a.val → Fin 3)

theorem activeSet_card {k t : ℕ} (a : ActiveSet k t) : a.val.card = t :=
  (Finset.mem_powersetCard.mp a.property).2

theorem slotTuples_card {k t : ℕ} (a : ActiveSet k t) :
    Fintype.card (↥a.val → Fin 3) = 3 ^ t := by
  simp [activeSet_card a]

/-- Equal-size fibers prove that slot sampling does not change subset weights. -/
theorem partner_card (k t : ℕ) :
    Fintype.card (Partner k t) = (subsets k t).card * 3 ^ t := by
  rw [Fintype.card_sigma]
  simp only [slotTuples_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_coe, Nat.cast_id]

theorem partner_nonempty {k t : ℕ} (htk : t ≤ k) : Nonempty (Partner k t) := by
  obtain ⟨a, ha⟩ := SubsetIntersection.subsets_nonempty htk
  exact ⟨⟨⟨a, ha⟩, fun _ => 0⟩⟩

theorem uniformMean_real_cast (k t : ℕ) (f : Finset (Fin k) → ℚ) :
    (SubsetIntersection.uniformMean k t f : ℝ) =
      (𝔼 a ∈ subsets k t, (f a : ℝ)) := by
  rw [Finset.expect_eq_sum_div_card]
  simp [SubsetIntersection.uniformMean]

theorem independentMean_real_cast (k t : ℕ)
    (f : Finset (Fin k) → Finset (Fin k) → ℚ) :
    (SubsetIntersection.independentMean k t f : ℝ) =
      (𝔼 a ∈ subsets k t, 𝔼 b ∈ subsets k t, (f a b : ℝ)) := by
  simp only [SubsetIntersection.independentMean, uniformMean_real_cast]

/-- Real `Finset.expect` form of the already-proved rational subset bound. -/
theorem subset_overlap_probability_le {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    (𝔼 a ∈ subsets k t, 𝔼 b ∈ subsets k t,
      if (a ∩ b).Nonempty then (1 : ℝ) else 0) ≤ (t : ℝ)^2 / k := by
  have h : (SubsetIntersection.overlapProbability k t : ℝ) ≤ (t : ℝ)^2 / k := by
    have h := SubsetIntersection.overlap_probability_le hk htk
    have hh := (Rat.cast_le (K := ℝ)).mpr h
    simpa using hh
  simpa only [SubsetIntersection.overlapProbability, independentMean_real_cast,
    apply_ite, Rat.cast_one, Rat.cast_zero] using h

theorem activeSet_expect (k t : ℕ) (f : Finset (Fin k) → ℝ) :
    (𝔼 a : ActiveSet k t, f a.val) = (𝔼 a ∈ subsets k t, f a) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_coe,
    Finset.sum_coe_sort]

/-- The uniform full-partner law projects to the uniform active-subset law. -/
theorem partner_expect_activeSet (k t : ℕ) (f : ActiveSet k t → ℝ) :
    (𝔼 p : Partner k t, f p.1) = (𝔼 a : ActiveSet k t, f a) := by
  have hsum : (∑ p : Partner k t, f p.1) = (3 : ℝ)^t * ∑ a : ActiveSet k t, f a := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, slotTuples_card,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [Finset.mul_sum]
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, hsum, partner_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Fintype.card_coe]
  have hc : (3 : ℝ)^t ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa only [mul_comm] using
    (mul_div_mul_left (∑ a : ActiveSet k t, f a) ((subsets k t).card : ℝ) hc)

theorem partner_expect_active (k t : ℕ) (f : Finset (Fin k) → ℝ) :
    (𝔼 p : Partner k t, f p.1.val) = (𝔼 a ∈ subsets k t, f a) := by
  rw [partner_expect_activeSet k t (fun a => f a.val), activeSet_expect]

theorem partner_pair_expect_active (k t : ℕ)
    (f : Finset (Fin k) → Finset (Fin k) → ℝ) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t, f p.1.val q.1.val) =
      (𝔼 a ∈ subsets k t, 𝔼 b ∈ subsets k t, f a b) := by
  calc
    _ = 𝔼 p : Partner k t, 𝔼 b ∈ subsets k t, f p.1.val b := by
      apply Finset.expect_congr rfl
      intro p _
      exact partner_expect_active k t (fun b => f p.1.val b)
    _ = _ := partner_expect_active k t (fun a => 𝔼 b ∈ subsets k t, f a b)

/-- The independently drawn full partners obey the same active-overlap bound. -/
theorem partner_active_overlap_probability_le {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      if (p.1.val ∩ q.1.val).Nonempty then (1 : ℝ) else 0) ≤ (t : ℝ)^2 / k := by
  rw [partner_pair_expect_active k t (fun a b => if (a ∩ b).Nonempty then (1 : ℝ) else 0)]
  exact subset_overlap_probability_le hk htk

def active {k t : ℕ} (p : Partner k t) (j : Fin k) : Bool :=
  decide (j ∈ p.1.val)

def decodeSlot (i : Fin 3) : PartnerProjection.Slot :=
  if i.val = 0 then .first else if i.val = 1 then .second else .third

def slots {k t : ℕ} (p : Partner k t) (j : Fin k) : PartnerProjection.Slot :=
  if hj : j ∈ p.1.val then decodeSlot (p.2 ⟨j, hj⟩) else .first

noncomputable def kernel {k t : ℕ} (rhs : Fin k → Bool) (p : Partner k t) :
    Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs) :=
  (PartnerLinear.projection rhs (active p) (slots p)).ker

def activeSubtypeEquiv {k t : ℕ} (p : Partner k t) :
    PartnerLinear.Active (active p) ≃ ↥p.1.val :=
  Equiv.subtypeEquivRight (fun j => by simp [active])

theorem kernel_finrank {k t : ℕ} (rhs : Fin k → Bool) (p : Partner k t) :
    Module.finrank (ZMod 2) (kernel rhs p) = t := by
  rw [kernel, PartnerLinear.projection_ker_finrank]
  calc
    Fintype.card (PartnerLinear.Active (active p)) = Fintype.card ↥p.1.val :=
      Fintype.card_congr (activeSubtypeEquiv p)
    _ = t := by simpa using activeSet_card p.1

theorem kernel_inf_finrank_le {k t : ℕ} (rhs : Fin k → Bool) (p q : Partner k t) :
    Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)) ≤ t := by
  calc
    Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)) ≤
        Module.finrank (ZMod 2) (kernel rhs p) := Submodule.finrank_mono inf_le_left
    _ = t := kernel_finrank rhs p

theorem kernel_inf_eq_bot_of_no_overlap {k t : ℕ}
    (rhs : Fin k → Bool) (p q : Partner k t)
    (h : ¬ (p.1.val ∩ q.1.val).Nonempty) :
    kernel rhs p ⊓ kernel rhs q = ⊥ := by
  apply PartnerLinear.disjoint_projection_kernels
    rhs (active p) (slots p) (active q) (slots q)
  intro j hj
  have hp : j ∈ p.1.val := by simpa [active] using hj
  have hq : j ∉ q.1.val := by
    intro hq
    exact h ⟨j, Finset.mem_inter.mpr ⟨hp, hq⟩⟩
  simp [active, hq]

def activeOverlap {k t : ℕ} (p q : Partner k t) : ℝ :=
  if (p.1.val ∩ q.1.val).Nonempty then 1 else 0

noncomputable def kernelCollision {k t : ℕ}
    (rhs : Fin k → Bool) (p q : Partner k t) : ℝ := by
  classical
  exact if kernel rhs p ⊓ kernel rhs q ≠ ⊥ then 1 else 0

theorem kernelCollision_le_activeOverlap {k t : ℕ}
    (rhs : Fin k → Bool) (p q : Partner k t) :
    kernelCollision rhs p q ≤ activeOverlap p q := by
  classical
  by_cases h : (p.1.val ∩ q.1.val).Nonempty
  · simp only [activeOverlap, ite_eq_left h, kernelCollision]
    split_ifs <;> norm_num
  · have hb := kernel_inf_eq_bot_of_no_overlap rhs p q h
    simp [kernelCollision, activeOverlap, h, hb]

theorem kernel_collision_probability_le {k t : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      kernelCollision rhs p q) ≤ (t : ℝ)^2 / k := by
  calc
    (𝔼 p : Partner k t, 𝔼 q : Partner k t, kernelCollision rhs p q) ≤
        (𝔼 p : Partner k t, 𝔼 q : Partner k t, activeOverlap p q) := by
      apply Finset.expect_le_expect
      intro p _
      apply Finset.expect_le_expect
      intro q _
      exact kernelCollision_le_activeOverlap rhs p q
    _ ≤ (t : ℝ)^2 / k := partner_active_overlap_probability_le hk htk

theorem kernel_overlap_weight_pointwise {k t : ℕ}
    (rhs : Fin k → Bool) (m : ℕ) (p q : Partner k t) :
    (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs))) ≤
      1 + activeOverlap p q * (2 : ℝ) ^ (m * t) := by
  have hcap :
      (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs))) ≤
        (2 : ℝ) ^ (m * t) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact Nat.mul_le_mul_left m (kernel_inf_finrank_le rhs p q)
  by_cases h : (p.1.val ∩ q.1.val).Nonempty
  · simp only [activeOverlap, ite_eq_left h, one_mul]
    linarith
  · have hb := kernel_inf_eq_bot_of_no_overlap rhs p q h
    rw [hb]
    simp [activeOverlap, h]

theorem kernel_overlap_weight_le {k t : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool) (m : ℕ) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)))) ≤
      1 + ((t : ℝ)^2 / k) * (2 : ℝ) ^ (m * t) := by
  let : Nonempty (Partner k t) := partner_nonempty htk
  have hmean :
      (𝔼 p : Partner k t, 𝔼 q : Partner k t,
        (1 + activeOverlap p q * (2 : ℝ) ^ (m * t))) =
      1 + (𝔼 p : Partner k t, 𝔼 q : Partner k t, activeOverlap p q) *
        (2 : ℝ) ^ (m * t) := by
    simp_rw [Finset.expect_add_distrib, ← Finset.expect_mul, Fintype.expect_const]
  calc
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)))) ≤
        (𝔼 p : Partner k t, 𝔼 q : Partner k t,
          (1 + activeOverlap p q * (2 : ℝ) ^ (m * t))) := by
      apply Finset.expect_le_expect
      intro p _
      apply Finset.expect_le_expect
      intro q _
      exact kernel_overlap_weight_pointwise rhs m p q
    _ = 1 + (𝔼 p : Partner k t, 𝔼 q : Partner k t, activeOverlap p q) *
        (2 : ℝ) ^ (m * t) := hmean
    _ ≤ 1 + ((t : ℝ)^2 / k) * (2 : ℝ) ^ (m * t) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right
      · exact partner_active_overlap_probability_le hk htk
      · exact pow_nonneg (by norm_num) _

end UniqueGamesTheorem.Soundness.PartnerSampling

end

section

/-! Lemma 6.3 for the actual independently sampled partner maps. -/

namespace UniqueGamesTheorem.Soundness.ActualMapComparison
open LinearMapDensity PartnerProjection PartnerSampling

theorem actual_partner_expectation_comparison {k t : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [Fintype (SourcePoint rhs →ₗ[ZMod 2] R)]
    [∀ p : Partner k t, Fintype (PartnerPoint rhs (active p) →ₗ[ZMod 2] R)]
    (H : (SourcePoint rhs →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1) :
    |uniformMean (fun p : Partner k t =>
        uniformMean (fun B : PartnerPoint rhs (active p) →ₗ[ZMod 2] R =>
          H (B.comp (PartnerLinear.projection rhs (active p) (slots p))))) - uniformMean H| ≤
      Real.sqrt (((t : ℝ)^2 / k) * (2 : ℝ)^(Module.finrank (ZMod 2) R * t)) := by
  let : Nonempty (Partner k t) := partner_nonempty htk
  have hsecond :
      uniformMean (fun M : SourcePoint rhs →ₗ[ZMod 2] R =>
        (mixtureDensity (kernel (t := t) rhs) M)^2) ≤
      1 + ((t : ℝ)^2 / k) * (2 : ℝ)^(Module.finrank (ZMod 2) R * t) := by
    rw [mixtureDensity_second_moment]
    exact kernel_overlap_weight_le hk htk rhs (Module.finrank (ZMod 2) R)
  have hc := ExpectationComparison.bounded_test_expectation_comparison
    Finset.univ Finset.univ_nonempty (mixtureDensity (R := R) (kernel (t := t) rhs)) H
    (((t : ℝ)^2 / k) * (2 : ℝ)^(Module.finrank (ZMod 2) R * t))
    (mixtureDensity_mean (R := R) (kernel (t := t) rhs)) hsecond (fun M _ => hH M)
  rw [mixture_pullback_uniformMean
    (fun p : Partner k t => PartnerLinear.projection rhs (active p) (slots p))
    (fun p => PartnerLinear.projection_surjective rhs (active p) (slots p)) H]
  have hkernel : kernel (t := t) rhs =
      (fun p : Partner k t => (PartnerLinear.projection rhs (active p) (slots p)).ker) := rfl
  rw [hkernel] at hc
  simpa only [uniformMean, mul_comm] using hc

theorem actual_partner_expectation_comparison_dimension {k t L : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [Fintype (SourcePoint rhs →ₗ[ZMod 2] R)]
    [∀ p : Partner k t, Fintype (PartnerPoint rhs (active p) →ₗ[ZMod 2] R)]
    (H : (SourcePoint rhs →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1)
    (hm : Module.finrank (ZMod 2) R ≤ L) :
    |uniformMean (fun p : Partner k t =>
        uniformMean (fun B : PartnerPoint rhs (active p) →ₗ[ZMod 2] R =>
          H (B.comp (PartnerLinear.projection rhs (active p) (slots p))))) - uniformMean H| ≤
      Real.sqrt (((t : ℝ)^2 / k) * (2 : ℝ)^(t * L)) := by
  have he : Module.finrank (ZMod 2) R * t ≤ t * L := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right t hm
  have hp : (2 : ℝ)^(Module.finrank (ZMod 2) R * t) ≤ (2 : ℝ)^(t*L) :=
    pow_le_pow_right₀ (by norm_num) he
  exact (actual_partner_expectation_comparison hk htk rhs H hH).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hp
      (div_nonneg (sq_nonneg (t : ℝ)) (Nat.cast_nonneg k))))

theorem actual_partner_expectation_quarter {k t L : ℕ} {θ : ℚ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [Fintype (SourcePoint rhs →ₗ[ZMod 2] R)]
    [∀ p : Partner k t, Fintype (PartnerPoint rhs (active p) →ₗ[ZMod 2] R)]
    (H : (SourcePoint rhs →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1)
    (hm : Module.finrank (ZMod 2) R ≤ L) (hθ : 0 ≤ θ)
    (budget : 16 * (t : ℚ)^2 * 2^(t*L) ≤ (k : ℚ)*θ^2) :
    |uniformMean (fun p : Partner k t =>
        uniformMean (fun B : PartnerPoint rhs (active p) →ₗ[ZMod 2] R =>
          H (B.comp (PartnerLinear.projection rhs (active p) (slots p))))) - uniformMean H| ≤
      (θ : ℝ) / 4 :=
  (actual_partner_expectation_comparison_dimension hk htk rhs H hH hm).trans
    (ExpectationComparison.comparison_error_le_quarter _ _ (by exact_mod_cast hθ)
      (Integration.RealBounds.comparison_square_budget hk budget))

end UniqueGamesTheorem.Soundness.ActualMapComparison

end

section

/-!
# Full slot indices and the actual partner law

Uniform indices at all positions restrict to uniform indices on an active set.
The explicit restriction/complement equivalence proves this sampling fact. The
dependent partner average then equals sampling the active set followed by all
slot indices, including unused indices outside the active set. Finally, the
coordinatewise occurrence/slot draw is related to that same law.
-/

namespace UniqueGamesTheorem.Soundness.PartnerFullSampling

open scoped BigOperators
open PartnerSampling

noncomputable section

def restrictIndices {P X : Type*} (J : Finset P) (indices : P → X) : ↥J → X :=
  fun j => indices j.val

/-- The values inside and outside a finite set reconstruct the full tuple. -/
def restrictionProductEquiv {P X : Type*} [DecidableEq P] (J : Finset P) :
    (P → X) ≃ ((↥J → X) × ({j : P // j ∉ J} → X)) where
  toFun indices := (restrictIndices J indices, fun j => indices j.val)
  invFun parts := fun j =>
    if hj : j ∈ J then parts.1 ⟨j, hj⟩ else parts.2 ⟨j, hj⟩
  left_inv indices := by
    funext j
    by_cases hj : j ∈ J <;> simp [restrictIndices, hj]
  right_inv parts := by
    apply Prod.ext
    · funext j
      simp [restrictIndices, j.property]
    · funext j
      simp [j.property]

/-- Marginalizing the nonempty complement tuple gives the exact uniform law
on the active coordinates. This includes an empty active set or complement. -/
theorem expect_restrictIndices {P X : Type*} [Fintype P] [DecidableEq P]
    [Fintype X] [Nonempty X] (J : Finset P) (h : (↥J → X) → ℝ) :
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
      𝔼 activeIndices : ↥J → X, h activeIndices := by
  calc
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
        𝔼 parts : (↥J → X) × ({j : P // j ∉ J} → X), h parts.1 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = 𝔼 activeIndices : ↥J → X, h activeIndices := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (↥J → X))
          (Finset.univ : Finset ({j : P // j ∉ J} → X))
          (fun parts => h parts.1))

def fromFullIndices {k t : ℕ} (a : ActiveSet k t) (indices : Fin k → Fin 3) :
    Partner k t := ⟨a, restrictIndices a.val indices⟩

/-- Fixed-active-set form of the actual three-way slot sampling identity. -/
theorem fixed_active_expect_fullIndices {k t : ℕ} (a : ActiveSet k t)
    (h : (↥a.val → Fin 3) → ℝ) :
    (𝔼 indices : Fin k → Fin 3, h (restrictIndices a.val indices)) =
      𝔼 activeIndices : ↥a.val → Fin 3, h activeIndices :=
  expect_restrictIndices a.val h

/-- All active-set fibers have `3^t` elements, so the uniform dependent-pair
average is the active-set average of the uniform slot average. -/
theorem partner_expect_active_slots (k t : ℕ) (f : Partner k t → ℝ) :
    (𝔼 p : Partner k t, f p) =
      𝔼 a : ActiveSet k t, 𝔼 indices : ↥a.val → Fin 3, f ⟨a, indices⟩ := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.sum_sigma,
    slotTuples_card, partner_card, Fintype.card_coe,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

/-- The full-index experiment has exactly the existing `Partner` law.
No independence or equality of probability laws is assumed. -/
theorem partner_expect_fullIndices (k t : ℕ) (f : Partner k t → ℝ) :
    (𝔼 p : Partner k t, f p) =
      𝔼 a : ActiveSet k t, 𝔼 indices : Fin k → Fin 3,
        f (fromFullIndices a indices) := by
  rw [partner_expect_active_slots]
  apply Finset.expect_congr rfl
  intro a _
  exact (fixed_active_expect_fullIndices a (fun indices => f ⟨a, indices⟩)).symm

/-- Slots outside active positions have no effect on the genuine projection. -/
theorem projection_eq_of_slots_eq_on_active {P : Type}
    (rhs active : P → Bool) (slot slot' : P → PartnerProjection.Slot)
    (hslot : ∀ j, active j = true → slot j = slot' j) :
    PartnerLinear.projection rhs active slot =
      PartnerLinear.projection rhs active slot' := by
  apply LinearMap.ext
  intro x
  change PartnerProjection.project rhs active slot x =
    PartnerProjection.project rhs active slot' x
  apply PartnerProjection.partner_ext rhs active
  · rfl
  · rfl
  · funext j
    by_cases hj : active j = true
    · simp [PartnerProjection.project, hj, hslot j hj]
    · simp [PartnerProjection.project, hj]

/-- Defaulting inactive slots to `.first` gives the same map as retaining all
the independently sampled full indices. -/
theorem projection_fromFullIndices {k t : ℕ} (rhs : Fin k → Bool)
    (a : ActiveSet k t) (indices : Fin k → Fin 3) :
    PartnerLinear.projection rhs (active (fromFullIndices a indices))
        (slots (fromFullIndices a indices)) =
      PartnerLinear.projection rhs (active (fromFullIndices a indices))
        (fun j => decodeSlot (indices j)) := by
  apply projection_eq_of_slots_eq_on_active
  intro j hj
  have hmem : j ∈ a.val := by
    change decide (j ∈ a.val) = true at hj
    exact of_decide_eq_true hj
  simp [slots, fromFullIndices, restrictIndices, hmem]

/-- Drawing an occurrence and a slot at each position is the same finite
sample space as drawing the occurrence tuple and the slot tuple separately. -/
def drawProductEquiv {P Id : Type*} :
    (P → Id × Fin 3) ≃ ((P → Id) × (P → Fin 3)) where
  toFun draw := (fun j => (draw j).1, fun j => (draw j).2)
  invFun parts := fun j => (parts.1 j, parts.2 j)
  left_inv draw := by funext j; rfl
  right_inv parts := by
    apply Prod.ext <;> funext j <;> rfl

/-- The raw occurrence/slot draw induces independent uniform occurrences and
uniform active slots, with all unused slot choices marginalized exactly. -/
theorem fixed_active_rawDraw_expect {k t : ℕ} {Id : Type*} [Fintype Id]
    (a : ActiveSet k t)
    (f : (Fin k → Id) → (↥a.val → Fin 3) → ℝ) :
    (𝔼 draw : Fin k → Id × Fin 3,
      f (fun j => (draw j).1)
        (restrictIndices a.val (fun j => (draw j).2))) =
      𝔼 occurrence : Fin k → Id, 𝔼 indices : ↥a.val → Fin 3,
        f occurrence indices := by
  calc
    (𝔼 draw : Fin k → Id × Fin 3,
        f (fun j => (draw j).1)
          (restrictIndices a.val (fun j => (draw j).2))) =
        𝔼 parts : (Fin k → Id) × (Fin k → Fin 3),
          f parts.1 (restrictIndices a.val parts.2) :=
      Fintype.expect_equiv drawProductEquiv _ _ (fun _ => rfl)
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 indices : Fin k → Fin 3,
        f occurrence (restrictIndices a.val indices) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product (Finset.univ : Finset (Fin k → Id))
          (Finset.univ : Finset (Fin k → Fin 3))
          (fun parts => f parts.1 (restrictIndices a.val parts.2)))
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 indices : ↥a.val → Fin 3,
        f occurrence indices := by
      apply Finset.expect_congr rfl
      intro occurrence _
      exact fixed_active_expect_fullIndices a (f occurrence)

/-- The actual raw draw, including indices outside the active set, agrees
with the occurrence-then-partner experiment for every real test function. -/
theorem occurrence_partner_expect_eq_rawDraw (k t : ℕ)
    {Id : Type*} [Fintype Id] (f : (Fin k → Id) → Partner k t → ℝ) :
    (𝔼 occurrence : Fin k → Id, 𝔼 p : Partner k t, f occurrence p) =
      𝔼 a : ActiveSet k t, 𝔼 draw : Fin k → Id × Fin 3,
        f (fun j => (draw j).1) (fromFullIndices a (fun j => (draw j).2)) := by
  symm
  calc
    (𝔼 a : ActiveSet k t, 𝔼 draw : Fin k → Id × Fin 3,
        f (fun j => (draw j).1) (fromFullIndices a (fun j => (draw j).2))) =
        𝔼 a : ActiveSet k t, 𝔼 occurrence : Fin k → Id,
          𝔼 indices : ↥a.val → Fin 3, f occurrence ⟨a, indices⟩ := by
      apply Finset.expect_congr rfl
      intro a _
      exact fixed_active_rawDraw_expect a (fun occurrence indices => f occurrence ⟨a, indices⟩)
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 a : ActiveSet k t,
        𝔼 indices : ↥a.val → Fin 3, f occurrence ⟨a, indices⟩ :=
      Finset.expect_comm _ _ _
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 p : Partner k t, f occurrence p := by
      apply Finset.expect_congr rfl
      intro occurrence _
      exact (partner_expect_active_slots k t (f occurrence)).symm

end

end UniqueGamesTheorem.Soundness.PartnerFullSampling

end

section

namespace UniqueGamesTheorem.Soundness.ActualMapComparison

def sourcePrecomposeEquiv {A E R : Type}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup R] [Module (ZMod 2) R] (e : A ≃ₗ[ZMod 2] E) :
    (E →ₗ[ZMod 2] R) ≃ (A →ₗ[ZMod 2] R) where
  toFun M := M.comp e.toLinearMap
  invFun M := M.comp e.symm.toLinearMap
  left_inv M := by
    apply LinearMap.ext
    intro x
    change M (e (e.symm x)) = M x
    rw [e.apply_symm_apply]
  right_inv M := by
    apply LinearMap.ext
    intro x
    change M (e.symm (e x)) = M x
    rw [e.symm_apply_apply]

theorem uniformMean_sourcePrecompose {A E R : Type}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup R] [Module (ZMod 2) R]
    [Fintype (A →ₗ[ZMod 2] R)] [Fintype (E →ₗ[ZMod 2] R)]
    (e : A ≃ₗ[ZMod 2] E) (H : (E →ₗ[ZMod 2] R) → ℝ) :
    LinearMapDensity.uniformMean (fun M : A →ₗ[ZMod 2] R =>
      H (M.comp e.symm.toLinearMap)) = LinearMapDensity.uniformMean H := by
  simpa only [LinearMapDensity.uniformMean] using
    (Fintype.expect_equiv (sourcePrecomposeEquiv e).symm
      (fun M : A →ₗ[ZMod 2] R => H (M.comp e.symm.toLinearMap)) H (fun _ => rfl))

theorem actual_partner_expectation_quarter_equiv {k t L : ℕ} {θ : ℚ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool)
    {R E : Type} [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]
    [AddCommGroup E] [Module (ZMod 2) E]
    [Fintype (PartnerProjection.SourcePoint rhs →ₗ[ZMod 2] R)]
    [Fintype (E →ₗ[ZMod 2] R)]
    [∀ p : PartnerSampling.Partner k t,
      Fintype (PartnerProjection.PartnerPoint rhs (PartnerSampling.active p) →ₗ[ZMod 2] R)]
    (e : PartnerProjection.SourcePoint rhs ≃ₗ[ZMod 2] E)
    (H : (E →ₗ[ZMod 2] R) → ℝ) (hH : ∀ M, |H M| ≤ 1)
    (hm : Module.finrank (ZMod 2) R ≤ L) (hθ : 0 ≤ θ)
    (budget : 16 * (t : ℚ)^2 * 2^(t*L) ≤ (k : ℚ) * θ^2) :
    |LinearMapDensity.uniformMean (fun p : PartnerSampling.Partner k t =>
        LinearMapDensity.uniformMean (fun B :
          PartnerProjection.PartnerPoint rhs (PartnerSampling.active p) →ₗ[ZMod 2] R =>
          H (B.comp ((PartnerLinear.projection rhs (PartnerSampling.active p)
            (PartnerSampling.slots p)).comp e.symm.toLinearMap)))) -
      LinearMapDensity.uniformMean H| ≤ (θ : ℝ) / 4 := by
  let Hcanon : (PartnerProjection.SourcePoint rhs →ₗ[ZMod 2] R) → ℝ :=
    fun M => H (M.comp e.symm.toLinearMap)
  have hcanon := actual_partner_expectation_quarter hk htk rhs Hcanon
    (fun M => hH (M.comp e.symm.toLinearMap)) hm hθ budget
  have hmean : LinearMapDensity.uniformMean Hcanon = LinearMapDensity.uniformMean H :=
    uniformMean_sourcePrecompose e H
  rw [hmean] at hcanon
  simpa only [Hcanon, LinearMap.comp_assoc] using hcanon

end UniqueGamesTheorem.Soundness.ActualMapComparison

end

section

/-! Exact finite uniform conditioning and total expectation, including empty fibres. -/

namespace UniqueGamesTheorem.Soundness.UniformPartition
open scoped BigOperators
noncomputable section

def mean {Ω : Type} [Fintype Ω] (g : Ω → ℝ) : ℝ :=
  (∑ ω, g ω) / Fintype.card Ω

theorem mean_equiv {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    (e : Ω ≃ Γ) (g : Γ → ℝ) : mean (fun ω => g (e ω)) = mean g := by
  unfold mean
  rw [e.sum_comp, Fintype.card_congr e]

def fiberSum {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) (g : Ω → ℝ) : ℝ :=
  ∑ ω, if f ω = h then g ω else 0

def fiberSize {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) : ℝ := fiberSum f h (fun _ => 1)

theorem fiberSize_eq_card {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) :
    fiberSize f h = ((Finset.univ.filter (fun ω => f ω = h)).card : ℝ) := by
  classical
  unfold fiberSize fiberSum
  rw [← Finset.sum_filter]
  simp

theorem sum_fiberSum {Ω H : Type} [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) :
    (∑ h, fiberSum f h g) = ∑ ω, g ω := by
  unfold fiberSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem fiberSize_mul {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (b : H → ℝ) (h : H) :
    fiberSize f h * b h = fiberSum f h (fun ω => b (f ω)) := by
  unfold fiberSize fiberSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : f ω = h <;> simp [hω]

theorem fiberSize_pos {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (h : H) (hh : ∃ ω, f ω = h) : 0 < fiberSize f h := by
  classical
  obtain ⟨ω, hω⟩ := hh
  rw [fiberSize_eq_card]
  have hc : 0 < (Finset.univ.filter (fun ω => f ω = h)).card :=
    Finset.card_pos.mpr ⟨ω, by simp [hω]⟩
  exact_mod_cast hc

theorem fiberSize_mul_conditional {Ω H : Type} [Fintype Ω] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) (h : H) :
    fiberSize f h * (fiberSum f h g / fiberSize f h) = fiberSum f h g := by
  classical
  by_cases hh : ∃ ω, f ω = h
  · have hn : fiberSize f h ≠ 0 := ne_of_gt (fiberSize_pos f h hh)
    field_simp [hn]
  · have hz : ∀ ω, f ω ≠ h := fun ω hω => hh ⟨ω, hω⟩
    simp [fiberSize, fiberSum, hz]

theorem total_mean {Ω H : Type} [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) :
    mean g = mean (fun ω => fiberSum f (f ω) g / fiberSize f (f ω)) := by
  let b : H → ℝ := fun h => fiberSum f h g / fiberSize f h
  change mean g = mean (fun ω => b (f ω))
  unfold mean
  apply congrArg (fun x : ℝ => x / (Fintype.card Ω : ℝ))
  calc
    (∑ ω, g ω) = ∑ h, fiberSum f h g := (sum_fiberSum f g).symm
    _ = ∑ h, fiberSize f h * b h := by
      apply Finset.sum_congr rfl
      intro h _
      exact (fiberSize_mul_conditional f g h).symm
    _ = ∑ h, fiberSum f h (fun ω => b (f ω)) := by
      apply Finset.sum_congr rfl
      intro h _
      exact fiberSize_mul f b h
    _ = ∑ ω, b (f ω) := sum_fiberSum f (fun ω => b (f ω))

theorem mean_mono {Ω : Type} [Fintype Ω] {g g' : Ω → ℝ}
    (h : ∀ ω, g ω ≤ g' ω) : mean g ≤ mean g' := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem mean_le_partition_bound {Ω H : Type}
    [Fintype Ω] [Fintype H] [DecidableEq H]
    (f : Ω → H) (g : Ω → ℝ) (bound : H → ℝ)
    (hlocal : ∀ h, (∃ ω, f ω = h) →
      fiberSum f h g / fiberSize f h ≤ bound h) :
    mean g ≤ mean (fun ω => bound (f ω)) := by
  calc
    mean g = mean (fun ω => fiberSum f (f ω) g / fiberSize f (f ω)) := total_mean f g
    _ ≤ mean (fun ω => bound (f ω)) := mean_mono (fun ω => hlocal (f ω) ⟨ω,rfl⟩)

theorem fiber_conditional_eq_subtype_mean {Ω H : Type}
    [Fintype Ω] [DecidableEq H] (f : Ω → H) (h : H) (g : Ω → ℝ) :
    fiberSum f h g / fiberSize f h =
      mean (fun ω : {ω // f ω = h} => g ω.val) := by
  classical
  simp only [fiberSum, fiberSize, mean]
  congr 1
  · rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun ω => by simp) g
  · rw [← Finset.sum_filter]
    simp [Fintype.card_subtype]

end
end UniqueGamesTheorem.Soundness.UniformPartition

end

end OAI
