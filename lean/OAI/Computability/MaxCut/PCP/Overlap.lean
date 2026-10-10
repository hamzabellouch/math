import Mathlib
import OAI.Computability.MaxCut.Games.GamesAdapter
import OAI.Computability.MaxCut.PCP.Variation
import OAI.Computability.MaxCut.Games.Kernels

namespace OAI

noncomputable section

/-!
Direct diagonal-overlap comparison for the finite correlated sampler.
All quantities are finite weight arrays; no reference sampler or embedding
claim is assumed. The final theorem consumes the per-label lower bound that
is proved for the actual finite threshold sampler in CorrelatedSampling.
-/

namespace MaxCutGames.Foundations.Repetition

section

open scoped BigOperators
open Information

private theorem min_half_formula_inline_Overlap (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula_inline_Overlap]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

private theorem discount_le_self_inline_Overlap {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

private theorem discount_loss_le_mul_inline_Overlap {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c - c / (1 + t) ≤ c * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : c - c / (1 + t) = c * t / (1 + t) := by
    field_simp [hd.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

/-- The direct common-mass argument, with its exact finite-array premises. -/
theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul_inline_Overlap (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self_inline_Overlap (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

/-- The per-label diagonal guarantee implies direct TV control even when the
target's question marginal differs from the simulator's question marginal. -/
theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self_inline_Overlap hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

open scoped BigOperators
open Games

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

/-- The law of the two local outputs, driven by a seed chosen independently
of the question pair. Local maps receive only their own question. -/
def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

/-- The published per-label estimate now concerns the actual finite game-law
sampler with a shared seed independent of the input questions. -/
theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

/-- Actual finite shared sampler approximates any prescribed diagonal law.
Its error is derived from the two actual conditional profiles and its uniform
finite exhaustion probability. -/
theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩

end MaxCutGames.Foundations.Repetition

/-!
Correlated rounding of finite partial assignments of equal density. A common
finite list of seeds is scanned locally at every vertex. An edge succeeds when
the first seed accepted by either endpoint is a jointly accepted good seed.
The finite truncation error is at most `(1 - density)^n`. Maximizing over the finite
set of deterministic labelings removes that error. No infinite random seed or
assumed rounding principle is used.
-/

namespace MaxCutGames.Repetition

section

open MaxCutGames.Foundations.Games
open MaxCutGames.Foundations.CorrelatedSampling
open MaxCutGames.Foundations.Repetition
open scoped BigOperators

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

def partialPairMass (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool) (x y : V) : ℝ :=
  μ.probability (fun s => accept x s && accept y s && R x y (label x s) (label y s))

def partialEdgeMass {E : Type*} (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (left right : E → V) (R : E → A → A → Bool) (e : E) : ℝ :=
  μ.probability (fun s => accept (left e) s && accept (right e) s &&
    R e (label (left e) s) (label (right e) s))

def partialLabelScore {E : Type*} [Fintype E] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool) (f : V → A) : ℝ :=
  ν.probability (fun e => R e (f (left e)) (f (right e)))

def partialSample (accept : V → S → Bool) (label : V → S → A)
    (fallback : A) (proposals : List S) (v : V) : A :=
  localSample (accept v) (label v) fallback proposals

private theorem expectation_mono_inline_RoundingSampling' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const_inline_RoundingSampling' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  simp [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized]

omit [Fintype V] [Fintype S] [Fintype A] in
private theorem first_good_relation_le_inline_RoundingSampling (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool)
    (fallback : A) (x y : V) (proposals : List S) :
    goodFirstIndicator (fun s => accept x s || accept y s)
      (fun s => accept x s && accept y s && R x y (label x s) (label y s)) proposals ≤
    (if R x y (partialSample accept label fallback proposals x)
      (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  cases hfirst : firstAccepted (fun s => accept x s || accept y s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      split <;> norm_num
  | some s =>
      by_cases hg : (accept x s && accept y s && R x y (label x s) (label y s)) = true
      · have hp : (accept x s = true ∧ accept y s = true) ∧
            R x y (label x s) (label y s) = true := by simpa using hg
        have hs := first_union_common (accept x) (accept y) proposals s hfirst hp.1.1 hp.1.2
        simp [goodFirstIndicator, hfirst, partialSample, localSample,
          hs.1, hs.2, hp.1.1, hp.1.2, hp.2]
      · simp only [goodFirstIndicator, hfirst, hg, Bool.false_eq_true, ite_false]
        split <;> norm_num

omit [Fintype V] [Fintype A] in
private theorem partial_mass_bounds_inline_RoundingSampling (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (density : ℝ)
    (hdensity : ∀ v, μ.probability (accept v) = density) (x y : V) :
    0 ≤ partialPairMass μ accept label R x y ∧
    partialPairMass μ accept label R x y ≤ density ∧
    density ≤ μ.probability (fun s => accept x s || accept y s) ∧
    μ.probability (fun s => accept x s || accept y s) +
      partialPairMass μ accept label R x y ≤ 2 * density := by
  refine ⟨μ.probability_nonnegative _, ?_, ?_, ?_⟩
  · rw [← hdensity x]
    apply μ.probability_mono
    intro s hs
    have hp : (accept x s = true ∧ accept y s = true) ∧
        R x y (label x s) (label y s) = true := by simpa using hs
    exact hp.1.1
  · rw [← hdensity x]
    exact μ.probability_mono (fun s hs => by simp [hs])
  · calc
      _ ≤ μ.probability (accept x) + μ.probability (accept y) := by
        unfold partialPairMass FiniteDistribution.probability
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro s _
        cases hx : accept x s <;> cases hy : accept y s <;>
          cases hr : R x y (label x s) (label y s) <;>
          simp [hx, hy, hr] ; linarith [μ.nonnegative s]
      _ = 2 * density := by rw [hdensity x, hdensity y]; ring

private theorem partial_ratio_bound_inline_RoundingSampling {g u density : ℝ} (hdensity : 0 < density)
    (hg : 0 ≤ g) (_hgl : g ≤ density) (hlu : density ≤ u) (hug : u + g ≤ 2 * density) :
    2 * (g / density) - 1 ≤ g / u := by
  have hu : 0 < u := lt_of_lt_of_le hdensity hlu
  apply (le_div_iff₀ hu).2
  by_cases hsgn : 2 * (g / density) - 1 ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hsgn hu.le).trans hg
  · have hcoeff : 0 ≤ 2 * g - density := by
      have hd : 1 < 2 * g / density := by
        rw [mul_div_assoc]
        linarith
      have := (lt_div_iff₀ hdensity).mp hd
      linarith
    have hm := mul_le_mul_of_nonneg_left hug hcoeff
    have heq : (2 * (g / density) - 1) * u = ((2 * g - density) * u) / density := by
      field_simp [ne_of_gt hdensity]

    rw [heq]
    apply (div_le_iff₀ hdensity).2
    nlinarith [sq_nonneg (density - g)]

omit [Fintype V] [Fintype A] in
/-- Pointwise success bound for the actual shared finite first-accept sampler.
The relation may depend on the ordered pair and need not be symmetric. -/
theorem partialSample_pair_lower (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (fallback : A) (density : ℝ)
    (hdensity₀ : 0 < density) (hdensity : ∀ v, μ.probability (accept v) = density)
    (x y : V) (n : Nat) :
    2 * (partialPairMass μ accept label R x y / density) - 1 - (1 - density) ^ n ≤
      traceAverage μ.weight n (fun proposals =>
        if R x y (partialSample accept label fallback proposals x)
          (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  let union : S → Bool := fun s => accept x s || accept y s
  let good : S → Bool := fun s =>
    accept x s && accept y s && R x y (label x s) (label y s)
  obtain ⟨hg, hgl, hlu, hug⟩ := partial_mass_bounds_inline_RoundingSampling μ accept label R density hdensity x y
  have hu : 0 < eventMass μ.weight union := lt_of_lt_of_le hdensity₀ hlu
  have hm : eventMass μ.weight (fun s => union s && good s) =
      partialPairMass μ accept label R x y := by
    unfold eventMass partialPairMass FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro s _
    cases hx : accept x s <;> cases hy : accept y s <;> simp [union, good, hx, hy]
  have hfirst := goodFirstMass_lower_bound μ.weight union good
    μ.nonnegative μ.normalized hu n
  rw [hm] at hfirst
  have hactual := traceAverage_mono μ.weight μ.nonnegative n _ _
    (first_good_relation_le_inline_RoundingSampling accept label R fallback x y)
  rw [goodFirstIndicator_law μ.weight _ _ μ.normalized n] at hactual
  have hcompl := eventMass_complement μ.weight union μ.normalized
  have hre : eventMass μ.weight (fun s => !(union s)) ≤ 1 - density := by
    change density ≤ eventMass μ.weight union at hlu
    linarith
  have hp := pow_le_pow_left₀
    (eventMass_nonneg μ.weight (fun s => !(union s)) μ.nonnegative) hre n
  have hr := partial_ratio_bound_inline_RoundingSampling hdensity₀ hg hgl hlu hug
  change 2 * (partialPairMass μ accept label R x y / density) - 1 ≤
    partialPairMass μ accept label R x y / eventMass μ.weight union at hr
  change goodFirstMass μ.weight union good n ≤ _ at hactual
  linarith

private theorem expectation_partial_lower_inline_RoundingSampling {E : Type*} [Fintype E]
    (ν : FiniteDistribution E) (g : E → ℝ) (density tail : ℝ) :
    ν.expectation (fun xy => 2 * (g xy / density) - 1 - tail) =
      2 * (ν.expectation g / density) - 1 - tail := by
  unfold FiniteDistribution.expectation
  calc
    _ = ∑ xy, (2 / density * (ν.weight xy * g xy) - (1 + tail) * ν.weight xy) := by
      apply Finset.sum_congr rfl
      intro xy _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ν.normalized]
      ring

/-- Finite partial-assignment correlated rounding. Every vertex has acceptance
probability `density`. The normalized accepted good-pair mass `T` gives an actual
deterministic labeling with success at least `2*T - 1`. -/
theorem exists_labeling_ge_partial {E : Type*} [Fintype E] [Nonempty V] [Nonempty A]
    (μ : FiniteDistribution S) (ν : FiniteDistribution E)
    (accept : V → S → Bool) (label : V → S → A)
    (left right : E → V) (R : E → A → A → Bool) (density : ℝ) (hdensity₀ : 0 < density)
    (hdensity : ∀ v, μ.probability (accept v) = density) :
    ∃ f : V → A,
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 ≤
        partialLabelScore ν left right R f := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨best, _, hbest⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (V → A))) Finset.univ_nonempty (partialLabelScore ν left right R)
  have hmax (f : V → A) :
      partialLabelScore ν left right R f ≤ partialLabelScore ν left right R best := by
    rw [← hbest]
    exact Finset.le_sup' (partialLabelScore ν left right R) (Finset.mem_univ f)
  have hbounded (n : Nat) :
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 -
        (1 - density) ^ n ≤ partialLabelScore ν left right R best := by
    let seeds := traceSeedLaw μ n
    let sample := fun seed => partialSample accept label fallback (traceList n seed)
    have hpoint (e : E) := partialSample_pair_lower μ accept label (fun _ _ => R e)
      fallback density hdensity₀ hdensity (left e) (right e) n
    change ∀ e : E, 2 * (partialEdgeMass μ accept label left right R e / density) - 1 -
      (1 - density) ^ n ≤ traceAverage μ.weight n (fun proposals =>
        if R e (partialSample accept label fallback proposals (left e))
          (partialSample accept label fallback proposals (right e)) then 1 else 0) at hpoint
    have hlower := expectation_mono_inline_RoundingSampling' ν hpoint
    rw [expectation_partial_lower_inline_RoundingSampling] at hlower
    have hswitch :
        ν.expectation (fun e => traceAverage μ.weight n (fun proposals =>
          if R e (partialSample accept label fallback proposals (left e))
            (partialSample accept label fallback proposals (right e)) then 1 else 0)) =
        seeds.expectation (fun seed => partialLabelScore ν left right R (sample seed)) := by
      simp_rw [← traceSeedLaw_expectation μ n]
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro seed
      simp [partialLabelScore, FiniteDistribution.probability,
        FiniteDistribution.expectation, sample, mul_ite]
    rw [hswitch] at hlower
    have hupper := expectation_mono_inline_RoundingSampling' seeds (fun seed => hmax (sample seed))
    rw [expectation_const_inline_RoundingSampling'] at hupper
    exact hlower.trans hupper
  refine ⟨best, ?_⟩
  have hdensity₁ : density ≤ 1 := by
    rw [← hdensity (Classical.choice (inferInstance : Nonempty V))]
    exact μ.probability_le_one _
  by_contra hn
  have hgap : 0 <
      (2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1) -
        partialLabelScore ν left right R best := sub_pos.mpr (lt_of_not_ge hn)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - density)
    (by linarith : 1 - density < 1)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hgap)).exists
  linarith [hbounded n]

end

/-!
Exact finite threshold expansion for unit vectors.  A shared seed chooses one
coordinate and one atom of the common threshold partition.  Squared amplitudes
are acceptance probabilities, and joint acceptance has the coordinatewise
minimum law.  The construction permits arbitrary vertex-dependent labels and
arbitrary relations between their labels.
-/

open scoped BigOperators
open Foundations Games CorrelatedSampling

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

/-- All squared amplitudes, including repetitions, determine a single shared
finite threshold partition. -/
def thresholdLevels (f : V → Ω → ℝ) : List ℝ := by
  classical
  exact (Finset.univ : Finset (V × Ω)).toList.map (fun p => f p.1 p.2 ^ 2)

theorem square_mem_thresholdLevels (f : V → Ω → ℝ) (x : V) (ω : Ω) :
    f x ω ^ 2 ∈ thresholdLevels f := by
  classical
  apply List.mem_map.mpr
  exact ⟨(x, ω), by simp, rfl⟩

/-- The seed is a coordinate and a finite threshold interval. -/
abbrev ThresholdSeed (f : V → Ω → ℝ) := RectangleSeed (thresholdLevels f) Ω

def thresholdDistribution [Nonempty Ω] (f : V → Ω → ℝ) :
    FiniteDistribution (ThresholdSeed f) := rectangleDistribution (thresholdLevels f)

theorem thresholdSeed_nonempty [Nonempty Ω] (f : V → Ω → ℝ) :
    Nonempty (ThresholdSeed f) := by
  have hsum : (∑ seed, (thresholdDistribution f).weight seed) ≠ 0 := by
    rw [(thresholdDistribution f).normalized]
    norm_num
  obtain ⟨seed, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨seed⟩

def thresholdAccept (f : V → Ω → ℝ) (x : V) : ThresholdSeed f → Bool :=
  rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)

/-- Labels use only the local vertex and the shared coordinate. -/
def thresholdLabel (f : V → Ω → ℝ) (a : V → Ω → A) (x : V)
    (seed : ThresholdSeed f) : A := a x seed.1

def thresholdRate (Ω : Type*) [Fintype Ω] : ℝ := 1 / Fintype.card Ω

theorem thresholdRate_positive [Nonempty Ω] : 0 < thresholdRate Ω := by
  unfold thresholdRate
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := Ω))

omit [Fintype V] in
theorem square_le_one_of_row_norm (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) (ω : Ω) : f x ω ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ t, f x t ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg (f x t)) (Finset.mem_univ ω)
    _ = 1 := hnorm x

/-- Every vertex accepts with the same positive mass, independently of its
unit vector.  Nonnegativity of the amplitudes is unnecessary for this lemma. -/
theorem threshold_acceptance_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) :
    (thresholdDistribution f).probability (thresholdAccept f x) = thresholdRate Ω := by
  change eventMass (rectangleWeight (thresholdLevels f))
    (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)) = _
  rw [rectangle_acceptance_mass (thresholdLevels f) _
    (square_mem_thresholdLevels f x) (fun ω => sq_nonneg (f x ω))
    (square_le_one_of_row_norm f hnorm x), hnorm x]
  rfl

/-- Joint acceptance with any relation on the two local labels has exactly the
minimum-overlap mass.  Both vertices use the same coordinate and threshold. -/
theorem threshold_good_pair_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Prop) [DecidableRel R] :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        decide (R (thresholdLabel f a x seed) (thresholdLabel f a y seed))) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  classical
  change (∑ seed : RectangleSeed (thresholdLevels f) Ω,
    if (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2) seed &&
        rectangleAccept (thresholdLevels f) (fun ω => f y ω ^ 2) seed) &&
        decide (R (a x seed.1) (a y seed.1)) then
      rectangleWeight (thresholdLevels f) seed else 0) = _
  have hand := congrFun (rectangle_and (thresholdLevels f)
    (fun ω => f x ω ^ 2) (fun ω => f y ω ^ 2))
  simp_rw [hand]
  rw [Fintype.sum_prod_type]
  have hrow (ω : Ω) :
      (∑ i : Fin (thresholdPartition (thresholdLevels f)).length,
        if rectangleAccept (thresholdLevels f)
            (fun t => min (f x t ^ 2) (f y t ^ 2)) (ω, i) &&
            decide (R (a x ω) (a y ω)) then
          rectangleWeight (thresholdLevels f) (ω, i) else 0) =
        (if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0) /
          (Fintype.card Ω : ℝ) := by
    by_cases hR : R (a x ω) (a y ω)
    · simpa only [hR, decide_true, Bool.and_true, ite_true] using
        rectangle_row_mass (thresholdLevels f)
          (fun t => min (f x t ^ 2) (f y t ^ 2)) ω
          (min_mem_thresholds _ (square_mem_thresholdLevels f x ω)
            (square_mem_thresholdLevels f y ω))
          (le_min (sq_nonneg _) (sq_nonneg _))
          ((min_le_left _ _).trans (square_le_one_of_row_norm f hnorm x ω))
    · simp [hR]
  simp_rw [hrow]
  simp only [thresholdRate, div_eq_mul_inv, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- Boolean-predicate form used by finite games and the shared sampler. -/
theorem threshold_good_pair_mass_bool [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Bool) :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        R (thresholdLabel f a x seed) (thresholdLabel f a y seed)) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  simpa only [Bool.decide_eq_true] using
    threshold_good_pair_mass f hnorm a x y (fun b c => R b c = true)

end MaxCutGames.Repetition

end

end OAI
