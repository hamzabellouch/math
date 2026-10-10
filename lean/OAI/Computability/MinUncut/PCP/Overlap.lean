import Mathlib
import OAI.Computability.MinUncut.PCP.DistributionMaps
import OAI.Computability.MinUncut.Games.LabelBound

namespace OAI

namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
open Information

private theorem min_half_formula (x y : ℝ) :
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
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

private theorem discount_le_self {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

private theorem discount_loss_le_mul {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
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
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
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
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
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

open scoped BigOperators
open Games
noncomputable section

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

open scoped BigOperators
open Games Information

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  Information.totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  Information.totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem selectedLeftProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedLeftProfileError G strategy selected positive j ≤
      Information.totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      Information.totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  leftCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      Information.totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      Information.totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    Information.totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    Information.totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem pushforward_snd_weight_eq_secondMarginal {A B : Type*}
    [Fintype A] [Fintype B] (μ : FiniteDistribution (A × B)) :
    (μ.pushforward Prod.snd).weight = secondMarginal μ.weight := by
  classical
  funext b
  simp [FiniteDistribution.pushforward, secondMarginal, Fintype.sum_prod_type]

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealDataSplitEquiv (j : I) :
    (T × (I → X ⊕ Y)) ≃ ((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) where
  toFun z := ((z.1, fun i => z.2 i.1), z.2 j)
  invFun z := (z.1.1, mergeAt j z.2 z.1.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = j <;> simp [mergeAt, h]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact mergeAt_other j z.2 z.1.2 i
    · exact mergeAt_self j z.2 z.1.2

theorem partialRevealMarginal_secondMarginal
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    secondMarginal (partialRevealMarginal μ j likelihood) =
      secondMarginal (fullRevealMarginal μ j likelihood) := by
  classical
  funext q
  calc
    _ = ∑ z : (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y),
        maskedJoint (partialRevealMarginal μ j likelihood) (z,q) := by
      simp [secondMarginal, Fintype.sum_prod_type, maskedJoint]
    _ = _ := by
      apply Fintype.sum_equiv (revealDataSplitEquiv (T := T) j).symm
      intro z
      exact (fullRevealMarginal_merge μ j likelihood z.1.1 z.1.2 z.2 q).symm

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationDataEquiv (selected : Finset (Fin n)) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ≃
      (((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
        ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem selectedFullReveal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) =
        secondMarginal (selectedRawMarginal G strategy selected j) := by
  classical
  funext q
  apply Fintype.sum_equiv
    (selectedObservationDataEquiv (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected).symm
  intro z
  exact (selectedRawMarginal_fullReveal G strategy selected j (z,q)).symm

theorem selectedRawMarginal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedRawMarginal G strategy selected j) =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  classical
  funext q
  calc
    _ = (selectedJointLaw G strategy selected positive).probability
        (fun z => decide (z.2 j = q)) := by
      simp only [secondMarginal, selectedRawMarginal, FiniteDistribution.probability,
        selectedJointLaw, toGameLaw, Fintype.sum_prod_type, decide_eq_true_eq]
    _ = ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q)) := by
      have h := selectedJointLaw_question_probability G strategy selected positive
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q))
      simpa [selectedQuestionTuple, mergeCoordinates, j.property] using h
    _ = _ := by
      rw [FiniteDistribution.weight_eq_probability_singleton, selectedQuestionMarginal,
        FiniteDistribution.probability_pushforward]

theorem selectedCommonLaw_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedCommonLaw G strategy selected positive j).weight =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  change secondMarginal (partialRevealMarginal G.questions j
    (selectedOutsideLikelihood G strategy selected)) = _
  rw [partialRevealMarginal_secondMarginal, selectedFullReveal_secondMarginal]
  exact selectedRawMarginal_secondMarginal G strategy selected positive j

theorem selectedCommonLaw_questions_pushforward (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    (selectedCommonLaw G strategy selected positive j).pushforward Prod.snd =
      selectedQuestionMarginal G strategy selected positive j.1 := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  exact (congrFun (pushforward_snd_weight_eq_secondMarginal
    (selectedCommonLaw G strategy selected positive j)) q).trans
      (congrFun (selectedCommonLaw_secondMarginal G strategy selected positive j) q)

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionRadius_le_informationRadius [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected)) ≤
      selectedInformationRadius G strategy selected := by
  have hcard : (1 : ℝ) ≤ Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)))
  have hlog := Real.log_nonneg hcard
  have hnonneg : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  unfold selectedInformationRadius
  apply Real.sqrt_le_sqrt
  nlinarith

theorem selectedQuestionMarginal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive j.1).totalVariation G.questions) ≤
      selectedInformationRadius G strategy selected :=
  (unselectedQuestionMarginal_totalVariation_sum_le_sqrt G strategy selected positive).trans
    (selectedQuestionRadius_le_informationRadius G strategy selected)

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

theorem selectedEmbeddingError_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    0 ≤ selectedEmbeddingError G strategy selected positive j := by
  exact add_nonneg
    (mul_nonneg (by norm_num) (Information.totalVariation_nonneg _ _))
    (mul_nonneg (by norm_num) (Information.totalVariation_nonneg _ _))

theorem selectedLeftProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedLeftProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedLeftProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hleft := selected_leftReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedRightProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedEmbeddingError_sum_le_fifteen [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedEmbeddingError G strategy selected positive j) ≤
      15 * selectedInformationRadius G strategy selected := by
  have hl := selectedLeftProfileError_sum G strategy selected positive
  have hr := selectedRightProfileError_sum G strategy selected positive
  have hn : 0 ≤ selectedInformationRadius G strategy selected := Real.sqrt_nonneg _
  simp only [selectedEmbeddingError, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end
end MinUncutGames.Foundations.Repetition

end OAI
