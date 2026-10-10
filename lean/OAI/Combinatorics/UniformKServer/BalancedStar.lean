import Mathlib
import OAI.Combinatorics.UniformKServer.BalancedRepair

namespace OAI

namespace UniformKServer.BalancedStar
open UniformKServer.BalancedRepair
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

def Balanced (a : ℝ) (x : ℤ) : Prop := x = ⌊a⌋ ∨ x = ⌈a⌉

structure Input (Ω ι : Type*) [Fintype Ω] [Fintype ι] where
  μ : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ μ ω
  total : ∑ ω, μ ω = 1
  a : ι → ℝ
  b : ι → ℝ
  a_nonneg : ∀ i, 0 ≤ a i
  b_nonneg : ∀ i, 0 ≤ b i
  X : Ω → ι → ℤ
  N : Ω → ℤ
  X_balanced : ∀ ω i, Balanced (a i) (X ω i)
  N_balanced : ∀ ω, Balanced (∑ i, b i) (N ω)
  X_mean : ∀ i, ∑ ω, μ ω * (X ω i : ℝ) = a i
  N_mean : ∑ ω, μ ω * (N ω : ℝ) = ∑ i, b i

noncomputable def realized (b : ι → ℝ) (A : Finset ι) (i : ι) : ℤ :=
  ⌊b i⌋ + if i ∈ A then 1 else 0

def T (I : Input Ω ι) : ℝ := ∑ i, |I.a i - I.b i|
def imbalance (I : Input Ω ι) : ℝ :=
  ∑ ω, I.μ ω * |(I.N ω : ℝ) - ∑ i, (I.X ω i : ℝ)|

noncomputable def jointCost (I : Input Ω ι) (g : Joint Ω ι) : ℝ :=
  ∑ q, g q * ∑ i, |(realized I.b q.2 i : ℝ) - (I.X q.1 i : ℝ)|

def Valid (I : Input Ω ι) (ω : Ω) (A : Finset ι) : Prop :=
  (∀ i, Balanced (I.b i) (realized I.b A i)) ∧
    (∑ i, realized I.b A i) = I.N ω


noncomputable def clip (b : ℝ) (x : ℤ) : ℤ := max ⌊b⌋ (min ⌈b⌉ x)

theorem balanced_bounds {a : ℝ} {x : ℤ} (hx : Balanced a x) : ⌊a⌋ ≤ x ∧ x ≤ ⌈a⌉ := by
  rcases hx with rfl | rfl <;> exact ⟨by first | rfl | exact Int.floor_le_ceil a,
    by first | rfl | exact Int.floor_le_ceil a⟩

theorem bounds_balanced {a : ℝ} {x : ℤ} (hx : ⌊a⌋ ≤ x ∧ x ≤ ⌈a⌉) : Balanced a x := by
  have := Int.ceil_le_floor_add_one a
  dsimp [Balanced]
  omega

theorem clip_balanced (b : ℝ) (x : ℤ) : Balanced b (clip b x) := by
  apply bounds_balanced
  dsimp [clip]
  exact ⟨le_max_left _ _, max_le (Int.floor_le_ceil b) (min_le_left _ _)⟩

omit [DecidableEq Ω] in
theorem clip_nonexpansive (μ : Ω → ℝ) (X : Ω → ℤ) (a b : ℝ)
    (_hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (hX : ∀ ω, Balanced a (X ω)) (hmean : ∑ ω, μ ω * (X ω : ℝ) = a) :
    (∑ ω, μ ω * |(clip b (X ω) : ℝ) - (X ω : ℝ)|) ≤ |a-b| := by
  rcases le_total a b with hab | hba
  · have hu : ∀ ω, X ω ≤ ⌈b⌉ := fun ω =>
      (balanced_bounds (hX ω)).2.trans (Int.ceil_mono hab)
    by_cases hl : ⌊b⌋ ≤ ⌊a⌋
    · have he : ∀ ω, clip b (X ω) = X ω := by
        intro ω
        rw [clip, min_eq_right (hu ω), max_eq_right (hl.trans (balanced_bounds (hX ω)).1)]
      simp [he]
    · have hl' : ∀ ω, X ω ≤ ⌊b⌋ := by
        intro ω
        have h₁ := (balanced_bounds (hX ω)).2
        have h₂ := Int.ceil_le_floor_add_one a
        omega
      have he : ∀ ω, clip b (X ω) = ⌊b⌋ := by
        intro ω
        rw [clip, min_eq_right (hu ω), max_eq_left (hl' ω)]
      calc
        _ = (⌊b⌋ : ℝ) - a := by
          simp only [he, abs_of_nonneg (sub_nonneg.mpr (Int.cast_le.mpr (hl' _))),
            mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, hμsum, hmean, one_mul]
        _ ≤ |a-b| := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; linarith [Int.floor_le b]
  · have hl : ∀ ω, ⌊b⌋ ≤ X ω := fun ω =>
      (Int.floor_mono hba).trans (balanced_bounds (hX ω)).1
    by_cases hu : ⌈a⌉ ≤ ⌈b⌉
    · have he : ∀ ω, clip b (X ω) = X ω := by
        intro ω
        rw [clip, min_eq_right ((balanced_bounds (hX ω)).2.trans hu), max_eq_right (hl ω)]
      simp [he]
    · have hu' : ∀ ω, ⌈b⌉ ≤ X ω := by
        intro ω
        have h₁ := (balanced_bounds (hX ω)).1
        have h₂ := Int.ceil_le_floor_add_one a
        omega
      have he : ∀ ω, clip b (X ω) = ⌈b⌉ := by
        intro ω
        rw [clip, min_eq_left (hu' ω), max_eq_right (Int.floor_le_ceil b)]
      calc
        _ = a - (⌈b⌉ : ℝ) := by
          simp only [he, abs_of_nonpos (sub_nonpos.mpr (Int.cast_le.mpr (hu' _)))]
          simp only [neg_sub, mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, hμsum, hmean, one_mul]
        _ ≤ |a-b| := by rw [abs_of_nonneg (sub_nonneg.mpr hba)]; linarith [Int.le_ceil b]


noncomputable def lowerSum (b : ι → ℝ) : ℤ := ∑ i, ⌊b i⌋
noncomputable def upperSet (b : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => ⌊b i⌋ < ⌈b i⌉)
noncomputable def clippedSet (b : ι → ℝ) (X : ι → ℤ) : Finset ι :=
  Finset.univ.filter (fun i => ⌊b i⌋ < clip (b i) (X i))
noncomputable def slots (b : ι → ℝ) (N : ℤ) : ℕ := (N - lowerSum b).toNat
noncomputable def fraction (b : ι → ℝ) (i : ι) : ℝ := b i - ⌊b i⌋

omit [Fintype ι] [DecidableEq ι] in
theorem fraction_bounds (b : ι → ℝ) (i : ι) : fraction b i ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [fraction]
  constructor
  · exact sub_nonneg.mpr (Int.floor_le _)
  · exact (Int.fract_lt_one (b i)).le

theorem sum_realized (b : ι → ℝ) (A : Finset ι) :
    (∑ i, realized b A i) = lowerSum b + (A.card : ℤ) := by
  simp [realized, lowerSum, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem clippedSet_subset (b : ι → ℝ) (X : ι → ℤ) : clippedSet b X ⊆ upperSet b := by
  intro i hi
  simp only [clippedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi.trans_le (balanced_bounds (clip_balanced (b i) (X i))).2

theorem represented_clip (b : ι → ℝ) (X : ι → ℤ) (i : ι) :
    realized b (clippedSet b X) i = clip (b i) (X i) := by
  have hb := balanced_bounds (clip_balanced (b i) (X i))
  have hc := Int.ceil_le_floor_add_one (b i)
  simp only [realized, clippedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

theorem subset_balanced (b : ι → ℝ) {A : Finset ι} (hA : A ⊆ upperSet b) (i : ι) :
    Balanced (b i) (realized b A i) := by
  unfold realized
  by_cases hi : i ∈ A
  · rw [ite_eq_left hi]
    right
    have h := hA hi
    simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hc := Int.ceil_le_floor_add_one (b i)
    omega
  · exact Or.inl (by simp [hi])

theorem ceil_sum (b : ι → ℝ) :
    (∑ i, ⌈b i⌉) = lowerSum b + ((upperSet b).card : ℤ) := by
  rw [← sum_realized]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [realized]
  have hf := Int.floor_le_ceil (b i)
  have hc := Int.ceil_le_floor_add_one (b i)
  simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

omit [DecidableEq ι] in
theorem lowerSum_le_floor (b : ι → ℝ) : lowerSum b ≤ ⌊∑ i, b i⌋ := by
  apply Int.le_floor.mpr
  simp only [lowerSum, Int.cast_sum]
  exact Finset.sum_le_sum fun i _ => Int.floor_le (b i)

omit [DecidableEq ι] in
theorem ceil_le_sum (b : ι → ℝ) : ⌈∑ i, b i⌉ ≤ ∑ i, ⌈b i⌉ := by
  apply Int.ceil_le.mpr
  simp only [Int.cast_sum]
  exact Finset.sum_le_sum fun i _ => Int.le_ceil (b i)

theorem slots_spec (b : ι → ℝ) (N : ℤ) (hN : Balanced (∑ i, b i) N) :
    (slots b N : ℤ) = N - lowerSum b ∧ slots b N ≤ (upperSet b).card := by
  have hbounds := balanced_bounds hN
  have hlo := lowerSum_le_floor b
  have hhi := ceil_le_sum b
  rw [ceil_sum] at hhi
  have hn : 0 ≤ N - lowerSum b := by omega
  constructor
  · exact Int.toNat_of_nonneg hn
  · dsimp [slots]
    omega

omit [DecidableEq ι] in
theorem slots_two (b : ι → ℝ) (N : ℤ) (hN : Balanced (∑ i, b i) N) :
    slots b N = (⌊∑ i, b i⌋ - lowerSum b).toNat ∨
      slots b N = (⌊∑ i, b i⌋ - lowerSum b).toNat + 1 := by
  have hbounds := balanced_bounds hN
  have hlo := lowerSum_le_floor b
  have hc := Int.ceil_le_floor_add_one (∑ i, b i)
  dsimp [slots]
  omega

theorem realized_distance (b : ι → ℝ) (A B : Finset ι) :
    (∑ i, |(realized b A i : ℝ) - (realized b B i : ℝ)|) = ((A ∆ B).card : ℝ) := by
  have he : ∀ i, |(realized b A i : ℝ) - (realized b B i : ℝ)| =
      if i ∈ A ∆ B then (1 : ℝ) else 0 := by
    intro i
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;>
      simp [realized, Finset.mem_symmDiff, ha, hb]
  simp [he]

theorem choose_subset_close (H B : Finset ι) (r : ℕ) (hB : B ⊆ H) (hr : r ≤ H.card) :
    ∃ A : Finset ι, A ⊆ H ∧ A.card = r ∧
      ((A ∆ B).card : ℝ) = |(r : ℝ) - (B.card : ℝ)| := by
  rcases le_total r B.card with h | h
  · obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq h
    refine ⟨A,hA.trans hB,hcard,?_⟩
    rw [symmDiff_of_le hA, Finset.card_sdiff_of_subset hA, hcard,
      Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · obtain ⟨A,hBA,hA,hcard⟩ := Finset.exists_subsuperset_card_eq hB h hr
    refine ⟨A,hA,hcard,?_⟩
    rw [symmDiff_of_ge hBA, Finset.card_sdiff_of_subset hBA, hcard,
      Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

theorem preliminary_exists (b : ι → ℝ) (X : ι → ℤ) (N : ℤ)
    (hN : Balanced (∑ i, b i) N) :
    ∃ A : Finset ι, A ⊆ upperSet b ∧ A.card = slots b N ∧
      (∑ i, |(realized b A i : ℝ) - (clip (b i) (X i) : ℝ)|) =
        |(N : ℝ) - ∑ i, (clip (b i) (X i) : ℝ)| := by
  obtain ⟨A,hA,hcard,hd⟩ := choose_subset_close (upperSet b) (clippedSet b X) (slots b N)
    (clippedSet_subset b X) (slots_spec b N hN).2
  refine ⟨A,hA,hcard,?_⟩
  simp_rw [← represented_clip b X]
  rw [realized_distance, hd, ← Int.cast_sum, sum_realized, Int.cast_add, Int.cast_natCast]
  have hc : (slots b N : ℝ) = (N : ℝ) - (lowerSum b : ℝ) := by
    exact_mod_cast (slots_spec b N hN).1
  rw [hc]
  congr 1
  ring

noncomputable def preliminary (I : Input Ω ι) (ω : Ω) : Finset ι :=
  (preliminary_exists I.b (I.X ω) (I.N ω) (I.N_balanced ω)).choose

omit [DecidableEq Ω] in
theorem preliminary_spec (I : Input Ω ι) (ω : Ω) :
    preliminary I ω ⊆ upperSet I.b ∧ (preliminary I ω).card = slots I.b (I.N ω) ∧
      (∑ i, |(realized I.b (preliminary I ω) i : ℝ) - (clip (I.b i) (I.X ω i) : ℝ)|) =
        |(I.N ω : ℝ) - ∑ i, (clip (I.b i) (I.X ω i) : ℝ)| :=
  (preliminary_exists I.b (I.X ω) (I.N ω) (I.N_balanced ω)).choose_spec


omit [DecidableEq ι] in
theorem abs_sum_sub_le (u v : ι → ℝ) :
    |(∑ i, u i) - ∑ i, v i| ≤ ∑ i, |u i-v i| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

omit [DecidableEq Ω] [DecidableEq ι] in
theorem weighted_abs_le (I : Input Ω ι) (x : Ω → ℝ) :
    |∑ ω, I.μ ω * x ω| ≤ ∑ ω, I.μ ω * |x ω| := by
  calc
    _ ≤ ∑ ω, |I.μ ω * x ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp_rw [abs_mul, abs_of_nonneg (I.nonneg _)]

noncomputable def preliminaryCost (I : Input Ω ι) : ℝ :=
  ∑ ω, I.μ ω * ∑ i, |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|

noncomputable def clipCost (I : Input Ω ι) : ℝ :=
  ∑ ω, I.μ ω * ∑ i, |(clip (I.b i) (I.X ω i) : ℝ) - (I.X ω i : ℝ)|

omit [DecidableEq Ω] [DecidableEq ι] in
theorem clipCost_le (I : Input Ω ι) : clipCost I ≤ T I := by
  simp only [clipCost, Finset.mul_sum, T]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ =>
    clip_nonexpansive I.μ (fun ω => I.X ω i) (I.a i) (I.b i) I.nonneg I.total
      (fun ω => I.X_balanced ω i) (I.X_mean i)

omit [DecidableEq Ω] in
theorem preliminaryCost_le (I : Input Ω ι) :
    preliminaryCost I ≤ 2*T I + imbalance I := by
  have hp (ω : Ω) :
      (∑ i, |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|) ≤
        2*(∑ i, |(clip (I.b i) (I.X ω i) : ℝ) - (I.X ω i : ℝ)|) +
        |(I.N ω : ℝ) - ∑ i, (I.X ω i : ℝ)| := by
    have htri := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      abs_sub_le (realized I.b (preliminary I ω) i : ℝ)
        (clip (I.b i) (I.X ω i) : ℝ) (I.X ω i : ℝ)
    rw [Finset.sum_add_distrib, (preliminary_spec I ω).2.2] at htri
    have hsum := abs_sum_sub_le (fun i => (I.X ω i : ℝ))
      (fun i => (clip (I.b i) (I.X ω i) : ℝ))
    simp_rw [abs_sub_comm (I.X ω _ : ℝ)] at hsum
    have ht := abs_sub_le (I.N ω : ℝ) (∑ i, (I.X ω i : ℝ))
      (∑ i, (clip (I.b i) (I.X ω i) : ℝ))
    linarith
  calc
    preliminaryCost I ≤ ∑ ω, I.μ ω *
        (2*(∑ i, |(clip (I.b i) (I.X ω i) : ℝ) - (I.X ω i : ℝ)|) +
          |(I.N ω : ℝ) - ∑ i, (I.X ω i : ℝ)|) :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hp ω) (I.nonneg ω)
    _ = 2*clipCost I + imbalance I := by
      simp only [clipCost, imbalance, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _; ring
    _ ≤ 2*T I + imbalance I := by linarith [clipCost_le I]

omit [DecidableEq Ω] in
theorem initial_marginal (I : Input Ω ι) (i : ι) :
    marginal (BalancedRepair.initial I.μ (preliminary I)) i =
      ∑ ω, I.μ ω * (if i ∈ preliminary I ω then 1 else 0) := by
  simp only [marginal, Fintype.sum_prod_type, BalancedRepair.initial]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (preliminary I ω)]
  · simp only [ite_true]
  · intro A _ hA; simp [hA]
  · simp

omit [DecidableEq Ω] in
theorem initial_realized_mean (I : Input Ω ι) (i : ι) :
    (∑ ω, I.μ ω * (realized I.b (preliminary I ω) i : ℝ)) =
      (⌊I.b i⌋ : ℝ) + marginal (BalancedRepair.initial I.μ (preliminary I)) i := by
  simp only [realized, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, I.total, one_mul, initial_marginal]

omit [DecidableEq Ω] in
theorem discrepancy_le (I : Input Ω ι) :
    discrepancy (fraction I.b) (BalancedRepair.initial I.μ (preliminary I)) ≤ preliminaryCost I + T I := by
  have hp (i : ι) :
      |marginal (BalancedRepair.initial I.μ (preliminary I)) i - fraction I.b i| ≤
        (∑ ω, I.μ ω * |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|) +
        |I.a i-I.b i| := by
    have hm : marginal (BalancedRepair.initial I.μ (preliminary I)) i - fraction I.b i =
        (∑ ω, I.μ ω * ((realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ))) +
        (I.a i-I.b i) := by
      rw [Finset.sum_congr rfl (fun ω _ => mul_sub _ _ _), Finset.sum_sub_distrib,
        initial_realized_mean, I.X_mean]
      dsimp only [fraction, Int.fract]; ring
    rw [hm]
    exact (abs_add_le _ _).trans (add_le_add (weighted_abs_le I _) le_rfl)
  calc
    _ ≤ ∑ i, ((∑ ω, I.μ ω *
        |(realized I.b (preliminary I ω) i : ℝ) - (I.X ω i : ℝ)|) + |I.a i-I.b i|) :=
      Finset.sum_le_sum fun i _ => hp i
    _ = preliminaryCost I + T I := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp [preliminaryCost, T, Finset.mul_sum]

omit [DecidableEq Ω] in
theorem slots_mean (I : Input Ω ι) :
    (∑ ω, I.μ ω * (slots I.b (I.N ω) : ℝ)) = ∑ i, fraction I.b i := by
  have hs (ω : Ω) : (slots I.b (I.N ω) : ℝ) =
      (I.N ω : ℝ) - (lowerSum I.b : ℝ) := by
    exact_mod_cast (slots_spec I.b (I.N ω) (I.N_balanced ω)).1
  simp only [hs, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, I.total, one_mul, I.N_mean]
  simp only [fraction, lowerSum, Int.cast_sum, Finset.sum_sub_distrib]

omit [DecidableEq Ω] in
theorem marginal_realized_mean (I : Input Ω ι) (g : Joint Ω ι)
    (hg : ∑ q, g q = 1) (i : ι) :
    (∑ q, g q * (realized I.b q.2 i : ℝ)) = (⌊I.b i⌋ : ℝ) + marginal g i := by
  simp only [realized, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hg, one_mul]
  rfl

omit [DecidableEq Ω] in
theorem support_subset (I : Input Ω ι) (g : Joint Ω ι)
    (hg : ∀ q, 0 ≤ g q) (hm : ∀ i, marginal g i = fraction I.b i)
    (q : Ω × Finset ι) (hq : 0 < g q) : q.2 ⊆ upperSet I.b := by
  intro i hi
  simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hn
  have he : ⌊I.b i⌋ = ⌈I.b i⌉ := le_antisymm (Int.floor_le_ceil _) (by omega)
  have hf : fraction I.b i = 0 := by
    have hl := Int.floor_le (I.b i)
    have hu := Int.le_ceil (I.b i)
    rw [← he] at hu
    dsimp only [fraction, Int.fract]; linarith
  have hle : g q ≤ marginal g i := by
    calc
      g q = g q * (if i ∈ q.2 then 1 else 0) := by simp [hi]
      _ ≤ marginal g i := Finset.single_le_sum (f := fun z => g z * if i ∈ z.2 then 1 else 0)
        (fun z _ => mul_nonneg (hg z) (by split_ifs <;> norm_num)) (Finset.mem_univ q)
  rw [hm, hf] at hle
  linarith

omit [DecidableEq Ω] in
theorem cost_transfer (I : Input Ω ι) (g : Joint Ω ι)
    (hg : admissible I.μ (slots I.b ∘ I.N) g) :
    jointCost I g ≤ cost (preliminary I) g + preliminaryCost I := by
  have hp (q : Ω × Finset ι) :
      (∑ i, |(realized I.b q.2 i : ℝ) - (I.X q.1 i : ℝ)|) ≤
        hamming (preliminary I) q +
        ∑ i, |(realized I.b (preliminary I q.1) i : ℝ) - (I.X q.1 i : ℝ)| := by
    have ht := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      abs_sub_le (realized I.b q.2 i : ℝ) (realized I.b (preliminary I q.1) i : ℝ)
        (I.X q.1 i : ℝ)
    rwa [Finset.sum_add_distrib, realized_distance] at ht
  calc
    _ ≤ ∑ q, g q * (hamming (preliminary I) q +
        ∑ i, |(realized I.b (preliminary I q.1) i : ℝ) - (I.X q.1 i : ℝ)|) :=
      Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hp q) (hg.1 q)
    _ = cost (preliminary I) g + preliminaryCost I := by
      simp only [mul_add, Finset.sum_add_distrib, cost]
      congr 1
      rw [Fintype.sum_prod_type]
      simp only [← Finset.sum_mul, hg.2.1]
      rfl

theorem rounding_star (I : Input Ω ι) :
    (∀ ω, ∃ A, Valid I ω A) ∧
    ∃ g : Joint Ω ι, (∀ q, 0 ≤ g q) ∧
      (∀ ω, ∑ A : Finset ι, g (ω,A) = I.μ ω) ∧
      (∀ q, 0 < g q → Valid I q.1 q.2) ∧
      (∀ i, ∑ q, g q * (realized I.b q.2 i : ℝ) = I.b i) ∧
      jointCost I g ≤ 32*T I + 11*imbalance I := by
  have hv (ω : Ω) (A : Finset ι) (hA : A ⊆ upperSet I.b)
      (hc : A.card = slots I.b (I.N ω)) : Valid I ω A := by
    refine ⟨subset_balanced I.b hA, ?_⟩
    rw [sum_realized, hc, (slots_spec I.b (I.N ω) (I.N_balanced ω)).1]
    ring
  constructor
  · intro ω
    exact ⟨preliminary I ω, hv ω _ (preliminary_spec I ω).1 (preliminary_spec I ω).2.1⟩
  obtain ⟨g,hg,hm,hcost⟩ := repair I.μ (slots I.b ∘ I.N) (preliminary I) (fraction I.b)
    I.nonneg I.total (fun ω => (preliminary_spec I ω).2.1)
    (⌊∑ i, I.b i⌋ - lowerSum I.b).toNat
    (fun ω => slots_two I.b (I.N ω) (I.N_balanced ω))
    (fraction_bounds I.b) (slots_mean I).symm
  refine ⟨g,hg.1,hg.2.1,?_,?_,?_⟩
  · intro q hq
    apply hv q.1 q.2 (support_subset I g hg.1 hm q hq)
    by_contra hn
    have hz := hg.2.2 q hn
    linarith
  · intro i
    rw [marginal_realized_mean I g (by rw [total_mass hg, I.total]), hm]
    dsimp only [fraction, Int.fract]; ring
  · have h₁ := cost_transfer I g hg
    have h₂ := discrepancy_le I
    have h₃ := preliminaryCost_le I
    linarith

end UniformKServer.BalancedStar

/-! One conditional update of the complete finite tree rounding process.
The arbitrary supported old law includes every correlation produced by earlier
ancestor roundings; no conditional independence is imposed. -/

end OAI
