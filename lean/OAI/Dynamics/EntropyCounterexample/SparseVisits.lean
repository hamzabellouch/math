import Mathlib

namespace OAI

noncomputable section

open Function Set Filter
open scoped BigOperators

namespace Problem340

theorem birkhoffSum_le_of_good_blocks {X : Type*} (T : X → X) (g : X → ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) {J : ℕ} (hg : ∀ x, g x ≤ 1)
    (hblock : ∀ x, ∃ k : ℕ, 0 < k ∧ k ≤ J ∧
      birkhoffSum T g k x ≤ τ * k) :
    ∀ n : ℕ, ∀ x, birkhoffSum T g n x ≤ τ * n + J := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x
    obtain ⟨k, hkpos, hkJ, hk⟩ := hblock x
    by_cases hkn : k ≤ n
    · have hn : n - k < n := Nat.sub_lt (lt_of_lt_of_le hkpos hkn) hkpos
      have htail := ih (n - k) hn (T^[k] x)
      have hsplit := birkhoffSum_add_right_apply T g k (n - k) x
      rw [Nat.add_sub_of_le hkn] at hsplit
      rw [hsplit]
      have hcast : (k : ℝ) + (n - k : ℕ) = n := by
        exact_mod_cast Nat.add_sub_of_le hkn
      nlinarith
    · have hsum : birkhoffSum T g n x ≤ (n : ℝ) := by
        unfold birkhoffSum
        calc
          (∑ i ∈ Finset.range n, g (T^[i] x)) ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun i _hi => hg (T^[i] x)
          _ = n := by simp
      have hnJ : n ≤ J := le_trans (le_of_lt (lt_of_not_ge hkn)) hkJ
      have hnJ' : (n : ℝ) ≤ J := by exact_mod_cast hnJ
      have hnonneg : 0 ≤ τ * (n : ℝ) := mul_nonneg hτ (Nat.cast_nonneg n)
      linarith

theorem exists_good_block_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {g : X → ℝ} (hg : UpperSemicontinuous g)
    {τ : ℝ} (hgood : ∀ x, ∃ n : ℕ, birkhoffSum T g n x < τ * n) :
    ∃ J : ℕ, ∀ x, ∃ k : ℕ, 0 < k ∧ k ≤ J ∧
      birkhoffSum T g k x ≤ τ * k := by
  classical
  let U : ℕ → Set X := fun n => {x | birkhoffSum T g n x < τ * n}
  have hU : ∀ n, IsOpen (U n) := by
    intro n
    have hsum : UpperSemicontinuous (birkhoffSum T g n) := by
      unfold birkhoffSum
      apply upperSemicontinuous_sum
      intro i _hi
      exact hg.comp (hT.iterate i)
    exact hsum.isOpen_preimage (τ * n)
  have hcover : (Set.univ : Set X) ⊆ ⋃ n, U n := by
    intro x _hx
    obtain ⟨n, hn⟩ := hgood x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨s.sup id, ?_⟩
  intro x
  obtain ⟨k, hks, hk⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  refine ⟨k, ?_, Finset.le_sup (f := id) hks, le_of_lt hk⟩
  by_contra h
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
  simp [U, hk0] at hk

theorem exists_good_block_of_eventually_zero {X : Type*} (T : X → X) (g : X → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (x : X)
    (hzero : ∀ᶠ n in atTop, g (T^[n] x) = 0) :
    ∃ n : ℕ, birkhoffSum T g n x < τ * n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hzero
  obtain ⟨n, hn⟩ := exists_nat_gt (birkhoffSum T g N x / τ)
  have htail : birkhoffSum T g n (T^[N] x) = 0 := by
    unfold birkhoffSum
    apply Finset.sum_eq_zero
    intro i _hi
    rw [← Function.iterate_add_apply]
    exact hN (i + N) (Nat.le_add_left N i)
  refine ⟨N + n, ?_⟩
  rw [birkhoffSum_add_right_apply, htail, add_zero, Nat.cast_add, mul_add]
  have hlt : birkhoffSum T g N x < (n : ℝ) * τ := (div_lt_iff₀ hτ).mp hn
  have hnonneg : 0 ≤ τ * (N : ℝ) := mul_nonneg hτ.le (Nat.cast_nonneg N)
  nlinarith

theorem exists_uniform_birkhoffSum_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {g : X → ℝ} (hg : UpperSemicontinuous g)
    (hg_le : ∀ x, g x ≤ 1)
    (hzero : ∀ x, ∀ᶠ n in atTop, g (T^[n] x) = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x, birkhoffSum T g n x ≤ τ * n + J := by
  obtain ⟨J, hJ⟩ := exists_good_block_bound hT hg
    (fun x => exists_good_block_of_eventually_zero T g hτ x (hzero x))
  exact ⟨J, birkhoffSum_le_of_good_blocks T g hτ.le hg_le hJ⟩

noncomputable def outsideVisitsCount {X : Type*} (T : X → X) (V : Set X)
    (n : ℕ) (x : X) : ℕ := by
  classical
  exact ((Finset.range n).filter (fun i => T^[i] x ∉ V)).card

theorem exists_sparse_visits_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {V : Set X} (hV : IsOpen V)
    (hentry : ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x,
      (outsideVisitsCount T V n x : ℝ) ≤ τ * n + J := by
  classical
  let g : X → ℝ := Vᶜ.indicator (fun _ => 1)
  have hg : UpperSemicontinuous g := hV.isClosed_compl.upperSemicontinuous_indicator zero_le_one
  have hgle : ∀ x, g x ≤ 1 := by
    intro x
    simp only [g, Set.indicator_apply]
    split_ifs <;> norm_num
  have hgzero : ∀ x, ∀ᶠ n in atTop, g (T^[n] x) = 0 := by
    intro x
    filter_upwards [hentry x] with n hn
    simp [g, hn]
  obtain ⟨J, hJ⟩ := exists_uniform_birkhoffSum_bound hT hg hgle hgzero hτ
  refine ⟨J, ?_⟩
  intro n x
  have hsum : birkhoffSum T g n x =
      (((Finset.range n).filter (fun i => T^[i] x ∉ V)).card : ℝ) := by
    simp only [birkhoffSum, g, Set.indicator_apply, Set.mem_compl_iff]
    rw [← Finset.sum_filter]
    simp
  change (((Finset.range n).filter (fun i => T^[i] x ∉ V)).card : ℝ) ≤ _
  rw [← hsum]
  exact hJ n x

theorem exists_sparse_sampled_visits_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {V : Set X} (hV : IsOpen V)
    (hentry : ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V)
    {m : ℕ} (hm : 0 < m) {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x,
      (outsideVisitsCount (T^[m]) V n x : ℝ) ≤ τ * n + J := by
  apply exists_sparse_visits_bound (hT.iterate m) hV ?_ hτ
  intro x
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hentry x)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← Function.iterate_mul]
  apply hN (m * n)
  refine hn.trans ?_
  simpa using Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hm)

theorem eventually_mem_of_tendsto_infDist {X : Type*} [PseudoMetricSpace X]
    {K V : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : IsOpen V) (hKV : K ⊆ V) {u : ℕ → X}
    (hu : Tendsto (fun n => Metric.infDist (u n) K) atTop (nhds 0)) :
    ∀ᶠ n in atTop, u n ∈ V := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hV hKV
  filter_upwards [hu.eventually (gt_mem_nhds hδ)] with n hn
  exact hsub ((Metric.mem_thickening_iff_infDist_lt hne).mpr hn)

theorem exists_sparse_blocks_of_attraction {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {K V : Set X} (hK : IsCompact K)
    (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V)
    (hattract : ∀ x, Tendsto (fun n => Metric.infDist (T^[n] x) K) atTop (nhds 0))
    {m : ℕ} (hm : 0 < m) {τ : ℝ} (hτ : 0 < τ) :
    ∃ J : ℕ, ∀ n : ℕ, ∀ x,
      (outsideVisitsCount (T^[m]) V n x : ℝ) ≤ τ * n + J := by
  apply exists_sparse_sampled_visits_bound hT hV ?_ hm hτ
  intro x
  exact eventually_mem_of_tendsto_infDist hK hne hV hKV (hattract x)

theorem eventually_uniform_sparse_visits {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {T : X → X} (hT : Continuous T) {V : Set X} (hV : IsOpen V)
    (hentry : ∀ x, ∀ᶠ n in atTop, T^[n] x ∈ V) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ x, (outsideVisitsCount T V n x : ℝ) ≤ τ * n := by
  obtain ⟨J, hJ⟩ := exists_sparse_visits_bound hT hV hentry (half_pos hτ)
  obtain ⟨N, hN⟩ := exists_nat_gt ((J : ℝ) / (τ / 2))
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn x
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : (J : ℝ) < (N : ℝ) * (τ / 2) := (div_lt_iff₀ (half_pos hτ)).mp hN
  have hbound := hJ n x
  nlinarith

theorem eventually_uniform_sparse_blocks_of_attraction {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X] {T : X → X} (hT : Continuous T)
    {K V : Set X} (hK : IsCompact K) (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V)
    (hattract : ∀ x, Tendsto (fun n => Metric.infDist (T^[n] x) K) atTop (nhds 0))
    {m : ℕ} (hm : 0 < m) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ x, (outsideVisitsCount (T^[m]) V n x : ℝ) ≤ τ * n := by
  apply eventually_uniform_sparse_visits (hT.iterate m) hV ?_ hτ
  intro x
  have hex := eventually_mem_of_tendsto_infDist hK hne hV hKV (hattract x)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hex
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← Function.iterate_mul]
  apply hN (m * n)
  refine hn.trans ?_
  simpa using Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hm)

end Problem340

end

end OAI
