import Mathlib

namespace OAI

open Filter
open scoped Topology ENNReal

namespace Invariant233.ProductNorm

theorem floor_lower_bound (x t : ℝ) (hx : 0 ≤ x) :
    t - 1 ≤ (⌊x + t⌋ : ℝ) := by
  have h := Int.sub_one_lt_floor (x + t)
  linarith

theorem finite_cost_lower_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hx : ∀ i ∈ I, 0 ≤ x i) :
    (n : ℝ) * (∑ i ∈ I, c i * θ i) - (∑ i ∈ I, c i) ≤
      ∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ) := by
  calc
    (n : ℝ) * (∑ i ∈ I, c i * θ i) - (∑ i ∈ I, c i) =
        ∑ i ∈ I, c i * ((n : ℝ) * θ i - 1) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (floor_lower_bound (x i) ((n : ℝ) * θ i) (hx i hi))
        (hc i hi)

theorem finite_weight_upper_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hx : ∀ i ∈ I, 0 ≤ x i) :
    Real.exp (-(∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  apply Real.exp_le_exp.mpr
  have h := finite_cost_lower_bound I c x θ n hc hx
  linarith

theorem infinite_weight_upper_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ c i) (hx : ∀ i, 0 ≤ x i) (hθ : ∀ i, 0 ≤ θ i)
    (hsum : Summable (fun i => c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) :
    Real.exp (-(∑' i, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  have hcost : ∀ i, 0 ≤ c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ) := by
    intro i
    apply mul_nonneg (hc i)
    exact_mod_cast Int.floor_nonneg.mpr (add_nonneg (hx i) (mul_nonneg (Nat.cast_nonneg n) (hθ i)))
  calc
    Real.exp (-(∑' i, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
        Real.exp (-(∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (Summable.sum_le_tsum I (fun i _hi => hcost i) hsum)
    _ ≤ _ := finite_weight_upper_bound I c x θ n (fun i _ => hc i) (fun i _ => hx i)

theorem root_upper_bound (u C S : ℝ) (n : ℕ) (hn : 0 < n)
    (hu : 0 ≤ u) (h : u ≤ Real.exp (C - (n : ℝ) * S)) :
    u ^ (1 / (n : ℝ)) ≤ Real.exp (C / (n : ℝ) - S) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    u ^ (1 / (n : ℝ)) ≤ Real.exp (C - (n : ℝ) * S) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow hu h (by positivity)
    _ = Real.exp ((C - (n : ℝ) * S) * (1 / (n : ℝ))) :=
      (Real.exp_mul _ _).symm
    _ = Real.exp (C / (n : ℝ) - S) := by
      congr 1
      field_simp

theorem tendsto_root_zero_of_exponential_bounds
    (u C S : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hbound : ∀ q n, 0 < n → u n ≤ Real.exp (C q - (n : ℝ) * S q))
    (hS : ∀ b : ℝ, ∃ q, b < S q) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le ha (Real.rpow_nonneg (hu n) _)
  · intro ε hε
    obtain ⟨q, hq⟩ := hS (1 - Real.log ε)
    have hlim : Tendsto (fun n : ℕ => C q / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (C q)
    have hevent : ∀ᶠ n : ℕ in atTop, C q / (n : ℝ) < 1 :=
      hlim.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hevent, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    calc
      (u n) ^ (1 / (n : ℝ)) ≤ Real.exp (C q / (n : ℝ) - S q) :=
        root_upper_bound (u n) (C q) (S q) n hnpos (hu n) (hbound q n hnpos)
      _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
      _ = ε := Real.exp_log hε

theorem block_angle_sum_lower_bound {ι : Type*} (I : Finset ι)
    (hI : I.Nonempty) (K : ℝ) (hK : 0 < K) (θ : ι → ℝ)
    (hθ : ∀ i ∈ I, 1 / ((I.card : ℝ) * K) ≤ θ i) :
    1 / K ≤ ∑ i ∈ I, θ i := by
  have hcard : (I.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hI
  have hK0 : K ≠ 0 := ne_of_gt hK
  calc
    1 / K = ∑ _i ∈ I, 1 / ((I.card : ℝ) * K) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ _ := Finset.sum_le_sum hθ

theorem one_le_block_cost (C K angleSum : ℝ) (hK : 1 ≤ K)
    (hC : K ^ 2 ≤ C) (hθ : 1 / K ≤ angleSum) :
    1 ≤ C * angleSum := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hCnonneg : 0 ≤ C := (sq_nonneg K).trans hC
  have hCK : K ≤ C / K := (le_div_iff₀ hKpos).mpr (by nlinarith)
  calc
    1 ≤ K := hK
    _ ≤ C / K := hCK
    _ = C * (1 / K) := by ring
    _ ≤ C * angleSum := mul_le_mul_of_nonneg_left hθ hCnonneg

theorem unbounded_prefix_cost (b : ℕ → ℝ) (hb : ∀ j, 1 ≤ b j) :
    ∀ a : ℝ, ∃ q : ℕ, a < ∑ j ∈ Finset.range q, b j := by
  intro a
  obtain ⟨q, hq⟩ := exists_nat_gt a
  refine ⟨q, hq.trans_le ?_⟩
  calc
    (q : ℝ) = ∑ _j ∈ Finset.range q, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _hj => hb j

theorem block_cost_tsum_eq_top (C K angleSum : ℕ → ℝ)
    (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (hθ : ∀ j, 1 / K j ≤ angleSum j) :
    (∑' j, ENNReal.ofReal (C j * angleSum j)) = ⊤ := by
  apply top_unique
  calc
    (⊤ : ℝ≥0∞) = ∑' _j : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun j => by
      simpa using ENNReal.ofReal_le_ofReal
        (one_le_block_cost (C j) (K j) (angleSum j) (hK j) (hC j) (hθ j))

theorem exists_finite_sum_gt_of_tsum_eq_top {ι : Type*}
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hdiv : (∑' i, ENNReal.ofReal (a i)) = ⊤) (b : ℝ) :
    ∃ I : Finset ι, b < ∑ i ∈ I, a i := by
  classical
  by_cases hb : 0 ≤ b
  · have hlt : ENNReal.ofReal b < ∑' i, ENNReal.ofReal (a i) := by
      rw [hdiv]
      exact ENNReal.ofReal_lt_top
    rw [ENNReal.tsum_eq_iSup_sum] at hlt
    obtain ⟨I, hI⟩ := lt_iSup_iff.mp hlt
    refine ⟨I, ?_⟩
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => ha i)] at hI
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb).mp hI
  · exact ⟨∅, by simpa using lt_of_not_ge hb⟩

theorem tsum_eq_top_of_disjoint_blocks {ι : Type*}
    (J : ℕ → Finset ι) (hJ : Pairwise (fun j k => Disjoint (J j) (J k)))
    (a : ι → ℝ≥0∞) (ha : ∀ j, 1 ≤ ∑ i ∈ J j, a i) :
    (∑' i, a i) = ⊤ := by
  classical
  let e : (Σ j : ℕ, ↥(J j)) → ι := fun p => p.2.1
  have he : Function.Injective e := by
    rintro ⟨j, i, hi⟩ ⟨k, l, hl⟩ hil
    change i = l at hil
    have hjk : j = k := by
      by_contra hne
      exact Finset.disjoint_left.mp (hJ hne) hi (hil.symm ▸ hl)
    subst k
    subst l
    rfl
  apply top_unique
  calc
    (⊤ : ℝ≥0∞) = ∑' _j : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' j : ℕ, ∑' i : ↥(J j), a i := ENNReal.tsum_le_tsum fun j => by
      simpa only [tsum_fintype, Finset.univ_eq_attach, Finset.sum_attach] using ha j
    _ = ∑' p : (Σ j : ℕ, ↥(J j)), a (e p) :=
      (ENNReal.tsum_sigma (fun j (i : ↥(J j)) => a i)).symm
    _ ≤ ∑' i, a i := ENNReal.tsum_comp_le_tsum_of_injective he a

theorem block_coordinate_cost_tsum_eq_top
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (C K : ℕ → ℝ)
    (θ : (Σ j : ℕ, Fin (m j)) → ℝ)
    (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j (i : Fin (m j)), 1 / ((m j : ℝ) * K j) ≤ θ ⟨j, i⟩) :
    (∑' i, ENNReal.ofReal (C i.1) * ENNReal.ofReal (θ i)) = ⊤ := by
  rw [ENNReal.tsum_sigma (fun j (i : Fin (m j)) =>
    ENNReal.ofReal (C j) * ENNReal.ofReal (θ ⟨j, i⟩))]
  apply top_unique
  calc
    (⊤ : ℝ≥0∞) = ∑' _j : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun j => by
      have hC0 : 0 ≤ C j := (sq_nonneg (K j)).trans (hC j)
      have hI : (Finset.univ : Finset (Fin (m j))).Nonempty := by
        exact ⟨⟨0, hm j⟩, Finset.mem_univ _⟩
      have hsum : 1 / K j ≤ ∑ i : Fin (m j), θ ⟨j, i⟩ := by
        apply block_angle_sum_lower_bound Finset.univ hI (K j)
          (lt_of_lt_of_le zero_lt_one (hK j)) (fun i => θ ⟨j, i⟩)
        intro i hi
        simpa using hθ j i
      have hblock := one_le_block_cost (C j) (K j)
        (∑ i : Fin (m j), θ ⟨j, i⟩) (hK j) (hC j) hsum
      calc
        (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C j * ∑ i : Fin (m j), θ ⟨j, i⟩) := by
          simpa using ENNReal.ofReal_le_ofReal hblock
        _ = ∑' i : Fin (m j), ENNReal.ofReal (C j) * ENNReal.ofReal (θ ⟨j, i⟩) := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_sum_of_nonneg
            (fun i _hi => hθ0 ⟨j, i⟩), tsum_fintype, Finset.mul_sum]

theorem tendsto_root_zero_of_block_bounds
    (u loss C K angleSum : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (hθ : ∀ j, 1 / K j ≤ angleSum j)
    (hbound : ∀ q n, 0 < n →
      u n ≤ Real.exp (loss q - (n : ℝ) *
        (∑ j ∈ Finset.range q, C j * angleSum j))) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_root_zero_of_exponential_bounds u loss
    (fun q => ∑ j ∈ Finset.range q, C j * angleSum j) hu hbound
  exact unbounded_prefix_cost _ fun j =>
    one_le_block_cost (C j) (K j) (angleSum j) (hK j) (hC j) (hθ j)

end Invariant233.ProductNorm

end OAI
