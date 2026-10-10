import OAI.MathematicalPhysics.NavierStokes.Material.History

namespace OAI

namespace Alternating.Memory
open scoped Topology

noncomputable def periodicDecoder (a b x : ℝ) : ℝ :=
  Int.fract x - Real.smoothTransition ((Int.fract x - a) / (b - a))

theorem periodicDecoder_periodic (a b : ℝ) : Function.Periodic (periodicDecoder a b) 1 := by
  intro x
  simp only [periodicDecoder, Int.fract_add_one]

theorem periodicDecoder_on_unit {a b x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    periodicDecoder a b x = x - Real.smoothTransition ((x - a) / (b - a)) := by
  simp only [periodicDecoder, Int.fract_eq_self.2 hx]

theorem periodicDecoder_on_safe {a b m : ℝ} (hab : a < b) (hbm : b < 1) (hma : m < a)
    {x : ℝ} (hx : x ∈ Set.Icc 0 m) : periodicDecoder a b x = x := by
  rw [periodicDecoder_on_unit ⟨hx.1, by linarith [hx.2]⟩,
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith [hx.2]) (by linarith)), sub_zero]

theorem periodicDecoder_near_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    {x : ℝ} (hx : x ∈ Set.Ioo (b - 1) a) : periodicDecoder a b x = x := by
  have hba : 0 < b - a := sub_pos.2 hab
  by_cases hx0 : 0 ≤ x
  · rw [periodicDecoder_on_unit ⟨hx0, hx.2.trans (hab.trans hb)⟩,
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx.2.le) hba.le), sub_zero]
  · have hneg : x < 0 := lt_of_not_ge hx0
    have hfloor : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.2 ⟨by norm_num; linarith [hx.1], by simpa⟩
    have hfract : Int.fract x = x + 1 := by simp [Int.fract, hfloor]
    have hstep : 1 ≤ (x + 1 - a) / (b - a) := (le_div_iff₀ hba).2 (by linarith [hx.1])
    simp [periodicDecoder, hfract, Real.smoothTransition.one_of_one_le hstep]

theorem periodicDecoder_smooth {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicDecoder a b) := by
  apply contDiff_iff_contDiffAt.2
  intro x
  let k : ℤ := ⌊x⌋
  by_cases hx : x = (k : ℝ)
  · have hlocal : periodicDecoder a b =ᶠ[𝓝 x] (fun y : ℝ => y - (k : ℝ)) := by
      filter_upwards [Ioo_mem_nhds (a := (k : ℝ) + b - 1) (b := (k : ℝ) + a)
        (by rw [hx]; linarith) (by rw [hx]; linarith)] with y hy
      have hi := ((periodicDecoder_periodic a b).int_mul (-k)) y
      have heq : periodicDecoder a b y = periodicDecoder a b (y - k) := by
        simpa [sub_eq_add_neg] using hi.symm
      rw [heq]
      exact periodicDecoder_near_zero ha hab hb ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq hlocal
  · have hlow : (k : ℝ) < x := (Int.floor_le x).lt_of_ne (Ne.symm hx)
    have hupp : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
    have hlocal : periodicDecoder a b =ᶠ[𝓝 x]
        (fun y : ℝ => (y - k) - Real.smoothTransition (((y - k) - a) / (b - a))) := by
      filter_upwards [Ioo_mem_nhds hlow hupp] with y hy
      have hfloor : ⌊y⌋ = k := Int.floor_eq_iff.2 ⟨hy.1.le, hy.2⟩
      simp only [periodicDecoder, Int.fract, hfloor]
    apply ContDiffAt.congr_of_eventuallyEq (hg := hlocal)
    apply (show ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (y - k) - Real.smoothTransition (((y - k) - a) / (b - a))) from ?_).contDiffAt
    fun_prop

theorem periodic_iteratedDeriv {P : ℝ → ℝ} (hP : Function.Periodic P 1) (n : ℕ) :
    Function.Periodic (iteratedDeriv n P) 1 := by
  have heq : (fun x => P (x + 1)) = P := funext hP
  have h := iteratedDeriv_comp_add_const n P 1
  rw [heq] at h
  exact fun x => (congr_fun h x).symm

theorem periodicDecoder_derivatives_bounded {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |iteratedDeriv n (periodicDecoder a b) x| ≤ M := by
  have hp := periodic_iteratedDeriv (periodicDecoder_periodic a b) n
  have hc := (periodicDecoder_smooth ha hab hb).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  obtain ⟨M, hM, hbound⟩ :=
    (hp.isBounded_of_continuous (by norm_num : (1 : ℝ) ≠ 0) hc).exists_pos_norm_le
  exact ⟨M, hM, fun x => by simpa using hbound _ ⟨x, rfl⟩⟩

end Alternating.Memory

namespace Alternating.Memory
open scoped BigOperators
open Finset

noncomputable def safeDecoder (b : ℕ) : ℝ → ℝ :=
  periodicDecoder ((2 * tailBound b + 1) / 3) ((tailBound b + 2) / 3)

theorem safeDecoder_smooth {b : ℕ} (hb : 2 ≤ b) :
    ContDiff ℝ (⊤ : ℕ∞) (safeDecoder b) := by
  have hm0 := tailBound_nonneg hb
  have hm1 := tailBound_lt_one hb
  exact periodicDecoder_smooth (by linarith) (by linarith) (by linarith)

theorem safeDecoder_periodic (b : ℕ) : Function.Periodic (safeDecoder b) 1 :=
  periodicDecoder_periodic _ _

theorem safeDecoder_on_safe {b : ℕ} (hb : 2 ≤ b) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (tailBound b)) : safeDecoder b x = x := by
  have hm1 := tailBound_lt_one hb
  exact periodicDecoder_on_safe (by linarith) (by linarith) (by linarith) hx

theorem safeDecoder_derivatives_bounded {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |iteratedDeriv n (safeDecoder b) x| ≤ M := by
  have hm0 := tailBound_nonneg hb
  have hm1 := tailBound_lt_one hb
  exact periodicDecoder_derivatives_bounded (by linarith) (by linarith) (by linarith) n

theorem safe_read_exact {b N : ℕ} (hb : 2 ≤ b) (C : ∀ n, Block b (width N n)) (n : ℕ) :
    safeDecoder b ((b : ℝ) ^ scale N n * donor b N C n) = (C n).code ∧
    safeDecoder b ((b : ℝ) ^ (scale N n + 1 + width N n) * donor b N C n) = (C n).rightCode ∧
    safeDecoder b ((b : ℝ) ^ (scale N n + 1) * donor b N C n) -
      (b : ℝ)⁻¹ ^ width N n *
        safeDecoder b ((b : ℝ) ^ (scale N n + 1 + width N n) * donor b N C n) = (C n).leftCode :=
  read_exact hb C (safeDecoder_periodic b) (fun _ hx => safeDecoder_on_safe hb hx) n

theorem history_nonneg {b N : ℕ} (hb : 0 < b)
    (C : ∀ n, Block b (width N n)) (parity n : ℕ) :
    0 ≤ history b N C parity n := by
  apply sum_nonneg
  intro j _hj
  exact mul_nonneg (epsilon_nonneg hb N j) (C j).code_nonneg

theorem history_le {b N : ℕ} (hb : 2 ≤ b)
    (C : ∀ n, Block b (width N n)) (parity n : ℕ) :
    history b N C parity n ≤ ∑ j ∈ range (n + 1), epsilon b N j := by
  calc
    history b N C parity n ≤
        ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = parity), epsilon b N j := by
      apply sum_le_sum
      intro j _hj
      apply mul_le_of_le_one_right (epsilon_nonneg (by omega) N j)
      exact ((C j).code_le hb).trans (tailBound_lt_one hb).le
    _ ≤ ∑ j ∈ range (n + 1), epsilon b N j := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro j _hj _
      exact epsilon_nonneg (by omega) N j

theorem history_small {b N : ℕ} (hb : 4 ≤ b)
    (C : ∀ n, Block b (width N n)) (parity n : ℕ) :
    history b N C parity n < 1 / 4 :=
  ((history_le (by omega) C parity n).trans (epsilon_sum_range_le (by omega) N (n + 1))).trans_lt
    (initial_epsilon_small hb N)

theorem history_succ {b N : ℕ} (C : ∀ n, Block b (width N n)) (parity n : ℕ) :
    history b N C parity (n + 1) = history b N C parity n +
      if (n + 1) % 2 = parity then epsilon b N (n + 1) * (C (n + 1)).code else 0 := by
  simp only [history]
  rw [range_add_one, filter_insert]
  by_cases h : (n + 1) % 2 = parity
  · simp [h, add_comm]
  · simp [h]

theorem alternating_histories_step {b N : ℕ} (C : ∀ n, Block b (width N n)) (n : ℕ) :
    history b N C (n % 2) (n + 1) = donor b N C n ∧
    history b N C ((n + 1) % 2) (n + 1) = history b N C ((n + 1) % 2) n +
      epsilon b N (n + 1) * (C (n + 1)).code := by
  have hparity : (n + 1) % 2 ≠ n % 2 := by omega
  simp [history_succ, hparity, donor]

theorem history_interpolation_mem {b N : ℕ} (hb : 4 ≤ b)
    (C : ∀ n, Block b (width N n)) (parity n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    (1 - u) * history b N C parity n + u * history b N C parity (n + 1) ∈
      Set.Ico 0 (1 / 4 : ℝ) := by
  have ha0 := history_nonneg (by omega : 0 < b) C parity n
  have hb0 := history_nonneg (by omega : 0 < b) C parity (n + 1)
  have ha1 := history_small hb C parity n
  have hb1 := history_small hb C parity (n + 1)
  refine ⟨add_nonneg (mul_nonneg (by linarith [hu.2]) ha0) (mul_nonneg hu.1 hb0), ?_⟩
  have h : (1 - u) * ((1 / 4 : ℝ) - history b N C parity n) +
      u * ((1 / 4 : ℝ) - history b N C parity (n + 1)) > 0 := by
    rcases hu.1.eq_or_lt with h | h
    · rw [← h]
      simp
      linarith
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (by linarith [hu.2]) (by linarith)) (mul_pos h (by linarith))
  linarith

end Alternating.Memory

end OAI
