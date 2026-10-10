import OAI.Probability.BenjaminiSchramm.CrossingExponent

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology

namespace Percolation.BenjaminiSchramm

theorem positive_layer_moment_rate (P : ℕ → ℝ) (hP : ∀ n, 0 < P n)
    (hP0 : 1 ≤ P 0) (hmul : ∀ m n, P (m+n) ≤ P m*P n)
    (C : ℝ) (hbound : ∀ n, P n ≤ C)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlower : ∀ n : ℕ, Real.exp (-A*n-B) ≤ P n) :
    ∃ β : ℝ, 0 ≤ β ∧
      (∀ n : ℕ, Real.exp (-β*n) ≤ P n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        P n ≤ K*Real.exp (-(β-ε)*n)) ∧
      Tendsto (fun n : ℕ => -Real.log (P n)/n) atTop (𝓝 β) := by
  let u : ℕ → ℝ := fun n => Real.log (P n)
  have hu : Subadditive u := by
    intro m n
    have hh := Real.log_le_log (hP (m+n)) (hmul m n)
    rw [Real.log_mul (hP m).ne' (hP n).ne'] at hh
    exact hh
  have hlo (n : ℕ) : -A*n-B ≤ u n := by
    have hh := Real.log_le_log (Real.exp_pos _) (hlower n)
    rwa [Real.log_exp] at hh
  have hbdd : BddBelow (Set.range fun n : ℕ => u n/n) := by
    refine ⟨-A-B,?_⟩
    rintro _ ⟨n,rfl⟩
    by_cases hn : n=0
    · simp only [hn,Nat.cast_zero,div_zero]
      linarith
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      apply (le_div_iff₀ hnpos).mpr
      nlinarith [hlo n]
  let β := -hu.lim
  have hlim0 : Tendsto (fun n : ℕ => u n/n) atTop (𝓝 hu.lim) := hu.tendsto_lim hbdd
  have hlim : Tendsto (fun n : ℕ => -Real.log (P n)/n) atTop (𝓝 β) := by
    simpa only [neg_div,u] using hlim0.neg
  have hlog (n : ℕ) : u n ≤ Real.log C := Real.log_le_log (hP n) (hbound n)
  have hzero : Tendsto (fun n : ℕ => Real.log C/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlimle : hu.lim ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim0 hzero
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (hlog n) (Nat.cast_nonneg n)
  have hβ : 0 ≤ β := neg_nonneg.mpr hlimle
  refine ⟨β,hβ,?_,?_,hlim⟩
  · intro n
    by_cases hn : n=0
    · simpa only [hn,Nat.cast_zero,mul_zero,Real.exp_zero] using hP0
    have hr := (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn) : (0 : ℝ) < n)).mp
      (hu.lim_le_div hbdd hn)
    have hh : -β*(n : ℝ) ≤ Real.log (P n) := by simpa only [β,u,neg_neg] using hr
    have he := Real.exp_le_exp.mpr hh
    rwa [Real.exp_log (hP n)] at he
  · intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      (hlim.eventually (lt_mem_nhds (sub_lt_self β hε)))
    let f : ℕ → ℝ := fun n => P n*Real.exp ((β-ε)*n)
    obtain ⟨i,hi,himax⟩ := Finset.exists_max_image (Finset.range (N+1)) f
      ⟨0,Finset.mem_range.mpr (Nat.succ_pos N)⟩
    let K := max 1 (f i)
    refine ⟨K,lt_of_lt_of_le (by norm_num) (le_max_left _ _),fun n => ?_⟩
    by_cases hn : n < N+1
    · have hK : f n ≤ K := (himax n (Finset.mem_range.mpr hn)).trans (le_max_right _ _)
      have hh := mul_le_mul_of_nonneg_right hK (Real.exp_pos (-(β-ε)*n)).le
      have he : Real.exp ((β-ε)*n)*Real.exp (-(β-ε)*n)=1 := by
        rw [←Real.exp_add]
        ring_nf
        exact Real.exp_zero
      dsimp [f] at hh
      rwa [mul_assoc,he,mul_one] at hh
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hh := (lt_div_iff₀ hnpos).mp (hN n (by omega))
      have he := Real.exp_le_exp.mpr (show Real.log (P n) ≤ -(β-ε)*(n : ℝ) by linarith)
      rw [Real.exp_log (hP n)] at he
      exact he.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _))

end Percolation.BenjaminiSchramm

end

end OAI
