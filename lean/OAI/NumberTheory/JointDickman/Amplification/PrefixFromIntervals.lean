import OAI.NumberTheory.JointDickman.Amplification.ScaledIntervalCover

namespace OAI

/-! # Assembling local counting-scale means into a full initial interval -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_mean_from_scaled_intervals
    (T : ℕ → ℕ) (scale : ℕ → ℝ) (hT : ∀ᶠ B in atTop, 0 < T B)
    (hscale : Tendsto scale atTop atTop)
    (f : ℕ → ℕ → (ℕ → ℝ) → ℕ → ℝ) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (hpos : ∀ B n σ, (∀ u, |σ u| ≤ 3) → ∀ u, 0 ≤ f B n σ u)
    (hcap : ∀ᶠ B in atTop, ∀ n σ, (∀ u, |σ u| ≤ 3) → ∀ u, f B n σ u ≤ D)
    (hlocal : ∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ σ, (∀ u, |σ u| ≤ 3) →
      (1/(a*(T B+1)*scale n))*(∑ u ∈ Ico ⌈a*(T B+1)*scale n⌉₊ ⌊2*(a*(T B+1)*scale n)⌋₊,
        f B n σ u) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ σ, (∀ u, |σ u| ≤ 3) →
      (∑ u ∈ range ⌊C*T B*scale n⌋₊, f B n σ u)/(T B*scale n) < ε := by
  intro ε hε
  let a := ε/(16*(D+1))
  have ha : 0 < a := by dsimp [a]; positivity
  let K := ⌈C/a⌉₊
  let S := Icc 2 K
  let V : ℝ := ∑ k ∈ S, (k : ℝ)
  have hV : 0 ≤ V := sum_nonneg (fun k _ => Nat.cast_nonneg k)
  let ν := ε/(16*a*(V+1))
  have hν : 0 < ν := by dsimp [ν]; positivity
  have haD : 4*a*D ≤ ε/4 := by
    have hh : D/(D+1) ≤ 1 := (div_le_one (by linarith : 0 < D+1)).mpr (by linarith)
    calc
      4*a*D = (ε/4)*(D/(D+1)) := by dsimp [a]; field_simp; ring
      _ ≤ (ε/4)*1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ε/4 := mul_one _
  have hνV : 2*a*V*ν < ε/4 := by
    have hh : V/(V+1) < 1 := (div_lt_one (by linarith : 0 < V+1)).mpr (by linarith)
    calc
      2*a*V*ν = (ε/8)*(V/(V+1)) := by dsimp [ν]; field_simp; ring
      _ < (ε/8)*1 := mul_lt_mul_of_pos_left hh (by positivity)
      _ < ε/4 := by linarith
  have hlocals (k : ℕ) (hk : k ∈ S) := hlocal (k*a)
    (mul_pos (by exact_mod_cast (show 0 < k by have := (mem_Icc.mp hk).1; omega)) ha) ν hν
  filter_upwards [hT,hcap,(eventually_all_finset S).mpr hlocals] with B hTB hcapB hlocalB
  have hTr : (1 : ℝ) ≤ T B := by exact_mod_cast hTB
  filter_upwards [(eventually_all_finset S).mpr hlocalB,
    hscale.eventually_gt_atTop (max (1/a) (4*D/ε))] with n hn hsc
  have hsc0 : 0 < scale n := (lt_of_lt_of_le (by positivity : 0 < 1/a) (le_max_left _ _)).trans hsc
  let Y := (T B : ℝ)*scale n
  let X := a*((T B : ℝ)+1)*scale n
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hX : 1 ≤ X := by
    have hs : 1/a < scale n := (le_max_left _ _).trans_lt hsc
    have hs' : 1 < a*scale n := (div_lt_iff₀ ha).mp hs |>.trans_eq (mul_comm _ _)
    dsimp [X]
    nlinarith [mul_nonneg ha.le hsc0.le]
  have hXY : X/Y ≤ 2*a := by
    apply (div_le_iff₀ hY).mpr
    dsimp [X,Y]
    nlinarith [mul_nonneg ha.le hsc0.le]
  have hround : D/Y < ε/4 := by
    have hs : 4*D/ε < scale n := (le_max_right _ _).trans_lt hsc
    have hs' : 4*D < scale n*ε := (div_lt_iff₀ hε).mp hs
    apply (div_lt_iff₀ hY).mpr
    dsimp [Y]
    nlinarith [mul_nonneg (show 0 ≤ (T B : ℝ)-1 by linarith) hsc0.le]
  intro σ hσ
  have hU : (⌊C*T B*scale n⌋₊ : ℝ) ≤ ((K : ℝ)+1)*X := by
    have hK : C ≤ (K : ℝ)*a := (div_le_iff₀ ha).mp (Nat.le_ceil (C/a))
    calc
      (⌊C*T B*scale n⌋₊ : ℝ) ≤ C*T B*scale n := Nat.floor_le (by positivity)
      _ ≤ ((K : ℝ)*a)*((T B : ℝ)+1)*scale n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hK (le_add_of_nonneg_right zero_le_one)
            (Nat.cast_nonneg _) (by positivity)) hsc0.le
      _ = (K : ℝ)*X := by dsimp [X]; ring
      _ ≤ ((K : ℝ)+1)*X := mul_le_mul_of_nonneg_right (by linarith) (by linarith [hX])
  have hcover := scaled_interval_sum_bound hX hD K ⌊C*T B*scale n⌋₊ hU
    (f B n σ) (hpos B n σ hσ) (hcapB n σ hσ)
  have hsum : (∑ k ∈ S, ∑ u ∈ Ico ⌈(k : ℝ)*X⌉₊ ⌊2*((k : ℝ)*X)⌋₊, f B n σ u) ≤ V*X*ν := by
    calc
      _ ≤ ∑ k ∈ S, ((k : ℝ)*X)*ν := by
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (mem_Icc.mp hk).1; omega)
        have hh := (hn k hk σ hσ).le
        have heq : (k : ℝ)*a*(T B+1)*scale n = (k : ℝ)*X := by dsimp [X]; ring
        rw [heq] at hh
        exact (div_le_iff₀ (mul_pos hk0 (by linarith : 0 < X))).mp (by simpa only [one_div_mul_eq_div] using hh) |>.trans_eq (mul_comm _ _)
      _ = V*X*ν := by dsimp [V]; rw [sum_mul,sum_mul]
  apply (div_le_div_of_nonneg_right (hcover.trans (add_le_add le_rfl hsum)) hY.le).trans_lt
  calc
    ((2*X+1)*D+V*X*ν)/Y = 2*D*(X/Y)+D/Y+(V*ν)*(X/Y) := by ring
    _ ≤ 4*a*D+D/Y+2*a*V*ν := by
      have hh₁ := mul_le_mul_of_nonneg_left hXY (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
      have hh₂ := mul_le_mul_of_nonneg_left hXY (mul_nonneg hV hν.le)
      nlinarith
    _ < ε := by linarith

end JointDickman

end OAI
