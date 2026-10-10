import OAI.Geometry.RCD.Transport.HyperbolicChord
import OAI.Geometry.RCD.Heat.GaussianCoshComparison

namespace OAI

/-! # Hyperbolic comparison on a finite uniform grid -/

open Set
namespace RegularPointCoordinates

theorem gaussian_grid_comparison (u : ℝ → ℝ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hu0 : 0 ≤ u 0) (hu1 : 0 ≤ u 1)
    (hm : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      Real.exp (-c*(x-y)^2/8)*(u x+u y)/2 ≤ u ((x+y)/2))
    (n : ℕ) (hn : 0 < n)
    (hcoef : 1 ≤ Real.exp (-c*(1/(n:ℝ))^2/2)*Real.cosh (q*(1/(n:ℝ)))) :
    ∀ j : ℕ, j ≤ n → hyperbolicChord q (u 0) (u 1) ((j:ℝ)/n) ≤ u ((j:ℝ)/n) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let d : ℝ := 1/(n:ℝ)
  let a : ℝ := Real.exp (-c*d^2/2)
  let U := fun j : ℕ => u ((j:ℝ)/n)
  let H := fun j : ℕ => hyperbolicChord q (u 0) (u 1) ((j:ℝ)/n)
  have hd : 0 < d := one_div_pos.mpr hnR
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by
    have := sq_pos_of_pos hd
    nlinarith)
  have hprev (j : ℕ) (hj : 0 < j) : ((j-1:ℕ):ℝ)/n=(j:ℝ)/n-d := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    dsimp only [d]
    ring
  have hnext (j : ℕ) : ((j+1:ℕ):ℝ)/n=(j:ℝ)/n+d := by
    push_cast
    dsimp only [d]
    ring
  have hU (j : ℕ) (hj0 : 0 < j) (hjn : j < n) : a*(U (j-1)+U (j+1))/2 ≤ U j := by
    have hp0 : 0 ≤ ((j-1:ℕ):ℝ)/n := div_nonneg (Nat.cast_nonneg _) hnR.le
    have hp1 : ((j-1:ℕ):ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast (show j-1 ≤ n by omega))
    have hn0 : 0 ≤ ((j+1:ℕ):ℝ)/n := div_nonneg (Nat.cast_nonneg _) hnR.le
    have hn1 : ((j+1:ℕ):ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast (show j+1 ≤ n by omega))
    have hs := hm _ ⟨hp0,hp1⟩ _ ⟨hn0,hn1⟩
    have he : (((j-1:ℕ):ℝ)/n+((j+1:ℕ):ℝ)/n)/2=(j:ℝ)/n := by
      rw [hprev j hj0,hnext j]
      ring
    have hf : -c*(((j-1:ℕ):ℝ)/n-((j+1:ℕ):ℝ)/n)^2/8=-c*d^2/2 := by
      rw [hprev j hj0,hnext j]
      ring
    rw [he,hf] at hs
    exact hs
  have hH (j : ℕ) (hj0 : 0 < j) (hjn : j < n) : H j ≤ a*(H (j-1)+H (j+1))/2 := by
    have hs := hyperbolicChord_neighbor_sum q (u 0) (u 1) ((j:ℝ)/n) d
    rw [←hprev j hj0,←hnext j] at hs
    have ht0 : 0 ≤ (j:ℝ)/n := div_nonneg (Nat.cast_nonneg _) hnR.le
    have ht1 : (j:ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hjn.le)
    have hpos : 0 ≤ H j := hyperbolicChord_nonneg hq hu0 hu1 ht0 ht1
    have hh := mul_le_mul_of_nonneg_right hcoef hpos
    rw [one_mul] at hh
    change H j ≤ (a*Real.cosh (q*d))*H j at hh
    calc
      H j ≤ (a*Real.cosh (q*d))*H j := hh
      _ = a*(H (j-1)+H (j+1))/2 := by
        change _ = a*(hyperbolicChord q (u 0) (u 1) (((j-1:ℕ):ℝ)/n)+
          hyperbolicChord q (u 0) (u 1) (((j+1:ℕ):ℝ)/n))/2
        rw [hs]
        dsimp only [H]
        ring
  apply discrete_gaussian_comparison ha0 ha1 _ _ hU hH
  · simp [H,U,hyperbolicChord_zero hq]
  · simp [H,U,hnR.ne',hyperbolicChord_one hq]

end RegularPointCoordinates

end OAI
