import OAI.NumberTheory.Ostmann.Dirichlet.ZetaZeroInequality

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

theorem exists_zeta_large_height_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 ≤ |s.im| →
      1-c/Real.log (|s.im| + 6) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨K, hK, hineq⟩ := exists_zeta_zero_reciprocal_bound
  let delta : ℝ := 1/(8*(K+1))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hd8 : delta ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*(K+1))).mpr
    nlinarith
  have hKd : K*delta ≤ 1/8 := by
    dsimp only [delta]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 8*(K+1))).mpr
    nlinarith
  let c : ℝ := delta/4
  refine ⟨c, by dsimp only [c]; positivity, ?_⟩
  intro s ht hs hzero
  have hb1 : s.re < 1 := by
    by_contra! h
    exact riemannZeta_ne_zero_of_one_le_re h hzero
  let H : ℝ := Real.log (|s.im| + 6)
  have hH : 1 ≤ H := zeta_height_ge_one s.im
  have hHp : 0 < H := by linarith
  let x : ℝ := delta/H
  have hxp : 0 < x := by dsimp only [x]; positivity
  have hxd : x ≤ delta := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have hclose : 1-s.re ≤ x/4 := by
    have he : c/H = x/4 := by dsimp only [c,x]; ring
    change 1-c/H ≤ s.re at hs
    rw [he] at hs
    linarith
  have hb34 : 7/8 ≤ s.re := by linarith
  have hsigma : 1 < 1+x := by linarith
  have hsigma2 : 1+x ≤ 2 := by linarith
  have hz : riemannZeta ((s.re:ℂ)+(s.im:ℂ)*Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzero
  have hr := hineq (1+x) s.re s.im hsigma hsigma2 hb34 hb1 ht hz
  let y : ℝ := 1+x-s.re
  have hyp : 0 < y := by dsimp only [y]; linarith
  have hy : y ≤ (5/4)*x := by dsimp only [y]; linarith
  have hKx : K*H*x ≤ 1/8 := by
    have he : K*H*x = K*delta := by dsimp only [x]; field_simp
    rw [he]
    exact hKd
  change 4/y ≤ 3/(1+x-1)+K*H at hr
  rw [add_sub_cancel_left] at hr
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hyp).mp hr) hxp.le
  have he : (3/x+K*H)*y*x = 3*y+K*H*x*y := by
    field_simp
  rw [he] at h
  have hKy := mul_le_mul_of_nonneg_right hKx hyp.le
  nlinarith only [h, hKy, hy, hxp]

end Ostmann.Dirichlet

end OAI
