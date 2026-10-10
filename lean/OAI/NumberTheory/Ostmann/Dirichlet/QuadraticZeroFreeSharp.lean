import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveTransfer
import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import OAI.NumberTheory.Ostmann.Dirichlet.QuadraticPolePenaltySharp
import OAI.NumberTheory.Ostmann.Reuse.SiegelGap

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

theorem exists_primitive_quadratic_log_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive → chi ≠ 1 → chi^2 = 1 →
      ∀ s : ℂ, 1-c/modulusHeight q s.im ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cd,hcd,hdisk⟩ := exists_primitive_real_zero_free_disk
  obtain ⟨K,hK,hineq⟩ := exists_quadratic_zero_reciprocal_bound_sharp cd hcd
  let delta : ℝ := min (1/(16*(K+1))) (cd/4)
  have hd : 0 < delta := lt_min (by positivity) (by positivity)
  have hdK : delta ≤ 1/(16*(K+1)) := min_le_left _ _
  have hdcd : delta ≤ cd/4 := min_le_right _ _
  have hd8 : delta ≤ 1/8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*(K+1))).mp hdK
    nlinarith
  have hKd : K*delta ≤ 1/16 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*(K+1))).mp hdK
    nlinarith
  have hdsq : delta^2/cd^2 ≤ 1/16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hcd)).mpr
    nlinarith [sq_nonneg (cd/4-delta)]
  let c : ℝ := min (delta/4) (cd/4)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcδ : c ≤ delta/4 := min_le_left _ _
  have hcc : c ≤ cd/2 := by have h := min_le_right (delta/4) (cd/4); change c ≤ cd/4 at h; linarith
  refine ⟨c,hc,?_⟩
  intro q _ hq chi hprim hchi hsq s hs hzero
  have hb1 : s.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  let H : ℝ := modulusHeight q s.im
  have hbase := modulusHeight_ge_one q s.im
  have hH : 1 ≤ H := hbase
  have hHp : 0 < H := by linarith
  let x : ℝ := delta/H
  have hxp : 0 < x := by dsimp only [x]; positivity
  have hxd : x ≤ delta := by
    apply (div_le_iff₀ hHp).mpr
    nlinarith
  have hclose : 1-s.re ≤ x/4 := by
    have h : c/H ≤ (delta/4)/H := div_le_div_of_nonneg_right hcδ hHp.le
    have he : (delta/4)/H = x/4 := by dsimp only [x]; ring
    rw [he] at h
    change 1-c/H ≤ s.re at hs
    linarith
  have hb34 : 3/4 ≤ s.re := by linarith
  have hsigma : 1 < 1+x := by linarith
  have hsigma2 : 1+x ≤ 2 := by linarith
  have hz : DirichletCharacter.LFunction chi ((s.re:ℂ)+(s.im:ℂ)*Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzero
  have hheight : cd/(2*Real.log (q:ℝ)) ≤ |s.im| := by
    by_contra! hlow
    have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq
    have hL : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
    have hLH : Real.log (q:ℝ) ≤ H := by
      have ht : 0 ≤ Real.log (|s.im|+6) := Real.log_nonneg (by have := abs_nonneg s.im; linarith)
      have hle : Real.log (q:ℝ) ≤ modulusHeight q s.im := by unfold modulusHeight; linarith
      dsimp only [H]
      nlinarith
    have hbeta : 1-s.re ≤ cd/(2*Real.log (q:ℝ)) := by
      calc
        _ ≤ c/H := by change 1-c/H ≤ s.re at hs; linarith
        _ ≤ c/Real.log (q:ℝ) := div_le_div_of_nonneg_left hc.le hL hLH
        _ ≤ (cd/2)/Real.log (q:ℝ) := div_le_div_of_nonneg_right hcc hL.le
        _ = _ := by ring
    have hnorm : ‖s-1‖ ≤ cd/Real.log (q:ℝ) := by
      have h := Complex.norm_le_abs_re_add_abs_im (s-1)
      simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero] at h
      rw [abs_of_neg (by linarith : s.re-1 < 0)] at h
      have he : 2*(cd/(2*Real.log (q:ℝ))) = cd/Real.log (q:ℝ) := by ring
      linarith
    have hreal : ∀ a : ZMod q, (chi a).im = 0 :=
      (RealCharacterAnalysis.real_values_iff_quadratic chi).mpr
        (MulChar.isQuadratic_iff_sq_eq_one.mpr hsq)
    exact hdisk q hq chi hprim hchi hreal s hnorm hzero
  have hr := hineq q hq chi hchi hsq (1+x) s.re s.im hsigma hsigma2 hb34 hb1 hheight hz
  let y : ℝ := 1+x-s.re
  have hyp : 0 < y := by dsimp only [y]; linarith
  have hy : y ≤ (5/4)*x := by dsimp only [y]; linarith
  have hKx : (K*H+x*H^2/cd^2)*x ≤ 1/8 := by
    have he : (K*H+x*H^2/cd^2)*x = K*delta+delta^2/cd^2 := by
      dsimp only [x]
      field_simp
    rw [he]
    linarith
  change 4/y ≤ 3/(1+x-1)+K*H+(1+x-1)*H^2/cd^2 at hr
  rw [add_sub_cancel_left] at hr
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hyp).mp hr) hxp.le
  have he : (3/x+K*H+x*H^2/cd^2)*y*x =
      3*y+(K*H+x*H^2/cd^2)*x*y := by field_simp; ring
  rw [he] at h
  have hKy := mul_le_mul_of_nonneg_right hKx hyp.le
  nlinarith only [h,hKy,hy,hxp]

end Ostmann.Dirichlet

end OAI
