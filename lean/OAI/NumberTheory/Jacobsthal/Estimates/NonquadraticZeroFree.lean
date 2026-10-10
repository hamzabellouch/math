import OAI.NumberTheory.Jacobsthal.Harmonic.CharacterPositivity

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

noncomputable def modulusHeight (q : ℕ) (t : ℝ) : ℝ := Real.log (q:ℝ)+Real.log (|t|+6)

lemma modulusHeight_ge_one (q : ℕ) [NeZero q] (t : ℝ) : 1 ≤ modulusHeight q t := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have ht := abs_nonneg t
  have hlt : 1 < Real.log (|t|+6) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans (by linarith))
  unfold modulusHeight
  linarith

lemma modulusHeight_double_le (q : ℕ) [NeZero q] (t : ℝ) :
    modulusHeight q (2*t) ≤ 2 * modulusHeight q t := by
  have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq := Real.log_nonneg hq
  have ht := abs_nonneg t
  have htp : 0 < |t|+6 := by linarith
  have h2 : Real.log 2 ≤ Real.log (|t|+6) := Real.log_le_log (by norm_num) (by linarith)
  have he : |2*t| = 2*|t| := by rw [abs_mul]; norm_num
  have hlog : Real.log (|2*t|+6) ≤ Real.log (2*(|t|+6)) :=
    Real.log_le_log (by positivity) (by rw [he]; linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) htp.ne'] at hlog
  unfold modulusHeight
  linarith

theorem exists_nonquadratic_zero_reciprocal_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi^2 ≠ 1 → ∀ sigma beta t : ℝ,
      1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      4/(sigma-beta) ≤ 3/(sigma-1)+K*modulusHeight q t := by
  obtain ⟨Cp, hCp, hp⟩ := uniform_zero_penalty
  obtain ⟨Cu, hCu, hu⟩ := uniform_neg_real_log_derivative
  obtain ⟨Cz, hCz, hz⟩ := _root_.Erdos970.strongPnt_triv_bound_zeta
  refine ⟨3*Cz+4*Cp+2*Cu, by linarith, ?_⟩
  intro q _ chi hsq sigma beta t hs hs2 hb34 hb1 hzero
  have hchi : chi ≠ 1 := by
    intro h
    apply hsq
    rw [h, one_pow]
  have hpen := hp q chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  have hup := hu q (chi^2) hsq sigma (2*t) hs hs2
  have hup' : (-deriv (DirichletCharacter.LFunction (chi^2)) ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
      DirichletCharacter.LFunction (chi^2) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re ≤
      2*Cu*modulusHeight q t := by
    apply hup.trans
    change Cu * modulusHeight q (2*t) ≤ _
    have h := mul_le_mul_of_nonneg_left (modulusHeight_double_le q t) hCu.le
    nlinarith only [h]
  have hzeta := hz sigma 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hzeta
  have hzeta' := (Complex.re_le_norm (-deriv riemannZeta (sigma:ℂ)/riemannZeta (sigma:ℂ))).trans hzeta
  have habsorb : Cz ≤ Cz*modulusHeight q t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (modulusHeight_ge_one q t) hCz
  have hpositive := character_log_derivative_positivity chi sigma t hs
  change _ ≤ Cp*modulusHeight q t-1/(sigma-beta) at hpen
  rw [one_div] at hpen
  simp only [div_eq_mul_inv]
  nlinarith only [hpositive, hpen, hup', hzeta', habsorb]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz

theorem exists_nonquadratic_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi^2 ≠ 1 → ∀ s : ℂ,
      1-c/modulusHeight q s.im ≤ s.re → DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨K, hK, hineq⟩ := exists_nonquadratic_zero_reciprocal_bound
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
  intro q _ chi hsq s hs hzero
  have hchi : chi ≠ 1 := by
    intro h
    apply hsq
    rw [h, one_pow]
  have hb1 : s.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  let H : ℝ := modulusHeight q s.im
  have hH : 1 ≤ H := modulusHeight_ge_one q s.im
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
  have hb34 : 3/4 ≤ s.re := by linarith
  have hsigma : 1 < 1+x := by linarith
  have hsigma2 : 1+x ≤ 2 := by linarith
  have hz : DirichletCharacter.LFunction chi ((s.re:ℂ)+(s.im:ℂ)*Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzero
  have hr := hineq q chi hsq (1+x) s.re s.im hsigma hsigma2 hb34 hb1 hz
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

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
