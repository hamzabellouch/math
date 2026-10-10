import OAI.NumberTheory.JointDickman.Amplification.ZeroFreeBounds

namespace OAI

/-! # A small zero-free strip for primitive nonprincipal characters

The width may be an arbitrary fixed negative power of the modulus and height.
This is sufficient when both parameters are bounded by powers of a logarithm.
-/
namespace JointDickman
open Complex Set

private theorem half_plane_lipschitz {f : ℂ → ℂ} {a R D : ℝ}
    (hf : Differentiable ℂ f)
    (hb : ∀ s : ℂ, a ≤ s.re → ‖s‖ ≤ R → ‖deriv f s‖ ≤ D)
    {z w : ℂ} (hz : a ≤ z.re) (hw : a ≤ w.re)
    (hzn : ‖z‖ ≤ R) (hwn : ‖w‖ ≤ R) :
    ‖f z - f w‖ ≤ D * ‖z-w‖ := by
  let S := {s : ℂ | a ≤ s.re} ∩ Metric.closedBall 0 R
  have hS : Convex ℝ S := (convex_halfSpace_re_ge a).inter (convex_closedBall 0 R)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := S) (fun z _ => hf z) ?_ hS
    ⟨hw, by simpa only [Metric.mem_closedBall, dist_zero_right] using hwn⟩
    ⟨hz, by simpa only [Metric.mem_closedBall, dist_zero_right] using hzn⟩
  intro s hs
  exact hb s hs.1 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hs.2)

/-- A Siegel-type strip, with an ineffective constant but uniform modulus and height. -/
theorem primitive_character_zero_free_strip {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ,
          1 - A * (((q:ℝ)+2)*(|t|+2))^(-ε) ≤ σ → σ ≤ 2 →
          A * (((q:ℝ)+2)*(|t|+2))^(-ε) ≤ ‖χ.LFunction (σ + I*t)‖ := by
  obtain ⟨c,hc,hl⟩ := LargePrimeGaps.nonprincipal_strip_lower
    (show 0 < ε/2 by positivity) (show ε/2 ≤ 1 by linarith)
  obtain ⟨K,hK,hd⟩ := LargePrimeGaps.LFunction_deriv_norm_small_power
    (show 0 < ε/4 by positivity) (show ε/4 ≤ 1/2 by linarith)
  let D := K * (4:ℝ)^(ε/2)
  have hD : 0 < D := by dsimp [D]; positivity
  let A := min (ε/8) (min (1/4) (min (c/2) (c/(2*D))))
  have hA : 0 < A := by dsimp [A]; positivity
  have hAe : A ≤ ε/8 := min_le_left _ _
  have hA4 : A ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hAc : A ≤ c/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAD : A ≤ c/(2*D) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨A,hA,hA4,?_⟩
  intro q _ χ hp hn σ t hσ hσ2
  let W : ℝ := ((q:ℝ)+2)*(|t|+2)
  have hW : 1 ≤ W := by dsimp [W]; nlinarith [Nat.cast_nonneg (α := ℝ) q, abs_nonneg t]
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hpw : 0 < W^(-ε) := Real.rpow_pos_of_pos hW0 _
  have hpw1 : W^(-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
  have hpw2 : W^(-ε) ≤ W^(-(ε/2)) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  have hsmall : A * W^(-ε) ≤ ε/8 :=
    (mul_le_of_le_one_right hA.le hpw1).trans hAe
  have hσ0 : 0 ≤ σ := by change 1-A*W^(-ε) ≤ σ at hσ; linarith
  have hwanted : A*W^(-ε) ≤ (c/2)*W^(-(ε/2)) :=
    mul_le_mul hAc hpw2 hpw.le (by positivity)
  by_cases hσ1 : 1 ≤ σ
  · exact hwanted.trans ((mul_le_mul_of_nonneg_right (by linarith : c/2 ≤ c)
      (Real.rpow_nonneg hW0.le _)).trans (hl q χ hp hn σ t hσ1 hσ2))
  have hσlt : σ < 1 := lt_of_not_ge hσ1
  let w : ℂ := 1 + I*t
  let z : ℂ := σ + I*t
  have hnorm (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
      ‖(u:ℂ)+I*t‖+2 ≤ 4*(|t|+2) := by
    have hh := Complex.norm_le_abs_re_add_abs_im ((u:ℂ)+I*t)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.add_im,Complex.mul_im,one_mul,zero_add] at hh
    rw [abs_of_nonneg hu] at hh
    linarith [abs_nonneg t]
  have hb (s : ℂ) (hs : 1-ε/8 ≤ s.re) (hsn : ‖s‖ ≤ 4*(|t|+2)-2) :
      ‖deriv χ.LFunction s‖ ≤ D*W^(ε/2) := by
    have hbase : ((q:ℝ)+2)*(‖s‖+2) ≤ 4*W := by
      dsimp [W]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ q+2 by positivity)
        (show 0 ≤ 4*(|t|+2)-(‖s‖+2) by linarith)]
    have he := hd q χ hn s (by linarith)
    rw [show 2*(ε/4) = ε/2 by ring] at he
    calc
      _ ≤ K*(((q:ℝ)+2)*(‖s‖+2))^(ε/2) := he
      _ ≤ K*(4*W)^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hbase (by positivity)) hK.le
      _ = D*W^(ε/2) := by rw [Real.mul_rpow (by norm_num) hW0.le]; dsimp [D]; ring
  have hzre : 1-ε/8 ≤ z.re := by
    have hh : 1-ε/8 ≤ σ := by
      change 1-A*W^(-ε) ≤ σ at hσ
      linarith
    simpa [z] using hh
  have hwre : 1-ε/8 ≤ w.re := by
    simpa [w] using (show 1-ε/8 ≤ (1:ℝ) by linarith)
  have hzN : ‖z‖ ≤ 4*(|t|+2)-2 := by dsimp [z]; linarith [hnorm σ hσ0 hσlt.le]
  have hwN : ‖w‖ ≤ 4*(|t|+2)-2 := by
    have hh := hnorm 1 zero_le_one le_rfl
    norm_num only [ofReal_one] at hh
    dsimp [w]
    linarith
  have hdiff := half_plane_lipschitz (DirichletCharacter.differentiable_LFunction hn)
    hb hzre hwre hzN hwN
  have hdist : ‖z-w‖ = 1-σ := by
    have he : z-w = ((σ-1:ℝ):ℂ) := by dsimp [z,w]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  rw [hdist] at hdiff
  have hdiff' : ‖χ.LFunction z-χ.LFunction w‖ ≤ (c/2)*W^(-(ε/2)) := by
    calc
      _ ≤ D*W^(ε/2)*(1-σ) := hdiff
      _ ≤ D*W^(ε/2)*(A*W^(-ε)) := mul_le_mul_of_nonneg_left
        (by change 1-A*W^(-ε) ≤ σ at hσ; linarith) (by positivity)
      _ = (D*A)*W^(-(ε/2)) := by
        rw [mul_mul_mul_comm, ←Real.rpow_add hW0]
        congr 2
        ring
      _ ≤ (c/2)*W^(-(ε/2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hW0.le _)
        have hh := (le_div_iff₀ (by positivity : 0 < 2*D)).mp hAD
        nlinarith
  have hline : c*W^(-(ε/2)) ≤ ‖χ.LFunction w‖ := by
    simpa only [w, ofReal_one] using hl q χ hp hn 1 t le_rfl (by norm_num)
  have htri : ‖χ.LFunction w‖ ≤ ‖χ.LFunction w-χ.LFunction z‖+‖χ.LFunction z‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (χ.LFunction w-χ.LFunction z) (χ.LFunction z)
  rw [norm_sub_rev] at hdiff'
  have hh : (c/2)*W^(-(ε/2)) ≤ ‖χ.LFunction z‖ := by linarith
  exact hwanted.trans hh

/-- The same strip is zero-free for imprimitive nonprincipal characters. -/
theorem nonprincipal_character_zero_free_strip {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ t : ℝ,
        1 - A * (((q:ℝ)+2)*(|t|+2))^(-ε) ≤ σ → σ ≤ 2 →
        χ.LFunction (σ + I*t) ≠ 0 := by
  obtain ⟨A,hA,hA4,h⟩ := primitive_character_zero_free_strip hε hε1
  refine ⟨A,hA,hA4,?_⟩
  intro q _ χ hn σ t hσ hσ2
  let ψ := χ.primitiveCharacter
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : ψ ≠ 1 := by
    intro he
    apply hn
    rw [←χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from he,
      DirichletCharacter.changeLevel_one]
  have hc : (χ.conductor:ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hpow : (((q:ℝ)+2)*(|t|+2))^(-ε) ≤
      (((χ.conductor:ℝ)+2)*(|t|+2))^(-ε) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by linarith)
  have hp := h χ.conductor ψ χ.primitiveCharacter_isPrimitive hψ σ t
    (by nlinarith [mul_le_mul_of_nonneg_left hpow hA.le]) hσ2
  have hne : ψ.LFunction (σ+I*t) ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)) hp)
  have hbase : 1 ≤ ((q:ℝ)+2)*(|t|+2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) q, abs_nonneg t]
  have hpw := Real.rpow_le_one_of_one_le_of_nonpos hbase (show -ε ≤ 0 by linarith)
  have hσ0 : 0 < σ := by
    have hh := mul_le_of_le_one_right hA.le hpw
    linarith
  rw [←χ.changeLevel_primitiveCharacter,
    DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (Or.inl hψ)]
  apply mul_ne_zero hne
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpn : ‖(p:ℂ)^(-((σ:ℂ)+I*t))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hprime.pos]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (by linarith)
  have hb : ‖ψ (p:ZMod χ.conductor)*(p:ℂ)^(-((σ:ℂ)+I*t))‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)).trans_lt hpn
  intro he
  have heq : ψ (p:ZMod χ.conductor)*(p:ℂ)^(-((σ:ℂ)+I*t)) = 1 := sub_eq_zero.mp he |>.symm
  rw [heq, norm_one] at hb
  exact lt_irrefl _ hb

end JointDickman

end OAI
