import OAI.NumberTheory.Jacobsthal.Primes.ZetaPoleBounds

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz

theorem exists_primitive_real_zero_free_disk :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive → chi ≠ 1 →
      (∀ a : ZMod q, (chi a).im = 0) → ∀ z : ℂ,
      ‖z - 1‖ ≤ c / Real.log (q : ℝ) → DirichletCharacter.LFunction chi z ≠ 0 := by
  obtain ⟨ce, hce, hexceptional⟩ :=
    WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple
  obtain ⟨cg, hcg, hgap⟩ := WeightedTorusJets.dirichletRealZeroBound_proof
  let c : ℝ := min ce (min (cg / 2) (1 / 4))
  have hc : 0 < c := lt_min hce (lt_min (by positivity) (by norm_num))
  have hce' : c ≤ ce := min_le_left _ _
  have hcg' : c ≤ cg / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro q _ hq chi hprim hchi hreal z hz hzero
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 1 < Real.log (q : ℝ) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hlogpos : 0 < Real.log (q : ℝ) := by linarith
  have hz' : ‖z - 1‖ ≤ ce / Real.log (q : ℝ) :=
    hz.trans (div_le_div_of_nonneg_right hce' hlogpos.le)
  have him : z.im = 0 := (hexceptional q hq chi hprim hchi hreal z hz' hzero).1
  have hrad : c / Real.log (q : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ hlogpos).mpr
    nlinarith
  have hre : |z.re - 1| ≤ c / Real.log (q : ℝ) := by
    have h := Complex.abs_re_le_norm (z - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    exact h.trans hz
  have hrep : 0 < z.re := by
    have h := (abs_le.mp (hre.trans hrad)).1
    linarith
  have hrelt : z.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  have hrealz : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  have hzeroR : DirichletCharacter.LFunction chi (z.re : ℂ) = 0 := by
    rw [hrealz]
    exact hzero
  have hlower := hgap q hq chi hprim hchi hreal z.re ⟨hrep, hrelt, hzeroR⟩
  have hupper : (1 - z.re) * Real.log (q : ℝ) ≤ c := by
    apply (le_div_iff₀ hlogpos).mp
    have h := (abs_le.mp hre).1
    linarith
  linarith





lemma zetaPole_real_nonneg {s : ℂ} (hs : 1 ≤ s.re) : 0 ≤ (1/(s-1)).re := by
  simpa using real_zero_term_nonneg (w := s) (rho := (1:ℂ)) 1 (by simpa using hs)

lemma zetaPole_real_eq (s : ℂ) :
    (1/(s-1)).re = (s.re-1)/((s.re-1)^2+s.im^2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, pow_two]

theorem exists_zeta_all_height_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → s.re ≤ 2 →
      (-logDeriv riemannZeta s).re ≤ C*(modulusHeight q s.im)^2+(1/(s-1)).re := by
  obtain ⟨C0,hC0,hsmall⟩ := exists_zeta_small_height_real_bound
  obtain ⟨A,hA,C1,hC1,hlarge⟩ := _root_.Erdos970.LogDerivZetaBndUnif2
  refine ⟨C0+C1+1, by positivity, ?_⟩
  intro q _ s hs hs2
  have hH := modulusHeight_ge_one q s.im
  have hHsq : 1 ≤ (modulusHeight q s.im)^2 := by nlinarith
  by_cases ht : |s.im| ≤ 6
  · have h := hsmall s hs hs2 ht
    have hlift := mul_le_mul_of_nonneg_left hHsq (show 0 ≤ C0+C1+1 by positivity)
    have hbound : C0 ≤ (C0+C1+1)*(modulusHeight q s.im)^2 := by nlinarith only [hlift,hC1]
    linarith
  · have ht6 : 6 < |s.im| := lt_of_not_ge ht
    have ht3 : 3 < |s.im| := by linarith
    have hlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hr : 0 ≤ A/Real.log |s.im| := div_nonneg hA.1.le hlog.le
    have hstrip : s.re ∈ Set.Ici (1-A/(Real.log |s.im|)^1) := by
      change 1-A/(Real.log |s.im|)^1 ≤ s.re
      rw [pow_one]
      linarith
    have hz := hlarge s.re s.im ht3 hstrip
    have hnorm : ‖logDeriv riemannZeta s‖ ≤ C1*(Real.log |s.im|)^2 := by
      simpa only [logDeriv_apply, Complex.re_add_im] using hz
    have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hlq := Real.log_nonneg hq
    have hlogle : Real.log |s.im| ≤ modulusHeight q s.im := by
      have h := Real.log_le_log (by linarith : 0 < |s.im|) (by linarith : |s.im| ≤ |s.im|+6)
      unfold modulusHeight
      linarith
    have hsq : (Real.log |s.im|)^2 ≤ (modulusHeight q s.im)^2 := by nlinarith
    have hreal := (Complex.re_le_norm (-logDeriv riemannZeta s)).trans
      (by simpa only [norm_neg] using hnorm)
    have hmul := mul_le_mul_of_nonneg_left hsq hC1.le
    have hpole := zetaPole_real_nonneg hs.le
    have hlift : C1*(modulusHeight q s.im)^2 ≤ (C0+C1+1)*(modulusHeight q s.im)^2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith only [hreal, hmul, hlift, hpole]

theorem exists_principal_all_height_real_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → s.re ≤ 2 →
      (-logDeriv (DirichletCharacter.LFunctionTrivChar q) s).re ≤
        C*(modulusHeight q s.im)^2+(1/(s-1)).re := by
  obtain ⟨C,hC,hzeta⟩ := exists_zeta_all_height_real_bound
  refine ⟨C+1, by positivity, ?_⟩
  intro q _ s hs hs2
  have h := principal_neg_real_log_derivative_le q hs
  have hz := hzeta q s hs hs2
  have hH := modulusHeight_ge_one q s.im
  have hlog : Real.log (q:ℝ) ≤ modulusHeight q s.im := by
    have hh : 0 ≤ Real.log (|s.im|+6) := Real.log_nonneg (by have := abs_nonneg s.im; linarith)
    unfold modulusHeight
    linarith
  nlinarith only [h, hz, hH, hlog]





lemma real_pole_bound_away_from_zero (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {c sigma t : ℝ} (hc : 0 < c) (hs : 1 < sigma) (hs2 : sigma ≤ 2)
    (ht : c/(2*Real.log (q:ℝ)) ≤ |t|) :
    (1/(((sigma:ℂ)+(2*t:ℝ)*Complex.I)-1)).re ≤
      (1/c^2)*(modulusHeight q t)^2 := by
  have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hL : 0 < Real.log (q:ℝ) := Real.log_pos (by linarith)
  have htpos : 0 < |t| := (div_pos hc (by positivity)).trans_le ht
  have htne : t ≠ 0 := abs_pos.mp htpos
  have htsq : 0 < 4*t^2 := by positivity
  have hc2 : 0 < c^2 := by positivity
  have hct : c ≤ 2*Real.log (q:ℝ)*|t| := by
    have h := (div_le_iff₀ (show 0 < 2*Real.log (q:ℝ) by positivity)).mp ht
    nlinarith only [h]
  have hcSq : c^2 ≤ 4*(Real.log (q:ℝ))^2*t^2 := by
    have h : c^2 ≤ (2*Real.log (q:ℝ)*|t|)^2 := by gcongr
    norm_num only [mul_pow, sq_abs] at h
    exact h
  have hp : Real.log (q:ℝ) ≤ modulusHeight q t := by
    have hh : 0 ≤ Real.log (|t|+6) := Real.log_nonneg (by have := abs_nonneg t; linarith)
    unfold modulusHeight
    linarith
  have hsq : (Real.log (q:ℝ))^2 ≤ (modulusHeight q t)^2 := by gcongr
  rw [zetaPole_real_eq]
  have hr : ((sigma:ℂ)+(2*t:ℝ)*Complex.I).re = sigma := by simp
  have hi : ((sigma:ℂ)+(2*t:ℝ)*Complex.I).im = 2*t := by simp
  rw [hr, hi]
  calc
    _ ≤ 1/(4*t^2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (sigma-1)^2+(2*t)^2) htsq).mpr
      have h := mul_le_mul_of_nonneg_right (show sigma-1 ≤ 1 by linarith) (sq_nonneg (2*t))
      nlinarith only [h, sq_nonneg (sigma-1)]
    _ ≤ (Real.log (q:ℝ))^2/c^2 := (div_le_div_iff₀ htsq hc2).mpr (by nlinarith only [hcSq])
    _ ≤ (modulusHeight q t)^2/c^2 := div_le_div_of_nonneg_right hsq hc2.le
    _ = _ := by ring

theorem exists_quadratic_zero_reciprocal_bound (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi^2 = 1 →
      ∀ sigma beta t : ℝ, 1 < sigma → sigma ≤ 2 → 3/4 ≤ beta → beta < 1 →
      c/(2*Real.log (q:ℝ)) ≤ |t| →
      DirichletCharacter.LFunction chi ((beta:ℂ)+(t:ℂ)*Complex.I) = 0 →
      4/(sigma-beta) ≤ 3/(sigma-1)+K*(modulusHeight q t)^2 := by
  obtain ⟨Cp,hCp,hpen⟩ := uniform_zero_penalty
  obtain ⟨Cu,hCu,hprincipal⟩ := exists_principal_all_height_real_bound
  obtain ⟨Cz,hCz,hzeta⟩ := _root_.Erdos970.strongPnt_triv_bound_zeta
  refine ⟨3*Cz+4*Cp+4*Cu+1/c^2, by positivity, ?_⟩
  intro q _ hq chi hchi hsq sigma beta t hs hs2 hb34 hb1 ht hzero
  have hH := modulusHeight_ge_one q t
  have hHsq : modulusHeight q t ≤ (modulusHeight q t)^2 := by nlinarith
  have hOne : 1 ≤ (modulusHeight q t)^2 := by nlinarith
  have h1 := hpen q chi hchi sigma beta t hs hs2 hb34 hb1 hzero
  have h1' : (-deriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I) /
      DirichletCharacter.LFunction chi ((sigma:ℂ)+(t:ℂ)*Complex.I)).re ≤
      Cp*(modulusHeight q t)^2-1/(sigma-beta) := by
    have hm := mul_le_mul_of_nonneg_left hHsq hCp.le
    change _ ≤ Cp*modulusHeight q t-1/(sigma-beta) at h1
    linarith only [h1,hm]
  have h2 := hprincipal q ((sigma:ℂ)+(2*t:ℝ)*Complex.I) (by simpa using hs) (by simpa using hs2)
  have h2H : (modulusHeight q (2*t))^2 ≤ 4*(modulusHeight q t)^2 := by
    have hh := modulusHeight_double_le q t
    have hH2 := modulusHeight_ge_one q (2*t)
    nlinarith
  have hp := real_pole_bound_away_from_zero q hq hc hs hs2 ht
  have h2' : (-deriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q))
      ((sigma:ℂ)+(2*t:ℝ)*Complex.I) /
      DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) ((sigma:ℂ)+(2*t:ℝ)*Complex.I)).re ≤
      (4*Cu+1/c^2)*(modulusHeight q t)^2 := by
    simp only [show ((sigma:ℂ)+(2*t:ℝ)*Complex.I).im = 2*t by simp,
      DirichletCharacter.LFunctionTrivChar, logDeriv_apply, ← neg_div] at h2
    have hm := mul_le_mul_of_nonneg_left h2H hCu.le
    nlinarith only [h2,hp,hm]
  have hz := hzeta sigma 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  have hz' := (Complex.re_le_norm (-deriv riemannZeta (sigma:ℂ)/riemannZeta (sigma:ℂ))).trans hz
  have hCz' : Cz ≤ Cz*(modulusHeight q t)^2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne hCz
  have hpos := character_log_derivative_positivity chi sigma t hs
  rw [hsq] at hpos
  rw [one_div] at h1' h2'
  simp only [div_eq_mul_inv]
  nlinarith only [hpos,h1',h2',hz',hCz']





theorem exists_primitive_quadratic_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive → chi ≠ 1 → chi^2 = 1 →
      ∀ s : ℂ, 1-c/(modulusHeight q s.im)^2 ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cd,hcd,hdisk⟩ := exists_primitive_real_zero_free_disk
  obtain ⟨K,hK,hineq⟩ := exists_quadratic_zero_reciprocal_bound cd hcd
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
  let c : ℝ := min (delta/4) (cd/4)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcδ : c ≤ delta/4 := min_le_left _ _
  have hcc : c ≤ cd/2 := by have h := min_le_right (delta/4) (cd/4); change c ≤ cd/4 at h; linarith
  refine ⟨c,hc,?_⟩
  intro q _ hq chi hprim hchi hsq s hs hzero
  have hb1 : s.re < 1 := by
    by_contra! h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inl hchi) h hzero
  let H : ℝ := (modulusHeight q s.im)^2
  have hbase := modulusHeight_ge_one q s.im
  have hH : 1 ≤ H := by dsimp only [H]; nlinarith
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
  have hKx : K*H*x ≤ 1/8 := by
    have he : K*H*x = K*delta := by dsimp only [x]; field_simp
    rw [he]
    exact hKd
  change 4/y ≤ 3/(1+x-1)+K*H at hr
  rw [add_sub_cancel_left] at hr
  have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hyp).mp hr) hxp.le
  have he : (3/x+K*H)*y*x = 3*y+K*H*x*y := by field_simp
  rw [he] at h
  have hKy := mul_le_mul_of_nonneg_right hKx hyp.le
  nlinarith only [h,hKy,hy,hxp]





theorem exists_primitive_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive → chi ≠ 1 →
      ∀ s : ℂ, 1-c/(modulusHeight q s.im)^2 ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cn,hcn,hnonquad⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cq,hcq,hquad⟩ := exists_primitive_quadratic_zero_free_region
  refine ⟨min cn cq,lt_min hcn hcq,?_⟩
  intro q _ hq chi hprim hchi s hs
  have hH := modulusHeight_ge_one q s.im
  have hHp : 0 < modulusHeight q s.im := by linarith
  by_cases hsq : chi^2 = 1
  · apply hquad q hq chi hprim hchi hsq s
    have h := div_le_div_of_nonneg_right (min_le_right cn cq)
      (sq_nonneg (modulusHeight q s.im))
    linarith
  · apply hnonquad q chi hsq s
    have h1 : min cn cq/(modulusHeight q s.im)^2 ≤ min cn cq/modulusHeight q s.im :=
      div_le_div_of_nonneg_left (lt_min hcn hcq).le hHp (by nlinarith)
    have h2 : min cn cq/modulusHeight q s.im ≤ cn/modulusHeight q s.im :=
      div_le_div_of_nonneg_right (min_le_left cn cq) hHp.le
    linarith




open scoped BigOperators

lemma character_mod_two_eq_one (chi : DirichletCharacter ℂ 2) : chi = 1 := by
  apply MulChar.ext'
  intro a
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · rw [chi.map_zero, (1 : DirichletCharacter ℂ 2).map_zero]
  · rw [chi.map_one, (1 : DirichletCharacter ℂ 2).map_one]

lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) : chi.primitiveCharacter ≠ 1 := by
  intro h
  apply hchi
  calc
    chi = DirichletCharacter.changeLevel chi.conductor_dvd_level chi.primitiveCharacter :=
      chi.changeLevel_primitiveCharacter.symm
    _ = 1 := by rw [h, DirichletCharacter.changeLevel_one]

lemma conductor_ge_three {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) : 3 ≤ chi.conductor := by
  have h0 := chi.conductor_ne_zero
  have h1 : chi.conductor ≠ 1 := fun h => hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have h2 : chi.conductor ≠ 2 := by
    intro h
    have haux : ∀ n : ℕ, n=2 → ∀ psi : DirichletCharacter ℂ n, psi=1 := by
      intro n hn psi
      subst n
      exact character_mod_two_eq_one psi
    exact primitiveCharacter_ne_one chi hchi (haux _ h chi.primitiveCharacter)
  omega

lemma localEulerFactor_ne_zero_of_re_pos {p : ℕ} (hp : p.Prime) {alpha s : ℂ}
    (ha : ‖alpha‖ ≤ 1) (hs : 0 < s.re) : localEulerFactor alpha p s ≠ 0 := by
  have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : ‖(p:ℂ)^(-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    calc
      _ < (p:ℝ)^(0:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
      _ = _ := Real.rpow_zero _
  have hu : ‖alpha*(p:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans_lt (by simpa using hpow)
  intro hz
  have he : alpha*(p:ℂ)^(-s) = 1 := (sub_eq_zero.mp hz).symm
  rw [he,norm_one] at hu
  exact (lt_irrefl 1) hu

lemma LFunction_changeLevel_ne_zero_iff {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (chi : DirichletCharacter ℂ M) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction (DirichletCharacter.changeLevel hMN chi) s ≠ 0 ↔
      DirichletCharacter.LFunction chi s ≠ 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hMN chi (Or.inl hchi), mul_ne_zero_iff]
  have hp : (∏ p ∈ N.primeFactors, (1-chi p*(p:ℂ)^(-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact localEulerFactor_ne_zero_of_re_pos (Nat.prime_of_mem_primeFactors hp)
      (chi.norm_le_one p) hs
  exact and_iff_left hp

lemma LFunction_primitive_ne_zero_iff {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
    DirichletCharacter.LFunction chi s ≠ 0 ↔
      DirichletCharacter.LFunction chi.primitiveCharacter s ≠ 0 := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have h := LFunction_changeLevel_ne_zero_iff chi.conductor_dvd_level chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi) hs
  rwa [chi.changeLevel_primitiveCharacter] at h

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
