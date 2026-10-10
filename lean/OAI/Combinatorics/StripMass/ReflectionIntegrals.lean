import Mathlib
import OAI.Combinatorics.StripMass.ReflectionFractions

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory
lemma integral_reflectionResidueKernel_eq_zero_index {n : ℕ} {x : ℝ}
    (i : Fin (n+1)) :
    (∫ z, reflectionResidueKernel (n+1) x i z ∂unitCubeMeasure (n+1)) =
      ∫ z, reflectionResidueKernel (n+1) x 0 z ∂unitCubeMeasure (n+1) := by
  have he := (measurePreserving_piCongrLeft (fun _ : Fin (n+1) => volume.restrict (Ioo (0:ℝ) 1))
    (Equiv.swap 0 i).symm).integral_comp' (reflectionResidueKernel (n+1) x 0)
  simp only [StripPfaffian.piCongrLeft_const_apply, Equiv.symm_symm] at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [ae_unitCube (n+1)] with z hz
  rw [reflectionResidueKernel_perm x (fun i => (hz i).1.le), Equiv.swap_apply_left]

lemma integral_reflectionResidueKernel_zero_index {n : ℕ} {x : ℝ} (hx : 0 < x) :
    (∫ z, reflectionResidueKernel (n+1) x 0 z ∂unitCubeMeasure (n+1)) =
      2 * ∫ u in Ioo (0:ℝ) 1, (meanCharacteristic n).eval u * omega u / (x+u) := by
  rw [integral_unitCube_cons, integral_prod _ (integrable_unitCube_cons (integrable_reflectionResidueKernel hx 0)),
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  calc
    _ = ∫ y, 2*omega u/(x+u)*((∏ j, (y j-u))*density n y) ∂unitCubeMeasure n := by
      apply integral_congr_ae
      filter_upwards [ae_unitCube n] with y hy
      exact reflectionResidueKernel_cons x hu.1 (fun i => (hy i).1)
    _ = _ := by rw [integral_const_mul, ← meanCharacteristic_eval]; ring

lemma reflection_partialFractions_density {n : ℕ} {y : Fin (n+1) → ℝ}
    (hy : ∀ i, 0 < y i) {x : ℝ} (hx : 0 ≤ x) :
    reflectionProduct (n+1) x y * density (n+1) y =
      density (n+1) y - x * ∑ i, reflectionResidueKernel (n+1) x i y := by
  by_cases hi : Function.Injective y
  · rw [reflection_partialFractions_distinct (Nat.succ_pos n) hy hi hx, sub_mul,
      one_mul, mul_assoc, Finset.sum_mul]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold reflectionResidueKernel
    ring
  · simp only [density_zero_of_not_injective hi, reflectionResidueKernel,
      mul_zero, zero_div, Finset.sum_const_zero, sub_self]

lemma expectation_reflection_cauchy (n : ℕ) {x : ℝ} (hx : 0 < x) :
    expectation (n+1) (reflectionProduct (n+1) x) =
      1 - (2*((n:ℝ)+1)/(∫ z, density (n+1) z ∂unitCubeMeasure (n+1))) *
        ∑ k : Fin (n+1), (meanCharacteristic n).coeff k.val * transformedBasis k.val x := by
  have hD : (∫z, density (n+1) z ∂unitCubeMeasure (n+1)) ≠ 0 := by
    rw [integral_density_unitCube]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (n+1)) (normalizer_pos _).ne'
  rw [expectation_reflection_unitCube (n+1) hx.le]
  have he : (∫ y, reflectionProduct (n+1) x y * density (n+1) y ∂unitCubeMeasure (n+1)) =
      (∫ y, density (n+1) y ∂unitCubeMeasure (n+1)) -
        x * ((n:ℝ)+1) * (2 * ∫ u in Ioo (0:ℝ) 1, (meanCharacteristic n).eval u * omega u / (x+u)) := by
    calc
      _ = ∫ y, density (n+1) y - x * ∑ i, reflectionResidueKernel (n+1) x i y ∂unitCubeMeasure (n+1) := by
        apply integral_congr_ae
        filter_upwards [ae_unitCube (n+1)] with y hy
        exact reflection_partialFractions_density (fun i => (hy i).1) hx.le
      _ = _ := by
        rw [integral_sub (integrable_density_unitCube (n+1))
          ((integrable_finsetSum _ (fun i _ => integrable_reflectionResidueKernel hx i)).const_mul x),
          integral_const_mul, integral_finsetSum _ (fun i _ => integrable_reflectionResidueKernel hx i)]
        simp only [integral_reflectionResidueKernel_eq_zero_index, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
          integral_reflectionResidueKernel_zero_index hx, mul_assoc]
  rw [he, ← polynomial_transformedBasis (n+1) (meanCharacteristic n) (by have := meanCharacteristic_natDegree n; omega) hx]
  field_simp

 

theorem reflection_expectation_cauchyMomentProblem (n : ℕ) :
    ∃ v : Fin (n+1) → ℝ, CauchyMomentProblem (n+1) 1 v ∧
      ∀ x : ℝ, 0 < x → expectation (n+1) (reflectionProduct (n+1) x) = cauchyDefect (n+1) 1 v x := by
  let v : Fin (n+1) → ℝ := fun k =>
    (2*((n:ℝ)+1)/(∫z, density (n+1) z ∂unitCubeMeasure (n+1))) * (meanCharacteristic n).coeff k.val
  have he (x : ℝ) (hx : 0 < x) : expectation (n+1) (reflectionProduct (n+1) x) =
      cauchyDefect (n+1) 1 v x := by
    rw [expectation_reflection_cauchy n hx]
    simp only [cauchyDefect, v, Finset.mul_sum, mul_assoc]
  refine ⟨v, ?_, he⟩
  intro j
  calc
    _ = ∫ x in Ioo (0:ℝ) 1, momentBasis j.val x * expectation (n+1) (reflectionProduct (n+1) x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [he x hx.1]
    _ = 0 := reflection_expectation_moments j.isLt

end

 

noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators

lemma harmonicCoordinate_natDegree : harmonicCoordinate.natDegree = 4 := by
  unfold harmonicCoordinate
  compute_degree <;> norm_num

lemma harmonicCoordinate_leadingCoeff : harmonicCoordinate.leadingCoeff = -1 := by
  rw [leadingCoeff, harmonicCoordinate_natDegree]
  have he : harmonicCoordinate = (X^2-X^4 : Polynomial ℝ) := by unfold harmonicCoordinate; ring
  rw [he]
  norm_num

lemma degree_lt_implies_natDegree_lt {N : ℕ} (hN : 0 < N) {p : Polynomial ℝ}
    (hp : p.degree < (N : WithBot ℕ)) : p.natDegree < N := by
  by_cases h : p = 0
  · simpa [h] using hN
  · exact (natDegree_lt_iff_degree_lt h).mpr hp

lemma coeff_comp_top_of_le {p q : Polynomial ℝ} {N : ℕ} (hp : p.natDegree ≤ N)
    (hq : q.natDegree ≠ 0) :
    (p.comp q).coeff (N*q.natDegree) = p.coeff N * q.leadingCoeff^N := by
  rcases hp.eq_or_lt with he | he
  · rw [← he]
    exact coeff_comp_degree_mul_degree hq
  · rw [coeff_eq_zero_of_natDegree_lt he, zero_mul]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_comp]
    exact Nat.mul_lt_mul_of_pos_right he (Nat.pos_of_ne_zero hq)

lemma tildePoly_eval_zero (N : ℕ) {p : Polynomial ℝ} (hp : p.natDegree ≤ N) :
    (tildePoly N p).eval 0 = p.coeff N * (1/8:ℝ)^N := by
  have hq : (Polynomial.C (1/8:ℝ)*(1+X)).natDegree = 1 := by compute_degree; norm_num
  have hqL : (Polynomial.C (1/8:ℝ)*(1+X)).leadingCoeff = 1/8 := by
    rw [leadingCoeff, hq]
    norm_num [coeff_C_mul, coeff_add, coeff_one]
  rw [← coeff_zero_eq_eval_zero, tildePoly, coeff_reflect, revAt_zero]
  convert coeff_comp_top_of_le hp (by rw [hq]; norm_num) using 1 <;> simp only [hq, mul_one, hqL]

lemma comp_harmonic_odd (p : Polynomial ℝ) (n : ℕ) :
    (p.comp harmonicCoordinate).coeff (2*n+1) = 0 := by
  have he : harmonicCoordinate = (X*(1-X) : Polynomial ℝ).comp (X^2) := by
    simp only [mul_comp, sub_comp, X_comp, one_comp]
    rfl
  rw [he, ← comp_assoc, ← expand_eq_comp_X_pow, coeff_expand (by norm_num)]
  simp

lemma projection_top_coefficients (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ)) :
    let Q := P.comp harmonicCoordinate + X * J.comp harmonicCoordinate + X^2 * E.comp harmonicCoordinate
    Q.coeff (4*N+1) = (-8:ℝ)^N * (tildePoly N J).eval 0 ∧
      Q.coeff (4*N) = (-8:ℝ)^N * (tildePoly N P).eval 0 := by
  have hn : 0 < N := by omega
  have hen := degree_lt_implies_natDegree_lt hn hE
  have he : (X^2*E.comp harmonicCoordinate).natDegree < 4*N := by
    exact natDegree_mul_le.trans_lt (by rw [natDegree_X_pow, natDegree_comp, harmonicCoordinate_natDegree]; omega)
  have hpcomp : (P.comp harmonicCoordinate).natDegree ≤ 4*N := by
    rw [natDegree_comp, harmonicCoordinate_natDegree]; omega
  have hjN : (J.comp harmonicCoordinate).coeff (4*N) = J.coeff N * (-1:ℝ)^N := by
    simpa only [harmonicCoordinate_natDegree, harmonicCoordinate_leadingCoeff, mul_comm] using
      coeff_comp_top_of_le (q := harmonicCoordinate) hJ (by rw [harmonicCoordinate_natDegree]; norm_num)
  have hpN : (P.comp harmonicCoordinate).coeff (4*N) = P.coeff N * (-1:ℝ)^N := by
    simpa only [harmonicCoordinate_natDegree, harmonicCoordinate_leadingCoeff, mul_comm] using
      coeff_comp_top_of_le (q := harmonicCoordinate) hP (by rw [harmonicCoordinate_natDegree]; norm_num)
  have hjOdd : (X*J.comp harmonicCoordinate).coeff (4*N) = 0 := by
    have ha : 4*N = (4*N-1)+1 := by omega
    rw [ha, coeff_X_mul]
    have hb : 4*N-1 = 2*(2*N-1)+1 := by omega
    rw [hb, comp_harmonic_odd]
  have hscalar (a : ℝ) : a*(-1:ℝ)^N = (-8:ℝ)^N*(a*(1/8:ℝ)^N) := by
    rw [mul_left_comm, ← mul_pow]
    norm_num
  dsimp only
  constructor
  · rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt (by omega : (P.comp harmonicCoordinate).natDegree < 4*N+1),
      coeff_eq_zero_of_natDegree_lt (he.trans_le (by omega)), coeff_X_mul,
      zero_add, add_zero, hjN, tildePoly_eval_zero N hJ]
    exact hscalar _
  · rw [coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt he, add_zero, hjOdd, add_zero,
      hpN, tildePoly_eval_zero N hP]
    exact hscalar _

lemma homogeneousQ_monic {N : ℕ} {g : Polynomial ℝ} (hg : g.Monic) :
    (homogeneousQ N g).Monic := by
  exact (((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)).mul hg

lemma homogeneousQ_natDegree {N : ℕ} {g : Polynomial ℝ} (hg : g.Monic) (hd : g.natDegree = N) :
    (homogeneousQ N g).natDegree = 4*N+1 := by
  rw [homogeneousQ, (((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)).natDegree_mul hg,
    ((monic_X_sub_C C).pow _).natDegree_mul ((monic_X_sub_C c).pow _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one, hd]
  omega

lemma homogeneousQ_nextCoeff (N : ℕ) (hN : 1 ≤ N) {g : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = N) :
    (homogeneousQ N g).coeff (4*N) = g.coeff (N-1) - ((2*N+1:ℕ):ℝ)*C - (N:ℝ)*c := by
  have hdeg := homogeneousQ_natDegree hg hd
  have hn : 0 < (homogeneousQ N g).natDegree := by rw [hdeg]; omega
  rw [show 4*N = (homogeneousQ N g).natDegree-1 by omega, ← nextCoeff_of_natDegree_pos hn,
    homogeneousQ, (((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)).nextCoeff_mul hg,
    ((monic_X_sub_C C).pow _).nextCoeff_mul ((monic_X_sub_C c).pow _),
    (monic_X_sub_C C).nextCoeff_pow, (monic_X_sub_C c).nextCoeff_pow,
    nextCoeff_X_sub_C, nextCoeff_X_sub_C,
    nextCoeff_of_natDegree_pos (by rw [hd]; omega), hd]
  simp only [nsmul_eq_mul]
  ring

lemma projectionD_expectation (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    ∀ x : ℝ, 0 < x → projectionD (tildePoly N J) (tildePoly N E) x =
      (tildePoly N J).eval 0 * expectation N (reflectionProduct N x) := by
  have hEn : E.natDegree < N := degree_lt_implies_natDegree_lt (by omega) hE
  have hdiv : X ∣ tildePoly N E := X_dvd_iff.2 (by
    simpa only [coeff_zero_eq_eval_zero] using tildePoly_zero_of_degree_lt N hE)
  obtain ⟨e, he⟩ := hdiv
  have hen : e.natDegree < N := by
    by_cases he0 : e = 0
    · simp [he0]; omega
    have hb := tildePoly_natDegree_le N hEn.le
    rw [he, natDegree_X_mul he0] at hb
    omega
  have hF : ∀ j : ℕ, j ≤ N → Tendsto
      (fun t : ℝ => (-t)^j * projectionF (tildePoly N P) (tildePoly N J) (tildePoly N E) (-t))
      atTop (𝓝 0) := fun j hj => tilde_F_decay N g P J E hP hJ hEn.le hQ j hj
  obtain ⟨L, hD⟩ := tilde_D_limit N g P J E hP hJ hEn.le hQ
  change Tendsto (fun z : ℝ => projectionD (tildePoly N J) (tildePoly N E) z) atTop (𝓝 L) at hD
  have hDc := projectionD_cauchy (tildePoly N J) e (by simpa only [← he] using hD)
  have hm := projection_moments_of_decay N (tildePoly N P) (tildePoly N J) (tildePoly N E) hF
  let D₀ := (tildePoly N J).eval 0
  let v : Fin N → ℝ := fun k => -(Real.sqrt 2 / Real.pi) * (e.coeff k.val * (-1)^k.val)
  have hev {x : ℝ} (hx : 0 < x) :
      projectionD (tildePoly N J) (tildePoly N E) x = cauchyDefect N D₀ v x := by
    rw [he, hDc x hx, mul_assoc, stieltjes_polynomial_basis N e hen hx]
    simp only [cauchyDefect, v, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add, D₀]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hv : CauchyMomentProblem N D₀ v := by
    intro j
    calc
      _ = ∫ x in Ioo (0:ℝ) 1, x^j.val * (projectionD (tildePoly N J) (tildePoly N E) x * omega x) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx
        dsimp only
        rw [hev hx.1]
        unfold momentBasis
        ring
      _ = 0 := hm j.val j.isLt
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨w, hw, hew⟩ := reflection_expectation_cauchyMomentProblem n
  let w' : Fin (n+1) → ℝ := fun i => D₀ * w i
  have bew (x : ℝ) : cauchyDefect (n+1) D₀ w' x = D₀ * cauchyDefect (n+1) 1 w x := by
    simp only [cauchyDefect, w', mul_sub, mul_one, Finset.mul_sum, mul_assoc]
  have hw' : CauchyMomentProblem (n+1) D₀ w' := by
    intro j
    simp_rw [bew]
    have eq : (fun x => momentBasis j.val x * (D₀ * cauchyDefect (n+1) 1 w x)) =
        fun x => D₀ * (momentBasis j.val x * cauchyDefect (n+1) 1 w x) := by funext x; ring
    rw [eq, integral_const_mul, hw j, mul_zero]
  have huniq : v = w' := (existsUnique_cauchyMomentProblem (n+1) D₀).unique hv hw'
  intro x hx
  rw [hev hx, huniq, bew, ← hew x hx]

lemma tendsto_scaled_fBranch_sq_zero :
    Tendsto (fun t : ℝ => t * fBranch (-t)^2) (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun t : ℝ => (t+Real.sqrt ((t^2+t)/2))/2) := by fun_prop
  have ht : Tendsto (fun t : ℝ => (t+Real.sqrt ((t^2+t)/2))/2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hs := Real.sqrt_mul (sq_nonneg t) ((1-1/(-t))/2)
  have he : t^2*((1-1/(-t))/2) = (t^2+t)/2 := by field_simp; ring
  rw [he, Real.sqrt_sq ht.le] at hs
  rw [fBranch, Real.sq_sqrt (by positivity : 0 ≤ (1+Real.sqrt ((1-1/(-t))/2))/2)]
  linarith [hs]

lemma tendsto_scaled_fBranch_zero :
    Tendsto (fun t : ℝ => t * fBranch (-t)) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun t : ℝ => Real.sqrt (t*(t*fBranch (-t)^2))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ht.mul tendsto_scaled_fBranch_sq_zero).sqrt
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [show t*(t*fBranch (-t)^2) = (t*fBranch (-t))^2 by ring,
    Real.sqrt_sq (mul_nonneg ht.le (by unfold fBranch; positivity))]

lemma projectionF_sub_initial_limit (P J E : Polynomial ℝ) (hE : E.eval 0 = 0) :
    Tendsto (fun t : ℝ => projectionF P J E (-t) - J.eval 0 * fBranch (-t))
      (𝓝[>] 0) (𝓝 (P.eval 0)) := by
  have hdivJ : X ∣ J-Polynomial.C (J.eval 0) := X_dvd_iff.2 (by simp [coeff_zero_eq_eval_zero])
  have hdivE : X ∣ E := X_dvd_iff.2 (by simpa only [coeff_zero_eq_eval_zero] using hE)
  obtain ⟨j, hj⟩ := hdivJ
  obtain ⟨e, he⟩ := hdivE
  have hJ : J = Polynomial.C (J.eval 0) + X*j := by linear_combination hj
  have hp (p : Polynomial ℝ) : Tendsto (fun t : ℝ => p.eval (-t)) (𝓝[>] 0) (𝓝 (p.eval 0)) := by
    simpa only [Function.comp_def, neg_zero] using
      ((p.continuous.comp continuous_neg).tendsto 0).mono_left nhdsWithin_le_nhds
  have hl := ((hp P).sub (tendsto_scaled_fBranch_zero.mul (hp j))).sub
    (tendsto_scaled_fBranch_sq_zero.mul (hp e))
  simp only [zero_mul, sub_zero] at hl
  convert hl using 1
  funext t
  have hj' := congrArg (fun p : Polynomial ℝ => p.eval (-t)) hJ
  simp only [eval_add, eval_C, eval_mul, eval_X] at hj'
  simp only [projectionF, he, eval_mul, eval_X]
  rw [hj']
  ring

lemma defect_resolvent_limit (N : ℕ) :
    Tendsto (fun t : ℝ => ∫ x in Ioo 0 1, momentIntegrand N x * (x/(x+t)))
      (𝓝[>] 0) (𝓝 (∫ x in Ioo 0 1, momentIntegrand N x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (momentIntegrand N)
  · exact Filter.Eventually.of_forall (fun t => ((measurable_momentIntegrand N).mul
      (measurable_id.div (measurable_id.add_const t))).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hv := momentIntegrand_bounds N hx
    have hb : 0 ≤ x/(x+t) ∧ x/(x+t) ≤ 1 := by
      constructor
      · exact div_nonneg hx.1.le (by linarith [hx.1])
      · exact (div_le_one (by linarith [hx.1])).mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hv.1 hb.1)]
    exact mul_le_of_le_one_right hv.1 hb.2
  · exact integrableOn_momentIntegrand N
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hl : Tendsto (fun t : ℝ => momentIntegrand N x * (x/(x+t))) (𝓝 0)
        (𝓝 (momentIntegrand N x * (x/(x+0)))) := by
      exact tendsto_const_nhds.mul (tendsto_const_nhds.div
        (tendsto_const_nhds.add tendsto_id) (by simpa using ne_of_gt hx.1))
    simpa [hx.1.ne'] using hl.mono_left nhdsWithin_le_nhds

lemma projectionF_sub_initial_integral (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) {t : ℝ} (ht : 0 < t) :
    projectionF (tildePoly N P) (tildePoly N J) (tildePoly N E) (-t) -
      (tildePoly N J).eval 0 * fBranch (-t) =
      -(tildePoly N J).eval 0 * C - ((tildePoly N J).eval 0 / Real.pi) *
        ∫ x in Ioo 0 1, momentIntegrand N x * (x/(x+t)) := by
  let D₀ := (tildePoly N J).eval 0
  let D := projectionD (tildePoly N J) (tildePoly N E)
  have hEn : E.natDegree ≤ N := (degree_lt_implies_natDegree_lt (by omega) hE).le
  have hDecay : Tendsto (fun t : ℝ => projectionF (tildePoly N P) (tildePoly N J) (tildePoly N E) (-t))
      atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, projectionF, fBranch, highBranch] using tilde_F_decay N g P J E hP hJ hEn hQ 0 (Nat.zero_le N)
  have hF := projectionF_cauchy _ _ _ hDecay (-t) (neg_neg_of_pos ht)
  have hD := projectionD_expectation N hN g P J E hP hJ hE hQ
  have off : offCut 1 (-t) := by
    intro x hx
    simp only [one_mul]
    linarith [hx.1]
  have hωint := integrableOn_stieltjes integrableOn_omega off
  have hDint := integrableOn_stieltjes (integrableOn_projection_weight (tildePoly N J) (tildePoly N E)) off
  have hf := stieltjes_omega (neg_neg_of_pos ht)
  change fBranch (-t) = C + (1/Real.pi) * ∫ x in Ioo 0 1, omega x / (x-(-t)) at hf
  have hω : realStieltjes 1 omega (-t) = -(∫ x in Ioo 0 1, omega x/(x-(-t))) := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    dsimp only
    rw [one_mul, show -t-x = -(x-(-t)) by ring, div_neg]
  have hsub : realStieltjes 1 (fun x => D x * omega x) (-t) - D₀ * realStieltjes 1 omega (-t) =
      D₀ * ∫ x in Ioo 0 1, momentIntegrand N x * (x/(x+t)) := by
    rw [realStieltjes, realStieltjes, ← integral_const_mul, ← integral_sub hDint (hωint.const_mul D₀),
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    change (projectionD (tildePoly N J) (tildePoly N E) x * omega x) / (-t-1*x) -
      D₀ * (omega x / (-t-1*x)) = D₀ * (momentIntegrand N x * (x/(x+t)))
    rw [hD x hx.1]
    change (D₀ * expectation N (reflectionProduct N x) * omega x)/(-t-1*x) -
      D₀ * (omega x / (-t-1*x)) = D₀ * (momentIntegrand N x * (x/(x+t)))
    unfold momentIntegrand
    have had : x+t ≠ 0 := by linarith [hx.1]
    have hab : -t-1*x = -(x+t) := by ring
    rw [hab, div_neg, div_neg]
    field_simp [hx.1.ne']
    ring
  rw [hF, hf]
  change _ = -D₀*C - (D₀/Real.pi) * _
  change -(1/Real.pi) * realStieltjes 1 (fun x => D x * omega x) (-t) -
    D₀ * (C + 1/Real.pi * _) = _
  rw [eq_add_of_sub_eq hsub, hω]
  ring

 

lemma homogeneous_projection_integral_coefficient (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    (tildePoly N P).eval 0 = -(tildePoly N J).eval 0 * C -
      ((tildePoly N J).eval 0 / Real.pi) * ∫ x in Ioo 0 1, momentIntegrand N x := by
  have hlim := projectionF_sub_initial_limit (tildePoly N P) (tildePoly N J) (tildePoly N E)
    (tildePoly_zero_of_degree_lt N hE)
  have hint := (tendsto_const_nhds (x := -(tildePoly N J).eval 0*C)).sub ((defect_resolvent_limit N).const_mul ((tildePoly N J).eval 0 / Real.pi))
  apply tendsto_nhds_unique hlim
  apply hint.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (projectionF_sub_initial_integral N hN g P J E hP hJ hE hQ ht).symm

lemma eta_pos : 0 < eta := by
  have hd : d = Real.sqrt 2 / 2 := by
    rw [d, lambda, show 2*(Real.pi/8)=Real.pi/4 by ring, Real.cos_pi_div_four]
  have hs : 1 < Real.sqrt 2 := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<2)
  unfold eta
  rw [hd]
  linarith

lemma C_eta_identity : C = eta*(2*C+c) := by
  have ha := Real.cos_add (2*lambda) lambda
  have hs := Real.cos_sub (2*lambda) lambda
  rw [show 2*lambda+lambda=3*Real.pi/8 by unfold lambda; ring] at ha
  rw [show 2*lambda-lambda=lambda by ring] at hs
  change c = d*C - Real.sin (2*lambda)*Real.sin lambda at ha
  change C = d*C + Real.sin (2*lambda)*Real.sin lambda at hs
  have hc : c = (2*d-1)*C := by linarith
  have hd : d = Real.sqrt 2 / 2 := by
    rw [d, lambda, show 2*(Real.pi/8)=Real.pi/4 by ring, Real.cos_pi_div_four]
  have hd2 : d^2 = 1/2 := by rw [hd]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [eta, hc]
  nlinarith [congrArg (fun x : ℝ => 2*C*x) hd2]

 

theorem homogeneous_arch_coefficient_integral (N : ℕ) (hN : 1 ≤ N)
    {g : Polynomial ℝ} (hg : MonicProblem N g) :
    (N:ℝ)*C - eta*g.coeff (N-1) =
      (eta/Real.pi)*∫ x in Ioo 0 1, momentIntegrand N x := by
  obtain ⟨hgm, hgd, P, J, E, hP, hJ, hE, hQ⟩ := hg
  have hcoeff := projection_top_coefficients N hN P J E hP hJ hE
  dsimp only at hcoeff
  rw [← hQ] at hcoeff
  have hdeg := homogeneousQ_natDegree hgm hgd
  have hfirst : 1 = (-8:ℝ)^N * (tildePoly N J).eval 0 := by
    rw [← hcoeff.1, ← hdeg]
    exact (homogeneousQ_monic hgm).coeff_natDegree.symm
  have hsecond := hcoeff.2
  rw [homogeneousQ_nextCoeff N hN hgm hgd] at hsecond
  have hint := homogeneous_projection_integral_coefficient N hN g P J E hP hJ hE hQ
  have hbalance : g.coeff (N-1) = (N:ℝ)*(2*C+c) -
      (∫ x in Ioo 0 1, momentIntegrand N x)/Real.pi := by
    push_cast at hsecond
    linear_combination hsecond + (-8:ℝ)^N * hint +
      (C + (∫ x in Ioo 0 1, momentIntegrand N x)/Real.pi) * hfirst
  linear_combination (N:ℝ)*C_eta_identity - eta*hbalance

 
theorem homogeneous_arch_coefficient_growth :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ g : Polynomial ℝ, MonicProblem N g →
        lo*(N:ℝ)^(3/4:ℝ) ≤ (N:ℝ)*C - eta*g.coeff (N-1) ∧
          (N:ℝ)*C - eta*g.coeff (N-1) ≤ hi*(N:ℝ)^(3/4:ℝ) := by
  obtain ⟨lo, hi, hl, hh, hbound⟩ := positive_arch_integral_growth
  have hc : 0 < eta/Real.pi := div_pos eta_pos Real.pi_pos
  refine ⟨(eta/Real.pi)*lo, (eta/Real.pi)*hi, mul_pos hc hl, mul_pos hc hh, ?_⟩
  intro N hN g hg
  rw [homogeneous_arch_coefficient_integral N hN hg]
  obtain ⟨h1, h2⟩ := hbound N hN
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h1 hc.le
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h2 hc.le

end
end CriticalStrip

end OAI
