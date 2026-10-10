import Mathlib
import OAI.Combinatorics.StripMass.StieltjesLimits

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Polynomial Set Filter
open scoped Topology
theorem C_c_facts : 0 < c ∧ c < C ∧ C ^ 2 + c ^ 2 = 1 ∧
    C ^ 2 * (1 - C ^ 2) = 1 / 8 ∧ c ^ 2 * (1 - c ^ 2) = 1 / 8 ∧
    1 - 2 * C ^ 2 ≠ 0 ∧ 1 - 2 * c ^ 2 ≠ 0 := by
  have hh := branches_sq (u := (0 : ℝ)) (by constructor <;> norm_num)
  rw [highBranch_zero, lowBranch_zero] at hh
  simp only [sub_zero, sqrt_half] at hh
  have hC : 0 ≤ C := by rw [← highBranch_zero]; exact Real.sqrt_nonneg _
  have hc : 0 ≤ c := by rw [← lowBranch_zero]; exact Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sqrt_two_lt_two, hh.1, hh.2.1]

theorem harmonic_eval (b : ℝ) : harmonicCoordinate.eval b = b ^ 2 * (1 - b ^ 2) := by
  simp [harmonicCoordinate]

 

theorem branch_rescaled_tendsto {α : Type*} {l : Filter α} {z b : α → ℝ} {r : ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hb : Tendsto b l (𝓝 r))
    (hh : ∀ᶠ t in l, harmonicCoordinate.eval (b t) = (1 + 1 / z t) / 8)
    (hr : r ^ 2 * (1 - r ^ 2) = 1 / 8) (hrn : r ≠ 0) (hrd : 1 - 2 * r ^ 2 ≠ 0) :
    Tendsto (fun t => z t * (b t - r)) l (𝓝 ((1 / 8) / ((2 * r) * (1 - 2 * r ^ 2)))) := by
  have hd := (hb.add_const r).mul (((hb.pow 2).const_sub 1).sub_const (r ^ 2))
  have hdn : (r + r) * (1 - r ^ 2 - r ^ 2) ≠ 0 := by
    convert mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hrn) hrd using 1
    ring
  have ht := (tendsto_const_nhds : Tendsto (fun _ : α => (1 / 8 : ℝ)) l (𝓝 (1 / 8))).div hd hdn
  have hs : (r + r) * (1 - r ^ 2 - r ^ 2) = (2 * r) * (1 - 2 * r ^ 2) := by ring
  rw [hs] at ht
  apply ht.congr'
  filter_upwards [hz, hh, hd.eventually_ne hdn] with t hzt hht hdt
  simp only [harmonic_eval] at hht
  apply (div_eq_iff hdt).2
  have hbase : (b t - r) * (b t + r) * (1 - b t ^ 2 - r ^ 2) = (1 / z t) / 8 := by
    nlinarith [hht, hr]
  calc (1 / 8 : ℝ) = z t * ((1 / z t) / 8) := by field_simp
       _ = z t * ((b t - r) * (b t + r) * (1 - b t ^ 2 - r ^ 2)) := by rw [hbase]
       _ = z t * (b t - r) * ((b t + r) * (1 - b t ^ 2 - r ^ 2)) := by ring

theorem eventually_small_inverse {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : Tendsto (fun t => 1 / z t) l (𝓝 0)) :
    ∀ᶠ t in l, 1 / z t ∈ Ioo (-1 : ℝ) 1 :=
  hz.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))

theorem highBranch_rescaled {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0)) :
    Tendsto (fun t => z t * (highBranch (1 / z t) - C)) l
      (𝓝 ((1 / 8) / ((2 * C) * (1 - 2 * C ^ 2)))) := by
  have hf := C_c_facts
  apply branch_rescaled_tendsto hz
    (by simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi)
    ((eventually_small_inverse hi).mono fun _ ht => (branches_harmonic ht).1)
    hf.2.2.2.1 (ne_of_gt (lt_trans hf.1 hf.2.1)) hf.2.2.2.2.2.1

theorem lowBranch_rescaled {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0)) :
    Tendsto (fun t => z t * (lowBranch (1 / z t) - c)) l
      (𝓝 ((1 / 8) / ((2 * c) * (1 - 2 * c ^ 2)))) := by
  have hf := C_c_facts
  apply branch_rescaled_tendsto hz
    (by simpa only [lowBranch_zero, Function.comp_def] using lowBranch_continuous.continuousAt.tendsto.comp hi)
    ((eventually_small_inverse hi).mono fun _ ht => (branches_harmonic ht).2)
    hf.2.2.2.2.1 (ne_of_gt hf.1) hf.2.2.2.2.2.2

 
theorem lower_rescaling_zero {α : Type*} {l : Filter α} {z v : α → ℝ} {L : ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0))
    {k m : ℕ} (hkm : k < m) (hv : Tendsto (fun t => z t ^ m * v t) l (𝓝 L)) :
    Tendsto (fun t => z t ^ k * v t) l (𝓝 0) := by
  have hp := (hi.pow (m - k)).mul hv
  have hmk : m - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hkm)
  simp only [zero_pow hmk, zero_mul] at hp
  apply hp.congr'
  filter_upwards [hz] with t ht
  rw [one_div, inv_pow, pow_sub₀ (z t) ht hkm.le]
  field_simp

 

theorem homogeneousQ_high_decay {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0))
    (N : ℕ) (g : Polynomial ℝ) (k : ℕ) (hk : k < 2 * N + 1) :
    Tendsto (fun t => z t ^ k * (homogeneousQ N g).eval (highBranch (1 / z t))) l (𝓝 0) := by
  have hb : Tendsto (fun t => highBranch (1 / z t)) l (𝓝 C) := by
    simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi
  have hscale := ((highBranch_rescaled hz hi).pow (2 * N + 1)).mul
    (((hb.sub_const c).pow N).mul (g.continuous.continuousAt.tendsto.comp hb))
  have hlim : Tendsto (fun t => z t ^ (2 * N + 1) *
      (homogeneousQ N g).eval (highBranch (1 / z t))) l
      (𝓝 (((1 / 8) / ((2 * C) * (1 - 2 * C ^ 2))) ^ (2 * N + 1) *
        ((C - c) ^ N * g.eval C))) := by
    apply hscale.congr'
    exact Eventually.of_forall fun t => by
      simp only [homogeneousQ, eval_mul, eval_pow, eval_sub, eval_C, eval_X, Function.comp_def, mul_pow]
      ring
  exact lower_rescaling_zero hz hi hk hlim

theorem homogeneousQ_low_limit {α : Type*} {l : Filter α} {z : α → ℝ}
    (hz : ∀ᶠ t in l, z t ≠ 0) (hi : Tendsto (fun t => 1 / z t) l (𝓝 0))
    (N : ℕ) (g : Polynomial ℝ) :
    ∃ L : ℝ, Tendsto (fun t => z t ^ N * (homogeneousQ N g).eval (lowBranch (1 / z t))) l (𝓝 L) := by
  have hb : Tendsto (fun t => lowBranch (1 / z t)) l (𝓝 c) := by
    simpa only [lowBranch_zero, Function.comp_def] using lowBranch_continuous.continuousAt.tendsto.comp hi
  have hscale := ((hb.sub_const C).pow (2 * N + 1)).mul
    (((lowBranch_rescaled hz hi).pow N).mul (g.continuous.continuousAt.tendsto.comp hb))
  refine ⟨_, hscale.congr' ?_⟩
  exact Eventually.of_forall fun t => by
    simp only [homogeneousQ, eval_mul, eval_pow, eval_sub, eval_C, eval_X, Function.comp_def, mul_pow]
    ring

 

theorem tilde_projection_eval (N : ℕ) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.natDegree ≤ N)
    {z b : ℝ} (hz : z ≠ 0) (hb : harmonicCoordinate.eval b = (1 + 1 / z) / 8) :
    (tildePoly N P).eval z + b * (tildePoly N J).eval z + b ^ 2 * (tildePoly N E).eval z =
      z ^ N * (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
        X ^ 2 * E.comp harmonicCoordinate).eval b := by
  rw [tildePoly_eval N hP hz, tildePoly_eval N hJ hz, tildePoly_eval N hE hz]
  simp only [eval_add, eval_mul, eval_comp, eval_pow, eval_X, hb]
  ring

 

theorem tilde_F_decay (N : ℕ) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.natDegree ≤ N)
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate) (j : ℕ) (hj : j ≤ N) :
    Tendsto (fun t : ℝ => (-t) ^ j * ((tildePoly N P).eval (-t) +
      highBranch (1 / (-t)) * (tildePoly N J).eval (-t) +
      highBranch (1 / (-t)) ^ 2 * (tildePoly N E).eval (-t))) atTop (𝓝 0) := by
  have hz : ∀ᶠ t : ℝ in atTop, -t ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact neg_ne_zero.mpr ht.ne'
  have hi : Tendsto (fun t : ℝ => 1 / (-t)) atTop (𝓝 0) := by
    simpa only [one_div, inv_neg, neg_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).neg
  apply (homogeneousQ_high_decay hz hi N g (N + j) (by omega)).congr'
  filter_upwards [hz, eventually_small_inverse hi] with t ht hs
  have he := tilde_projection_eval N P J E hP hJ hE ht (branches_harmonic hs).1
  rw [← hQ] at he
  rw [he, pow_add]
  ring

 
theorem tilde_D_limit (N : ℕ) (g P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.natDegree ≤ N)
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate) :
    ∃ L : ℝ, Tendsto (fun z : ℝ => (tildePoly N J).eval z +
      Real.sqrt (1 + Real.sqrt ((1 + 1 / z) / 2)) * (tildePoly N E).eval z) atTop (𝓝 L) := by
  have hz : ∀ᶠ z : ℝ in atTop, z ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact hz.ne'
  have hi : Tendsto (fun z : ℝ => 1 / z) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0))
  have hh : Tendsto (fun z : ℝ => highBranch (1 / z)) atTop (𝓝 C) := by
    simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi
  have hl : Tendsto (fun z : ℝ => lowBranch (1 / z)) atTop (𝓝 c) := by
    simpa only [lowBranch_zero, Function.comp_def] using lowBranch_continuous.continuousAt.tendsto.comp hi
  have hdiff := hh.sub hl
  have hne : C - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt C_c_facts.2.1)
  obtain ⟨L, hL⟩ := homogeneousQ_low_limit hz hi N g
  have hhigh := homogeneousQ_high_decay hz hi N g N (by omega)
  refine ⟨(0 - L) / (C - c), ((hhigh.sub hL).div hdiff hne).congr' ?_⟩
  filter_upwards [hz, eventually_small_inverse hi, hdiff.eventually_ne hne] with z hzt hs hd
  apply (div_eq_iff hd).2
  rw [← branches_sum hs]
  have heh := tilde_projection_eval N P J E hP hJ hE hzt (branches_harmonic hs).1
  have hel := tilde_projection_eval N P J E hP hJ hE hzt (branches_harmonic hs).2
  rw [← hQ] at heh hel
  linear_combination -heh + hel

theorem harmonic_natDegree : harmonicCoordinate.natDegree = 4 := by
  unfold harmonicCoordinate
  compute_degree <;> norm_num

theorem degree_lt_natDegree_le_pred {N : ℕ} {p : Polynomial ℝ}
    (hN : 1 ≤ N) (hp : p.degree < (N : WithBot ℕ)) : p.natDegree ≤ N - 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have h : p.natDegree < N := (natDegree_lt_iff_degree_lt hp0).2 hp
  omega

 
theorem projection_natDegree_le (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ)) :
    (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
  have he := degree_lt_natDegree_le_pred hN hE
  have hp' : (P.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
    rw [natDegree_comp, harmonic_natDegree]
    omega
  have hj' : (X * J.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X, natDegree_comp, harmonic_natDegree]
    omega
  have he' : (X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X_pow, natDegree_comp, harmonic_natDegree]
    omega
  exact le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _) (max_le hp' hj')) he')

 

theorem projection_J_degree_lt (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℝ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N) :
    J.degree < (N : WithBot ℕ) := by
  by_cases hJ0 : J = 0
  · simp [hJ0]
  apply (natDegree_lt_iff_degree_lt hJ0).1
  by_contra hj
  have hjN : J.natDegree = N := by omega
  have he := degree_lt_natDegree_le_pred hN hE
  let A : Polynomial ℝ := P.comp harmonicCoordinate + X ^ 2 * E.comp harmonicCoordinate
  have hp' : (P.comp harmonicCoordinate).natDegree ≤ 4 * N := by
    rw [natDegree_comp, harmonic_natDegree]
    omega
  have he' : (X ^ 2 * E.comp harmonicCoordinate).natDegree ≤ 4 * N := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X_pow, natDegree_comp, harmonic_natDegree]
    omega
  have ha : A.natDegree ≤ 4 * N := le_trans (natDegree_add_le _ _) (max_le hp' he')
  have hjcomp : J.comp harmonicCoordinate ≠ 0 := by
    intro h
    have hd := natDegree_comp (p := J) (q := harmonicCoordinate)
    rw [h, natDegree_zero, hjN, harmonic_natDegree] at hd
    omega
  have hb : (X * J.comp harmonicCoordinate).natDegree = 4 * N + 1 := by
    rw [natDegree_X_mul hjcomp, natDegree_comp, hjN, harmonic_natDegree]
    omega
  have hsum :
      (P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
        X ^ 2 * E.comp harmonicCoordinate).natDegree = 4 * N + 1 := by
    have heq : P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
        X ^ 2 * E.comp harmonicCoordinate = A + X * J.comp harmonicCoordinate := by
      dsimp [A]
      ring
    rw [heq, natDegree_add_eq_right_of_natDegree_lt (by rw [hb]; omega), hb]
  omega

theorem homogeneousQ_lower_degree (N : ℕ) (hN : 1 ≤ N) {g : Polynomial ℝ}
    (hg : g.degree < (N : WithBot ℕ)) : (homogeneousQ N g).natDegree ≤ 4 * N := by
  have hg' := degree_lt_natDegree_le_pred hN hg
  have h := natDegree_mul_le (p := (X - Polynomial.C C) ^ (2 * N + 1) *
    (X - Polynomial.C c) ^ N) (q := g)
  have h' := natDegree_mul_le (p := (X - Polynomial.C C) ^ (2 * N + 1))
    (q := (X - Polynomial.C c) ^ N)
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one] at h'
  exact le_trans h (by omega)

end

noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators

 
theorem stieltjes_polynomial_basis (N : ℕ) (e : Polynomial ℝ) (he : e.natDegree < N)
    {z : ℝ} (hz : 0 < z) :
    z * realStieltjes (-1) (fun y => e.eval (-y) * omega y) z =
      ∑ k : Fin N, (e.coeff k.val * (-1) ^ k.val) * transformedBasis k.val z := by
  have hev (y : ℝ) : e.eval (-y) =
      ∑ k : Fin N, (e.coeff k.val * (-1) ^ k.val) * y ^ k.val := by
    rw [eval_eq_sum_range' he, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  have heq : (fun y => z * (e.eval (-y) * omega y / (z - (-1) * y))) =
      fun y => ∑ k : Fin N, (e.coeff k.val * (-1) ^ k.val) *
        (boundedCauchy z y * momentBasis k.val y) := by
    funext y
    rw [hev]
    simp only [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold boundedCauchy momentBasis
    ring
  rw [realStieltjes, ← integral_const_mul, heq, integral_finsetSum]
  · simp only [integral_const_mul, transformedBasis]
  · intro k _
    exact (integrableOn_boundedCauchy_basis k.val hz).const_mul _

 

theorem homogeneous_projection_zero (N : ℕ) (hN : 1 ≤ N) (g P J E : Polynomial ℝ)
    (hg : g.degree < (N : WithBot ℕ))
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ))
    (hQ : homogeneousQ N g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X ^ 2 * E.comp harmonicCoordinate) :
    P = 0 ∧ J = 0 ∧ E = 0 ∧ g = 0 := by
  have hEn : E.natDegree ≤ N := (degree_lt_natDegree_le_pred hN hE).trans (Nat.sub_le _ _)
  have hJl : J.degree < (N : WithBot ℕ) := projection_J_degree_lt N hN P J E hP hJ hE
    (by rw [← hQ]; exact homogeneousQ_lower_degree N hN hg)
  have htJ0 := tildePoly_zero_of_degree_lt N hJl
  have htE0 := tildePoly_zero_of_degree_lt N hE
  have hdiv : X ∣ tildePoly N E := X_dvd_iff.2 (by simpa only [coeff_zero_eq_eval_zero] using htE0)
  obtain ⟨e, he⟩ := hdiv
  have hen : e.natDegree < N := by
    by_cases he0 : e = 0
    · simp [he0]; omega
    have hb := tildePoly_natDegree_le N hEn
    rw [he, natDegree_X_mul he0] at hb
    omega
  have hF : ∀ j : ℕ, j ≤ N → Tendsto
      (fun t : ℝ => (-t) ^ j * projectionF (tildePoly N P) (tildePoly N J) (tildePoly N E) (-t))
      atTop (𝓝 0) := by
    intro j hj
    exact tilde_F_decay N g P J E hP hJ hEn hQ j hj
  obtain ⟨L, hD⟩ := tilde_D_limit N g P J E hP hJ hEn hQ
  change Tendsto (fun z : ℝ => projectionD (tildePoly N J) (tildePoly N E) z) atTop (𝓝 L) at hD
  have hDc := projectionD_cauchy (tildePoly N J) e (by simpa only [← he] using hD)
  have hm := projection_moments_of_decay N (tildePoly N P) (tildePoly N J) (tildePoly N E) hF
  let v : Fin N → ℝ := fun k => -(Real.sqrt 2 / Real.pi) * (e.coeff k.val * (-1) ^ k.val)
  have hDv {z : ℝ} (hz : 0 < z) :
      projectionD (tildePoly N J) (tildePoly N E) z = cauchyDefect N 0 v z := by
    rw [he, hDc z hz, htJ0, zero_add, mul_assoc, stieltjes_polynomial_basis N e hen hz]
    simp only [cauchyDefect, zero_sub, v, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, neg_neg]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hv : CauchyMomentProblem N 0 v := by
    intro j
    calc
      (∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x * cauchyDefect N 0 v x) =
          ∫ x in Ioo (0 : ℝ) 1, x ^ j.val * (projectionD (tildePoly N J) (tildePoly N E) x * omega x) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx
        dsimp only
        rw [hDv hx.1]
        unfold momentBasis
        ring
      _ = 0 := hm j.val j.isLt
  have hv0 := cauchyMomentProblem_zero hv
  have he0 : e = 0 := by
    ext k
    rw [coeff_zero]
    by_cases hk : k < N
    · have hvk := congrFun hv0 (⟨k, hk⟩ : Fin N)
      dsimp [v] at hvk
      have hs : -(Real.sqrt 2 / Real.pi) ≠ 0 := neg_ne_zero.mpr
        (div_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) Real.pi_ne_zero)
      have hc := (mul_eq_zero.mp hvk).resolve_left hs
      exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (by norm_num))
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hE0 : E = 0 := (tildePoly_eq_zero_iff N E).1 (by simpa only [he0, mul_zero] using he)
  have htE : tildePoly N E = 0 := (tildePoly_eq_zero_iff N E).2 hE0
  have htJ : tildePoly N J = 0 := by
    have hJlim : Tendsto (fun z : ℝ => (tildePoly N J).eval z) atTop (𝓝 L) := by
      simpa only [htE, projectionD, eval_zero, mul_zero, add_zero] using hD
    have hc := polynomial_constant_of_limit tendsto_norm_atTop_atTop (tildePoly N J) hJlim
    have hL : L = 0 := by simpa only [hc, eval_C] using htJ0
    simpa only [hL, C_0] using hc
  have htP : tildePoly N P = 0 := by
    have hPlim : Tendsto (fun t : ℝ => (tildePoly N P).eval (-t)) atTop (𝓝 0) := by
      simpa only [htJ, htE, projectionF, eval_zero, mul_zero, add_zero, pow_zero, one_mul] using hF 0 (Nat.zero_le N)
    simpa only [C_0] using polynomial_constant_of_limit norm_neg_atTop (tildePoly N P) hPlim
  have hP0 := (tildePoly_eq_zero_iff N P).1 htP
  have hJ0 := (tildePoly_eq_zero_iff N J).1 htJ
  refine ⟨hP0, hJ0, hE0, ?_⟩
  have hQ0 : homogeneousQ N g = 0 := by simp [hQ, hP0, hJ0, hE0]
  have hroot : (X - Polynomial.C C) ^ (2 * N + 1) * (X - Polynomial.C c) ^ N ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
  exact (mul_eq_zero.1 hQ0).resolve_left hroot



def rootPolynomial (N : ℕ) : Polynomial ℝ :=
  (X - Polynomial.C C) ^ (2 * N + 1) * (X - Polynomial.C c) ^ N

theorem rootPolynomial_monic (N : ℕ) : (rootPolynomial N).Monic :=
  ((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)

theorem rootPolynomial_natDegree (N : ℕ) : (rootPolynomial N).natDegree = 3 * N + 1 := by
  rw [rootPolynomial, ((monic_X_sub_C C).pow _).natDegree_mul ((monic_X_sub_C c).pow _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  omega

theorem rootPolynomial_degree (N : ℕ) : (rootPolynomial N).degree = ((3 * N + 1 : ℕ) : WithBot ℕ) := by
  rw [degree_eq_natDegree (rootPolynomial_monic N).ne_zero, rootPolynomial_natDegree]

abbrev ProjectionSpace (N : ℕ) :=
  (degreeLT ℝ (N + 1)) × (degreeLT ℝ (N + 1)) × (degreeLT ℝ N)

def projectionMap (N : ℕ) : ProjectionSpace N →ₗ[ℝ] Polynomial ℝ where
  toFun t := t.1.val.comp harmonicCoordinate + X * t.2.1.val.comp harmonicCoordinate +
    X ^ 2 * t.2.2.val.comp harmonicCoordinate
  map_add' t u := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_comp]
    ring
  map_smul' a t := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_comp,
      smul_add, mul_smul_comm, RingHom.id_apply]

def projectionRemainder (N : ℕ) : ProjectionSpace N →ₗ[ℝ] degreeLT ℝ (3 * N + 1) where
  toFun t := ⟨(projectionMap N t) %ₘ rootPolynomial N, mem_degreeLT.2 (by
    have h := degree_modByMonic_lt (projectionMap N t) (rootPolynomial_monic N)
    rwa [rootPolynomial_degree] at h)⟩
  map_add' t u := by
    apply Subtype.ext
    simp only [map_add, add_modByMonic, Submodule.coe_add]
  map_smul' a t := by
    apply Subtype.ext
    simp only [map_smul, smul_modByMonic, Submodule.coe_smul, RingHom.id_apply]

theorem projectionSpace_finrank (N : ℕ) : Module.finrank ℝ (ProjectionSpace N) = 3 * N + 2 := by
  simp only [ProjectionSpace, Module.finrank_prod,
    Module.finrank_eq_card_basis (degreeLT.basis ℝ (N + 1)),
    Module.finrank_eq_card_basis (degreeLT.basis ℝ N), Fintype.card_fin]
  omega

end
end CriticalStrip

end OAI
