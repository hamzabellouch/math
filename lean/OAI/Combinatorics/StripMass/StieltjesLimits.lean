import Mathlib
import OAI.Combinatorics.StripMass.QuarticIntegrals

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
theorem tendsto_realStieltjes_zero {α : Type*} {l : Filter α} {z : α → ℝ}
    {a : ℝ} {w : ℝ → ℝ} (hw : IntegrableOn w (Ioo (0 : ℝ) 1)) (ha : |a| ≤ 1)
    (hz : Tendsto (fun t => ‖z t‖) l atTop) :
    Tendsto (fun t => realStieltjes a w (z t)) l (𝓝 0) := by
  have hz' : Tendsto (fun t => |z t|) l atTop := by simpa only [Real.norm_eq_abs] using hz
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((hz'.eventually_ge_atTop 2).mono fun _ ht => norm_realStieltjes_le hw ha ht)
  exact tendsto_const_nhds.div_atTop (by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1) hz')

 
theorem polynomial_constant_of_limit {α : Type*} {l : Filter α} [l.NeBot]
    {z : α → ℝ} (hz : Tendsto (fun t => ‖z t‖) l atTop)
    (p : Polynomial ℝ) {L : ℝ} (hp : Tendsto (fun t => p.eval (z t)) l (𝓝 L)) :
    p = Polynomial.C L := by
  have hd : p.degree ≤ 0 := by
    by_contra h
    have htop := p.tendsto_norm_atTop (lt_of_not_ge h) hz
    exact not_tendsto_nhds_of_tendsto_atTop htop ‖L‖ hp.norm
  have heq := Polynomial.eq_C_of_degree_le_zero hd
  have hL : p.coeff 0 = L := by
    have hc : Tendsto (fun _ : α => p.coeff 0) l (𝓝 L) := by
      apply hp.congr'
      exact Eventually.of_forall fun t =>
        (congrArg (fun q : Polynomial ℝ => q.eval (z t)) heq).trans (Polynomial.eval_C)
    exact tendsto_nhds_unique tendsto_const_nhds hc
  rw [heq, hL]

 

theorem moments_zero_of_stieltjes_decay {α : Type*} {l : Filter α} [l.NeBot]
    {z : α → ℝ} (hz : Tendsto (fun t => ‖z t‖) l atTop) (N : ℕ)
    {w : ℝ → ℝ} (hw : IntegrableOn w (Ioo (0 : ℝ) 1))
    (hdecay : ∀ j : ℕ, j < N → Tendsto
      (fun t => z t ^ (j + 1) * realStieltjes 1 w (z t)) l (𝓝 0)) :
    ∀ j : ℕ, j < N → ∫ x in Ioo (0 : ℝ) 1, x ^ j * w x = 0 := by
  induction N generalizing w with
  | zero => simp
  | succ N ih =>
      let v : ℝ → ℝ := fun x => x * w x
      have hv : IntegrableOn v (Ioo (0 : ℝ) 1) :=
        integrableOn_continuous_mul hw continuous_id.continuousOn
      have hevent : ∀ᶠ t in l, offCut 1 (z t) := by
        filter_upwards [hz.eventually_ge_atTop 2] with t ht
        exact offCut_of_abs_large (by norm_num) (by simpa only [Real.norm_eq_abs] using ht)
      have hrec : ∀ᶠ t in l, z t * realStieltjes 1 w (z t) =
          realStieltjes 1 v (z t) + ∫ x in Ioo (0 : ℝ) 1, w x := by
        filter_upwards [hevent] with t ht
        simpa only [one_mul] using realStieltjes_mul_variable hw ht
      have hlim : Tendsto (fun t => z t * realStieltjes 1 w (z t)) l
          (𝓝 (∫ x in Ioo (0 : ℝ) 1, w x)) := by
        have h := (tendsto_realStieltjes_zero hv (by norm_num : |(1 : ℝ)| ≤ 1) hz).add_const
          (∫ x in Ioo (0 : ℝ) 1, w x)
        simpa only [zero_add] using h.congr' (hrec.mono fun _ ht => ht.symm)
      have hm : (∫ x in Ioo (0 : ℝ) 1, w x) = 0 := by
        apply tendsto_nhds_unique hlim
        simpa only [zero_add, pow_one] using hdecay 0 (Nat.succ_pos N)
      have hdecayv : ∀ j : ℕ, j < N → Tendsto
          (fun t => z t ^ (j + 1) * realStieltjes 1 v (z t)) l (𝓝 0) := by
        intro j hj
        apply (hdecay (j + 1) (Nat.succ_lt_succ hj)).congr'
        filter_upwards [hrec] with t ht
        rw [hm, add_zero] at ht
        rw [← ht, pow_succ]
        ring
      intro j hj
      cases j with
      | zero => simpa using hm
      | succ j =>
          have hj' : j < N := Nat.lt_of_succ_lt_succ hj
          have h := ih hv hdecayv j hj'
          convert h using 1
          apply setIntegral_congr_fun measurableSet_Ioo
          intro x _
          dsimp [v]
          rw [pow_succ]
          ring



 
def fBranch (z : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)
def projectionF (P J E : Polynomial ℝ) (z : ℝ) : ℝ :=
  P.eval z + fBranch z * J.eval z + fBranch z ^ 2 * E.eval z
def projectionD (J E : Polynomial ℝ) (z : ℝ) : ℝ :=
  J.eval z + lBranch z * E.eval z

theorem integrableOn_omega_projection : IntegrableOn omega (Ioo (0 : ℝ) 1) := by
  have hi := ((omega_resolvent (by norm_num : (0 : ℝ) < 1)).1).const_mul 2
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    unfold omega
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold omega; positivity)]
    simp only [one_mul]
    have hd : 0 < 1 + x := by linarith [hx.1]
    rw [← mul_div_assoc, le_div_iff₀ hd]
    have hw : 0 ≤ omega x := by unfold omega; positivity
    nlinarith [hx.2]

theorem offCut_one_neg {z : ℝ} (hz : z < 0) : offCut 1 z := by
  intro x hx
  simp only [one_mul]
  linarith [hx.1]

theorem offCut_neg_one_pos {z : ℝ} (hz : 0 < z) : offCut (-1) z := by
  intro x hx
  simp only [neg_one_mul, sub_neg_eq_add]
  linarith [hx.1]

theorem integrableOn_projection_weight (J E : Polynomial ℝ) :
    IntegrableOn (fun x => projectionD J E x * omega x) (Ioo (0 : ℝ) 1) := by
  have hj := integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_omega_projection J
  have he := integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_lBranch_omega E
  have heq : (fun x => projectionD J E x * omega x) =
      fun x => J.eval (1 * x) * omega x + E.eval (1 * x) * (lBranch x * omega x) := by
    funext x
    simp only [one_mul, projectionD]
    ring
  rw [heq]
  exact hj.add he

theorem fBranch_transform {z : ℝ} (hz : z < 0) :
    fBranch z = Real.cos (Real.pi / 8) -
      (1 / Real.pi) * realStieltjes 1 omega z := by
  have h := stieltjes_omega hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, omega x / (x - z)) = -realStieltjes 1 omega z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [fBranch, heq, mul_neg, ← sub_eq_add_neg] using h

theorem fBranch_square_transform {z : ℝ} (hz : z < 0) :
    fBranch z ^ 2 = Real.cos (Real.pi / 8) ^ 2 -
      (1 / Real.pi) * realStieltjes 1 (fun x => lBranch x * omega x) z := by
  have h := stieltjes_omega_square hz
  have heq : (∫ x in Ioo (0 : ℝ) 1, lBranch x * omega x / (x - z)) =
      -realStieltjes 1 (fun x => lBranch x * omega x) z := by
    rw [realStieltjes, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x _
    simp only [one_mul]
    rw [show x - z = -(z - x) by ring, div_neg]
  simpa only [fBranch, heq, mul_neg, ← sub_eq_add_neg] using h

 
theorem projectionF_polynomial (P J E : Polynomial ℝ) :
    ∃ R : Polynomial ℝ, ∀ z : ℝ, z < 0 →
      projectionF P J E z = R.eval z - (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨Rj, hRj⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_omega_projection J
  obtain ⟨Re, hRe⟩ := polynomial_mul_realStieltjes (a := (1 : ℝ)) integrableOn_lBranch_omega E
  refine ⟨P + Polynomial.C (Real.cos (Real.pi / 8)) * J +
    Polynomial.C (Real.cos (Real.pi / 8) ^ 2) * E -
    Polynomial.C (1 / Real.pi) * (Rj + Re), ?_⟩
  intro z hz
  have hj := hRj z (offCut_one_neg hz)
  have he := hRe z (offCut_one_neg hz)
  have hsum := realStieltjes_add
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_omega_projection J)
    (integrableOn_polynomial_weight (a := (1 : ℝ)) integrableOn_lBranch_omega E)
    (offCut_one_neg hz)
  have hw : (fun x => J.eval (1 * x) * omega x + E.eval (1 * x) * (lBranch x * omega x)) =
      fun x => projectionD J E x * omega x := by
    funext x
    simp only [one_mul, projectionD]
    ring
  rw [hw] at hsum
  simp only [one_mul] at hj he hsum
  rw [projectionF, fBranch_square_transform hz, fBranch_transform hz, hsum]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination -(1 / Real.pi) * hj - (1 / Real.pi) * he

theorem norm_neg_atTop : Tendsto (fun z : ℝ => ‖-z‖) atTop atTop := by
  simpa only [norm_neg] using (tendsto_norm_atTop_atTop : Tendsto (fun z : ℝ => ‖z‖) atTop atTop)

 

theorem projectionF_cauchy (P J E : Polynomial ℝ)
    (hF : Tendsto (fun t : ℝ => projectionF P J E (-t)) atTop (𝓝 0)) :
    ∀ z : ℝ, z < 0 → projectionF P J E z = -(1 / Real.pi) *
      realStieltjes 1 (fun x => projectionD J E x * omega x) z := by
  obtain ⟨R, hR⟩ := projectionF_polynomial P J E
  have hlim := hF.add ((tendsto_realStieltjes_zero (integrableOn_projection_weight J E)
    (by norm_num : |(1 : ℝ)| ≤ 1) norm_neg_atTop).const_mul (1 / Real.pi))
  have hRlim : Tendsto (fun t : ℝ => R.eval (-t)) atTop (𝓝 0) := by
    have hlim' : Tendsto (fun t : ℝ => projectionF P J E (-t) + (1 / Real.pi) *
        realStieltjes 1 (fun x => projectionD J E x * omega x) (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using hlim
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hR (-t) (neg_neg_of_pos ht)
    linarith
  have hR0 := polynomial_constant_of_limit norm_neg_atTop R hRlim
  intro z hz
  simpa only [hR0, Polynomial.eval_C, zero_sub, neg_mul] using hR z hz

 

theorem projection_moments_of_decay (N : ℕ) (P J E : Polynomial ℝ)
    (hF : ∀ j : ℕ, j ≤ N → Tendsto
      (fun t : ℝ => (-t) ^ j * projectionF P J E (-t)) atTop (𝓝 0)) :
    ∀ j : ℕ, j < N → ∫ x in Ioo (0 : ℝ) 1,
      x ^ j * (projectionD J E x * omega x) = 0 := by
  have hFc := projectionF_cauchy P J E (by simpa using hF 0 (Nat.zero_le N))
  apply moments_zero_of_stieltjes_decay norm_neg_atTop N (integrableOn_projection_weight J E)
  intro j hj
  apply (show Tendsto (fun t : ℝ => (-Real.pi) *
      ((-t) ^ (j + 1) * projectionF P J E (-t))) atTop (𝓝 0) from
    by simpa using (hF (j + 1) (Nat.succ_le_of_lt hj)).const_mul (-Real.pi)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [hFc (-t) (neg_neg_of_pos ht)]
  field_simp [Real.pi_ne_zero]

 

theorem projectionD_cauchy (J e : Polynomial ℝ) {L : ℝ}
    (hD : Tendsto (fun z : ℝ => projectionD J (Polynomial.X * e) z) atTop (𝓝 L)) :
    ∀ z : ℝ, 0 < z → projectionD J (Polynomial.X * e) z = J.eval 0 +
      (Real.sqrt 2 / Real.pi) * z * realStieltjes (-1)
        (fun x => e.eval (-x) * omega x) z := by
  obtain ⟨R, hR⟩ := polynomial_mul_realStieltjes (a := (-1 : ℝ)) integrableOn_omega_projection e
  let v : ℝ → ℝ := fun x => e.eval (-x) * omega x
  let S : Polynomial ℝ := J + Polynomial.C (Real.sqrt 2 * Real.cos (Real.pi / 8)) *
      (Polynomial.X * e) + Polynomial.C (Real.sqrt 2 / Real.pi) * (Polynomial.X * R)
  have hv : IntegrableOn v (Ioo (0 : ℝ) 1) := by
    simpa only [neg_one_mul] using integrableOn_polynomial_weight (a := (-1 : ℝ))
      integrableOn_omega_projection e
  have hEq : ∀ z : ℝ, 0 < z → projectionD J (Polynomial.X * e) z = S.eval z +
      (Real.sqrt 2 / Real.pi) * z * realStieltjes (-1) v z := by
    intro z hz
    have hl := stieltjes_lBranch hz
    have he := hR z (offCut_neg_one_pos hz)
    simp only [neg_one_mul] at he
    change e.eval z * realStieltjes (-1) omega z = realStieltjes (-1) v z + R.eval z at he
    have ht : (∫ x in Ioo (0 : ℝ) 1, omega x / (x + z)) = realStieltjes (-1) omega z := by
      simp [realStieltjes, add_comm]
    rw [ht] at hl
    simp only [projectionD, Polynomial.eval_mul, Polynomial.eval_X, hl, S,
      Polynomial.eval_add, Polynomial.eval_C]
    linear_combination (Real.sqrt 2 / Real.pi) * z * he
  have hnorm : Tendsto (fun z : ℝ => ‖z‖) atTop atTop := tendsto_norm_atTop_atTop
  have hzT : Tendsto (fun z : ℝ => z * realStieltjes (-1) v z) atTop
      (𝓝 (∫ x in Ioo (0 : ℝ) 1, v x)) := by
    have hweight : IntegrableOn (fun x => (-1 : ℝ) * x * v x) (Ioo (0 : ℝ) 1) :=
      integrableOn_continuous_mul hv (continuous_const.mul continuous_id).continuousOn
    have ht := (tendsto_realStieltjes_zero hweight (by norm_num : |(-1 : ℝ)| ≤ 1) hnorm).add_const
      (∫ x in Ioo (0 : ℝ) 1, v x)
    have ht' : Tendsto (fun z : ℝ => realStieltjes (-1) (fun x => (-1 : ℝ) * x * v x) z +
        ∫ x in Ioo (0 : ℝ) 1, v x) atTop (𝓝 (∫ x in Ioo (0 : ℝ) 1, v x)) := by
      simpa only [zero_add] using ht
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact (realStieltjes_mul_variable hv (offCut_neg_one_pos hz)).symm
  have hSlim : Tendsto (fun z : ℝ => S.eval z) atTop
      (𝓝 (L - (Real.sqrt 2 / Real.pi) * ∫ x in Ioo (0 : ℝ) 1, v x)) := by
    apply (hD.sub (hzT.const_mul (Real.sqrt 2 / Real.pi))).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [hEq z hz]
    ring
  have hS := polynomial_constant_of_limit hnorm S hSlim
  have hS0 : S.eval 0 = J.eval 0 := by simp [S]
  have hSc : ∀ z : ℝ, S.eval z = J.eval 0 := by
    intro z
    calc S.eval z = S.eval 0 := by rw [hS]; simp
         _ = J.eval 0 := hS0
  intro z hz
  simpa only [hSc] using hEq z hz

end

 

noncomputable section
open Polynomial Set Filter
open scoped Topology

 
def tildePoly (N : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  reflect N (p.comp (Polynomial.C (1 / 8) * (1 + X)))

theorem affine_natDegree :
    (Polynomial.C (1 / 8 : ℝ) * (1 + X)).natDegree = 1 := by
  compute_degree
  norm_num

theorem affine_leadingCoeff :
    (Polynomial.C (1 / 8 : ℝ) * (1 + X)).leadingCoeff = 1 / 8 := by
  rw [leadingCoeff, affine_natDegree]
  norm_num [coeff_C_mul, coeff_add, coeff_one]

theorem tildePoly_natDegree_le (N : ℕ) {p : Polynomial ℝ} (hp : p.natDegree ≤ N) :
    (tildePoly N p).natDegree ≤ N := by
  apply le_trans natDegree_reflect_le
  rw [natDegree_comp, affine_natDegree, mul_one, max_eq_left hp]

theorem tildePoly_eval (N : ℕ) {p : Polynomial ℝ} (hp : p.natDegree ≤ N)
    {z : ℝ} (hz : z ≠ 0) :
    (tildePoly N p).eval z = z ^ N * p.eval ((1 + 1 / z) / 8) := by
  let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have hdeg : (p.comp (Polynomial.C (1 / 8) * (1 + X))).natDegree ≤ N := by
    rw [natDegree_comp, affine_natDegree, mul_one]
    exact hp
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) z⁻¹ N
    (p.comp (Polynomial.C (1 / 8) * (1 + X))) hdeg
  simp only [invOf_eq_inv, inv_inv, eval₂_id, eval_comp, eval_mul, eval_C, eval_add,
    eval_one, eval_X] at h
  change (tildePoly N p).eval z * (z⁻¹) ^ N = p.eval ((1 / 8) * (1 + z⁻¹)) at h
  have heq : (1 / 8 : ℝ) * (1 + z⁻¹) = (1 + 1 / z) / 8 := by ring
  rw [heq] at h
  have h' := congrArg (fun x : ℝ => x * z ^ N) h
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one] at h'
  exact h'.trans (mul_comm _ _)

theorem tildePoly_eq_zero_iff (N : ℕ) (p : Polynomial ℝ) : tildePoly N p = 0 ↔ p = 0 := by
  rw [tildePoly, reflect_eq_zero_iff]
  rw [comp_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | ⟨_, h⟩
    · exact h
    · have hd := congrArg Polynomial.natDegree h
      rw [affine_natDegree, natDegree_C] at hd
      contradiction
  · exact Or.inl

theorem tildePoly_zero_of_degree_lt (N : ℕ) {p : Polynomial ℝ}
    (hp : p.degree < (N : WithBot ℕ)) : (tildePoly N p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, tildePoly, coeff_reflect, revAt_zero]
  apply coeff_eq_zero_of_degree_lt
  have hq : (Polynomial.C (1 / 8 : ℝ) * (1 + X)).degree = 1 := by
    rw [degree_eq_natDegree (p := Polynomial.C (1 / 8 : ℝ) * (1 + X)) (by
      intro h; have hd := affine_natDegree; rw [h, natDegree_zero] at hd; contradiction),
      affine_natDegree]
    rfl
  rw [degree_comp (by rw [hq]; norm_num), hq, mul_one]
  exact hp

 
def highBranch (u : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt ((1 - u) / 2)) / 2)
def lowBranch (u : ℝ) : ℝ := Real.sqrt ((1 - Real.sqrt ((1 - u) / 2)) / 2)

theorem sqrt_half : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
  have h1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn1 := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hn2 := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem highBranch_zero : highBranch 0 = C := by
  rw [C, lambda, Real.cos_pi_div_eight]
  unfold highBranch
  simp only [sub_zero, sqrt_half]
  have ha := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 + Real.sqrt 2 / 2) / 2)
  have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 + Real.sqrt 2)
  have hna := Real.sqrt_nonneg ((1 + Real.sqrt 2 / 2) / 2)
  have hnb := Real.sqrt_nonneg (2 + Real.sqrt 2)
  nlinarith

theorem lowBranch_zero : lowBranch 0 = c := by
  have hc : c = Real.sin (Real.pi / 8) := by
    rw [c, show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub]
  rw [hc, Real.sin_pi_div_eight]
  unfold lowBranch
  simp only [sub_zero, sqrt_half]
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ (1 - Real.sqrt 2 / 2) / 2 by linarith [sqrt_two_lt_two])
  have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 2 - Real.sqrt 2 by linarith [sqrt_two_lt_two])
  have hna := Real.sqrt_nonneg ((1 - Real.sqrt 2 / 2) / 2)
  have hnb := Real.sqrt_nonneg (2 - Real.sqrt 2)
  nlinarith

theorem highBranch_continuous : Continuous highBranch := by unfold highBranch; fun_prop
theorem lowBranch_continuous : Continuous lowBranch := by unfold lowBranch; fun_prop

theorem branches_sq {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    highBranch u ^ 2 = (1 + Real.sqrt ((1 - u) / 2)) / 2 ∧
    lowBranch u ^ 2 = (1 - Real.sqrt ((1 - u) / 2)) / 2 ∧
    Real.sqrt ((1 - u) / 2) ^ 2 = (1 - u) / 2 := by
  have hd : 0 ≤ (1 - u) / 2 := by linarith [hu.2]
  have hs := Real.sq_sqrt hd
  have hn := Real.sqrt_nonneg ((1 - u) / 2)
  have hlt : Real.sqrt ((1 - u) / 2) < 1 := by nlinarith [hu.1]
  exact ⟨Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith), hs⟩

theorem branches_harmonic {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    harmonicCoordinate.eval (highBranch u) = (1 + u) / 8 ∧
    harmonicCoordinate.eval (lowBranch u) = (1 + u) / 8 := by
  obtain ⟨hh, hl, hs⟩ := branches_sq hu
  simp only [harmonicCoordinate, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  constructor <;> nlinarith

theorem branches_sum {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    highBranch u + lowBranch u = Real.sqrt (1 + Real.sqrt ((1 + u) / 2)) := by
  obtain ⟨hh, hl, hs⟩ := branches_sq hu
  have ha : 0 ≤ highBranch u := Real.sqrt_nonneg _
  have hb : 0 ≤ lowBranch u := Real.sqrt_nonneg _
  have hs' := Real.sq_sqrt (show 0 ≤ (1 + u) / 2 by linarith [hu.1])
  have hn' := Real.sqrt_nonneg ((1 + u) / 2)
  have hp : 2 * highBranch u * lowBranch u = Real.sqrt ((1 + u) / 2) := by
    have hprod : (highBranch u * lowBranch u) ^ 2 = (1 + u) / 8 := by
      rw [mul_pow, hh, hl]
      nlinarith
    nlinarith [mul_nonneg ha hb]
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + Real.sqrt ((1 + u) / 2) by positivity)
  have hn := Real.sqrt_nonneg (1 + Real.sqrt ((1 + u) / 2))
  nlinarith

end
end CriticalStrip

end OAI
