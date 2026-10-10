import Mathlib

namespace OAI

/-! Contour moments, Newton coefficients and monic root polynomials. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Metric Complex Topology
open scoped Polynomial BigOperators

namespace DegeneratingTrees

 
def contourNewtonCoeff (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => -(∑ j : Fin (k + 1), contourNewtonCoeff s j * s (k + 1 - j)) / (k + 1)
termination_by k => k

 
def contourMoment (f : ℂ → ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(0, r), z ^ k * deriv f z / f z

 
def contourPolynomial (f : ℂ → ℂ) (r : ℝ) (d : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C (contourNewtonCoeff (contourMoment f r) k) * Polynomial.X ^ (d - k)

 

def FixedContourPreparationStatement : Prop :=
  ∀ (n d : ℕ) (F : (Fin n → ℂ) × ℂ → ℂ), AnalyticAt ℂ F (0, 0) →
    analyticOrderAt (fun y => F (0, y)) 0 = (d : ℕ∞) →
    ∃ (r : ℝ) (U : Set (Fin n → ℂ)) (g : (Fin n → ℂ) × ℂ → ℂ),
      0 < r ∧ IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧
      AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r) ∧
      AnalyticOnNhd ℂ g (U ×ˢ closedBall 0 (r / 2)) ∧
      (∀ q ∈ U, ∀ y ∈ closedBall (0 : ℂ) (r / 2), g (q, y) ≠ 0) ∧
      (∀ q ∈ U, ∀ y ∈ sphere (0 : ℂ) r, F (q, y) ≠ 0) ∧
      (∀ q ∈ U, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d) ∧
      (∀ k, AnalyticOnNhd ℂ
        (fun q => (contourPolynomial (fun y => F (q, y)) r d).coeff k) U) ∧
      (∀ q ∈ U, ∀ y ∈ closedBall (0 : ℂ) (r / 2),
        F (q, y) = (contourPolynomial (fun y => F (q, y)) r d).eval y * g (q, y))

 

theorem factor_closedDisc {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hne : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ a ∈ s, a ∈ ball (0 : ℂ) r ∧ 0 < m a) ∧
      AnalyticOnNhd ℂ g (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
      EqOn f (fun z => (∏ a ∈ s, (z - a) ^ m a) * g z) (closedBall 0 r) := by
  classical
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) r)
  have hD : 0 ≤ D :=
    (hf.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd).2 hf
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hb : (r : ℂ) ∈ sphere (0 : ℂ) r := by
    simp [abs_of_pos hr]
  have hb' : (r : ℂ) ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall hb
  have hb0 : meromorphicOrderAt f (r : ℂ) = 0 :=
    ((hf _ hb').meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 (hne _ hb)
  have hfinite : ∀ z : closedBall (0 : ℂ) r, meromorphicOrderAt f z ≠ ⊤ :=
    (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_closedBall hr.le)).1 ⟨⟨r, hb'⟩, by simp [hb0]⟩
  obtain ⟨g, hg, hgn, hfg⟩ := hf.meromorphicOn.extract_zeros_poles hfinite hfin
  let φ : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D a
  have hφ : AnalyticOnNhd ℂ φ (closedBall 0 r) := by
    intro z hz
    apply Function.FactorizedRational.analyticAt
    exact hD z
  have heq : EqOn f (fun z => φ z * g z) (closedBall 0 r) := by
    apply hf.eqOn_of_preconnected_of_frequently_eq (hφ.mul hg)
      isPreconnected_closedBall (mem_closedBall_self hr.le) (z₀ := 0)
    have hloc : f =ᶠ[𝓝[≠] 0] fun z => φ z * g z := by
      have hc := (mem_codiscreteWithin.mp hfg) 0 (mem_closedBall_self hr.le)
      rw [disjoint_principal_right] at hc
      have hnb : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∈ closedBall (0 : ℂ) r :=
        mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds (0 : ℂ) hr)
      filter_upwards [hc, hnb] with z hz hz'
      by_contra hn
      exact hz ⟨hz', hn⟩
    exact hloc.frequently
  refine ⟨hfin.toFinset, fun a => (D a).toNat, g, ?_, hg,
    fun z hz => hgn ⟨z, hz⟩, ?_⟩
  · intro a ha
    have haD : D a ≠ 0 := by simpa using ha
    have haB := D.supportWithinDomain (by exact haD)
    have ham : 0 < (D a).toNat := by
      have ha0 : (0 : ℤ) ≤ D a := hD a
      omega
    refine ⟨?_, ham⟩
    rw [mem_ball_zero_iff]
    have hle : ‖a‖ ≤ r := by simpa [mem_closedBall_zero_iff] using haB
    apply lt_of_le_of_ne hle
    intro he
    have hs : a ∈ sphere (0 : ℂ) r := by simpa [mem_sphere_zero_iff_norm] using he
    apply haD
    dsimp [D]
    rw [hf.meromorphicOn.divisor_apply haB]
    rw [((hf _ haB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).2 (hne a hs)]
    simp
  · intro z hz
    calc
      f z = φ z * g z := heq hz
      _ = _ := ?_
    apply congrArg (fun w => w * g z)
    dsimp [φ]
    rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset)]
    · simp only [Finset.prod_apply, Pi.pow_apply]
      apply Finset.prod_congr rfl
      intro a ha
      have hc : ((D a).toNat : ℤ) = D a := Int.toNat_of_nonneg (hD a)
      simpa only [hc] using (zpow_natCast (z - a) (D a).toNat)
    · intro a ha
      apply hfin.mem_toFinset.mpr
      simpa only [Function.FactorizedRational.mulSupport] using ha

private theorem deriv_eqOn_closedDisc {f h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hh : AnalyticOnNhd ℂ h (closedBall 0 r))
    (heq : EqOn f h (closedBall 0 r)) :
    EqOn (deriv f) (deriv h) (closedBall 0 r) := by
  have heq' := (heq.mono ball_subset_closedBall).deriv isOpen_ball
  exact heq'.of_subset_closure hf.deriv.continuousOn hh.deriv.continuousOn
    ball_subset_closedBall (by rw [closure_ball _ hr.ne'])

 

theorem contourMoment_eq_sum {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (s : Finset ℂ) (m : ℂ → ℕ)
    (hs : ∀ a ∈ s, a ∈ ball (0 : ℂ) r)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (hgn : ∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0)
    (heq : EqOn f (fun z => (∏ a ∈ s, (z - a) ^ m a) * g z)
      (closedBall 0 r)) (k : ℕ) :
    contourMoment f r k = ∑ a ∈ s, (m a : ℂ) * a ^ k := by
  classical
  let P : ℂ → ℂ := fun z => ∏ a ∈ s, (z - a) ^ m a
  have hp : AnalyticOnNhd ℂ P (closedBall 0 r) := by
    intro z hz
    exact s.analyticAt_fun_prod fun a ha => (analyticAt_id.sub analyticAt_const).pow _
  have hder := deriv_eqOn_closedDisc hr hf (hp.mul hg) heq
  have hza : ∀ z ∈ sphere (0 : ℂ) r, ∀ a ∈ s, z - a ≠ 0 := by
    intro z hz a ha he
    have hza := sub_eq_zero.mp he
    have hz' : ‖z‖ = r := by simpa using hz
    have ha' : ‖a‖ < r := by simpa using hs a ha
    rw [hza] at hz'
    exact (ne_of_lt ha') hz'
  have hld (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) :
      logDeriv f z = (∑ a ∈ s, (m a : ℂ) / (z - a)) + logDeriv g z := by
    have hzc := sphere_subset_closedBall hz
    calc
      logDeriv f z = logDeriv (fun z => P z * g z) z := by
        simp only [logDeriv_apply, hder hzc, heq hzc, P]
      _ = logDeriv P z + logDeriv g z :=
        logDeriv_mul z (Finset.prod_ne_zero_iff.mpr
          fun a ha => pow_ne_zero _ (hza z hz a ha))
          (hgn z hzc) (hp z hzc).differentiableAt (hg z hzc).differentiableAt
      _ = _ := by
        congr 1
        rw [show P = ∏ a ∈ s, fun z => (z - a) ^ m a from by
              ext point
              simp only [P, Finset.prod_apply],
          logDeriv_prod (f := fun (a z : ℂ) => (z - a) ^ m a)
            (fun a ha => pow_ne_zero _ (hza z hz a ha))
            (fun a ha => by fun_prop)]
        apply Finset.sum_congr rfl
        intro a ha
        rw [logDeriv_fun_pow (by fun_prop)]
        simp [logDeriv_apply, div_eq_mul_inv]
  let T : ℂ → ℂ → ℂ := fun a z => (m a : ℂ) * ((z - a)⁻¹ * z ^ k)
  have hTc : ∀ a ∈ s, ContinuousOn (T a) (sphere (0 : ℂ) r) := by
    intro a ha
    exact continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hza z hz a ha)
        |>.mul (continuousOn_id.pow k))
  have hT : ∀ a ∈ s, CircleIntegrable (T a) 0 r :=
    fun a ha => (hTc a ha).circleIntegrable hr.le
  have hunit : AnalyticOnNhd ℂ (fun z => z ^ k * logDeriv g z) (closedBall 0 r) := by
    exact (analyticOnNhd_id.pow k).mul (hg.deriv.div hg hgn)
  have hUi : CircleIntegrable (fun z => z ^ k * logDeriv g z) 0 r :=
    (hunit.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hSi : CircleIntegrable (fun z => ∑ a ∈ s, T a z) 0 r := by
    exact (continuousOn_finsetSum s hTc).circleIntegrable hr.le
  have hformula : (∮ z in C(0, r), z ^ k * deriv f z / f z) =
      ∑ a ∈ s, (m a : ℂ) * ((2 * Real.pi * I) * a ^ k) := by
    calc
      (∮ z in C(0, r), z ^ k * deriv f z / f z) =
          ∮ z in C(0, r), (∑ a ∈ s, T a z) + z ^ k * logDeriv g z := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        dsimp only
        rw [mul_div_assoc, ← logDeriv_apply, hld z hz, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [T]
        ring
      _ = (∑ a ∈ s, ∮ z in C(0, r), T a z) + 0 := by
        rw [circleIntegral.integral_add hSi hUi, circleIntegral.integral_fun_sum hT]
        rw [DiffContOnCl.circleIntegral_eq_zero hr.le
          (hunit.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl]
      _ = _ := by
        rw [add_zero]
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [T]
        rw [circleIntegral.integral_const_mul]
        congr 1
        exact (by simpa only [smul_eq_mul] using
          (show DifferentiableOn ℂ (fun z : ℂ => z ^ k) (closedBall 0 r) from
            by fun_prop).circleIntegral_sub_inv_smul (hs a ha))
  rw [contourMoment, hformula]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hn : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

 
theorem contourNewtonCoeff_powerSum {ι : Type*} [Fintype ι] (x : ι → ℂ) (k : ℕ) :
    contourNewtonCoeff (fun j => ∑ i, x i ^ j) k =
      (-1) ^ k * (Finset.univ.val.map x).esymm k := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [contourNewtonCoeff, Multiset.esymm]
    | succ k =>
      rw [contourNewtonCoeff]
      have hn := congrArg (MvPolynomial.aeval x)
        (MvPolynomial.mul_esymm_eq_sum ι ℂ (k + 1))
      simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
        MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum,
        MvPolynomial.aeval_X] at hn
      rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ] at hn
      simp only [lt_self_iff_false, ↓reduceIte, add_zero] at hn
      have hs : (∑ j : Fin (k + 1),
          contourNewtonCoeff (fun j => ∑ i, x i ^ j) j * ∑ i, x i ^ (k + 1 - j)) =
          ∑ j ∈ Finset.range (k + 1),
            (-1 : ℂ) ^ j * (Finset.univ.val.map x).esymm j *
              ∑ i, x i ^ (k + 1 - j) := by
        rw [Fin.sum_univ_eq_sum_range (fun j =>
          contourNewtonCoeff (fun j => ∑ i, x i ^ j) j * ∑ i, x i ^ (k + 1 - j))]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j (Finset.mem_range.mp hj)]
      rw [hs]
      have hn' : ((k + 1 : ℕ) : ℂ) * (Finset.univ.val.map x).esymm (k + 1) =
          (-1 : ℂ) ^ (k + 1 + 1) *
            ∑ j ∈ Finset.range (k + 1),
              (-1 : ℂ) ^ j * (Finset.univ.val.map x).esymm j *
                ∑ i, x i ^ (k + 1 - j) := by
        convert hn using 2
        apply Finset.sum_congr rfl
        intro j hj
        simp [Finset.mem_range.mp hj]
      have hz : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      apply (div_eq_iff hz).2
      have hsign : (-1 : ℂ) ^ (k + 1) * (-1) ^ (k + 1 + 1) = -1 := by
        rw [← pow_add]
        convert (Odd.neg_one_pow (show Odd (k + 1 + (k + 1 + 1)) by exact ⟨k + 1, by omega⟩) : _)
      have hmul := congrArg (fun z : ℂ => (-1) ^ (k + 1) * z) hn'
      simp only [← mul_assoc, hsign, neg_one_mul, Nat.cast_add, Nat.cast_one] at hmul
      linear_combination -hmul

 
theorem contourPolynomial_eq_prod {ι : Type*} [Fintype ι] (x : ι → ℂ)
    {f : ℂ → ℂ} {r : ℝ}
    (hs : ∀ k, contourMoment f r k = ∑ i, x i ^ k) :
    contourPolynomial f r (Fintype.card ι) = ∏ i, (Polynomial.X - Polynomial.C (x i)) := by
  classical
  have hf : contourMoment f r = fun k => ∑ i, x i ^ k := funext hs
  rw [contourPolynomial, hf]
  simp_rw [contourNewtonCoeff_powerSum]
  have hv := (Finset.univ.val.map x).prod_X_sub_X_eq_sum_esymm
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ,
    Multiset.map_map, Function.comp_def] at hv
  change (∏ i, (Polynomial.X - Polynomial.C (x i))) = _ at hv
  rw [hv]
  apply Finset.sum_congr rfl
  intro k hk
  simp [map_mul, map_pow, mul_assoc]

end DegeneratingTrees
end

end OAI
