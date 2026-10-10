import Mathlib
import OAI.Analysis.PathSelection.ContourPolynomials
import OAI.Analysis.PathSelection.FunctionSeries

namespace OAI

/-! Analytic contour moments and fixed-contour polynomial division. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace DegeneratingTrees
open Set Metric Filter Topology Complex
open scoped BigOperators NNReal ENNReal

 

theorem analytic_contourMoment {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {r : ℝ} (hr : 0 < r) {U : Set A} (hU : IsOpen U)
    {φ ψ : A → C(sphere (0 : ℂ) r, ℂ)}
    (hφ : AnalyticOnNhd ℂ φ U) (hψ : AnalyticOnNhd ℂ ψ U)
    (hφe : ∀ q ∈ U, ∀ z : sphere (0 : ℂ) r, φ q z = F (q, z))
    (hψe : ∀ q ∈ U, ∀ z : sphere (0 : ℂ) r, ψ q z = deriv (fun y => F (q, y)) z)
    (hφn : ∀ q ∈ U, IsUnit (φ q)) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U := by
  let w : C(sphere (0 : ℂ) r, ℂ) := ⟨fun z => (z : ℂ) ^ k, continuous_subtype_val.pow k⟩
  let T : A → ℂ := fun q => (2 * Real.pi * I)⁻¹ *
    circleFunctional r hr.le (w * ψ q * Ring.inverse (φ q))
  have hT : AnalyticOnNhd ℂ T U := by
    intro q hq
    apply AnalyticAt.mul analyticAt_const
    apply (circleFunctional r hr.le).analyticAt _ |>.comp
    apply AnalyticAt.mul (analyticAt_const.mul (hψ q hq))
    exact (analyticOnNhd_inverse _ (hφn q hq)).comp (hφ q hq)
  have hTe : EqOn T (fun q => contourMoment (fun y => F (q, y)) r k) U := by
    intro q hq
    dsimp [T, contourMoment]
    congr 1
    apply circleFunctional_eq
    intro z
    simp only [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ (hφn q hq),
      hφe q hq, hψe q hq, w, ContinuousMap.coe_mk, div_eq_mul_inv]
  intro q hq
  apply (hT q hq).congr
  filter_upwards [hU.mem_nhds hq] with x hx
  exact hTe hx

 

theorem contour_fiber_factorization {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r))
    (hne : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    ∃ (d : ℕ) (g : ℂ → ℂ), contourMoment f r 0 = (d : ℂ) ∧
      (contourPolynomial f r d).Monic ∧ (contourPolynomial f r d).natDegree = d ∧
      AnalyticOnNhd ℂ g (closedBall 0 r) ∧
      (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
      EqOn f (fun z => (contourPolynomial f r d).eval z * g z) (closedBall 0 r) := by
  classical
  obtain ⟨s, m, g, hs, hg, hgn, hfg⟩ := factor_closedDisc hr hf hne
  let ι := Σ a : s, Fin (m a)
  let x : ι → ℂ := fun i => i.1
  have hm (k : ℕ) : contourMoment f r k = ∑ i : ι, x i ^ k := by
    rw [contourMoment_eq_sum hr hf s m (fun a ha => (hs a ha).1) hg hgn hfg k]
    simpa [ι, x, Fintype.sum_sigma] using
      (Finset.sum_attach s (fun a => (m a : ℂ) * a ^ k)).symm
  have hP := contourPolynomial_eq_prod (f := f) (r := r) x hm
  refine ⟨Fintype.card ι, g, ?_, ?_, ?_, hg, hgn, ?_⟩
  · simpa using hm 0
  · rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (x i)
  · rw [hP, Polynomial.natDegree_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (x i))]
    simp
  · intro z hz
    rw [hfg hz, hP]
    dsimp only
    rw [Polynomial.eval_prod]
    congr 1
    simpa [ι, x, Fintype.prod_sigma] using
      (Finset.prod_attach s (fun a => (z - a) ^ m a)).symm

private theorem nat_eq_of_complex_dist_lt_one {m n : ℕ}
    (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  have h' : |((m : ℤ) - n : ℤ)| < 1 := by
    have hc : ((m : ℂ) - n) = (((m : ℤ) - n : ℤ) : ℂ) := by push_cast; rfl
    rw [dist_eq_norm, hc, Complex.norm_intCast] at h
    exact_mod_cast h
  have he := Int.abs_lt_one_iff.mp h'
  omega

 

theorem fixed_circle_data {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F 0) {d : ℕ}
    (hd : analyticOrderAt (fun y => F (0, y)) 0 = (d : ℕ∞)) :
    ∃ (r : ℝ) (U : Set A) (φ : A → C(sphere (0 : ℂ) r, ℂ)),
      0 < r ∧ IsOpen U ∧ (0 : A) ∈ U ∧
      AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r) ∧
      AnalyticOnNhd ℂ φ U ∧
      (∀ q ∈ U, ∀ z : sphere (0 : ℂ) r, φ q z = F (q, z)) ∧
      (∀ q ∈ U, IsUnit (φ q)) ∧
      (∀ k, AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U) ∧
      (∀ q ∈ U, contourMoment (fun y => F (q, y)) r 0 = (d : ℂ)) := by
  classical
  obtain ⟨a, ha, hprof⟩ := analytic_circle_profiles hF
  have hF₀ : AnalyticAt ℂ (fun y => F (0, y)) 0 :=
    hF.comp (f := fun y : ℂ => ((0 : A), y)) (x := 0)
      (analyticAt_const.prod analyticAt_id)
  obtain ⟨g, hg, hg0, hge⟩ := hF₀.analyticOrderAt_eq_natCast.mp hd
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      F (0, z) = z ^ d * g z := by
    filter_upwards [hg.eventually_analyticAt, hg.continuousAt.eventually_ne hg0, hge]
      with z hz hn he
    exact ⟨hz, hn, by simpa using he⟩
  obtain ⟨ε, hε, hεe⟩ := Metric.mem_nhds_iff.mp hev
  let r : ℝ := min a ε / 2
  have hr : 0 < r := half_pos (lt_min ha hε)
  have hra : r < a := (half_lt_self (lt_min ha hε)).trans_le (min_le_left _ _)
  have hrε : r < ε := (half_lt_self (lt_min ha hε)).trans_le (min_le_right _ _)
  have hgeB (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ F (0, z) = z ^ d * g z :=
    hεe (lt_of_le_of_lt (show dist z 0 ≤ r from hz) hrε)
  obtain ⟨φ, ψ, hFA, hφ, hψ, hφe, hψe⟩ := hprof r hr hra
  have h0a : (0 : A) ∈ ball 0 a := mem_ball_self ha
  have hφ0 : IsUnit (φ 0) := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro z
    rw [hφe 0 h0a z, (hgeB z (sphere_subset_closedBall z.property)).2.2]
    apply mul_ne_zero _ (hgeB z (sphere_subset_closedBall z.property)).2.1
    apply pow_ne_zero
    have hnz : ‖(z : ℂ)‖ = r := by simp
    intro he
    exact hr.ne' (by simpa [he] using hnz.symm)
  have hunitN : φ ⁻¹' {v | IsUnit v} ∈ 𝓝 (0 : A) :=
    (hφ 0 h0a).continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hφ0)
  obtain ⟨b, hb, hbU⟩ := Metric.mem_nhds_iff.mp hunitN
  let V : Set A := ball 0 a ∩ ball 0 b
  have hV : IsOpen V := isOpen_ball.inter isOpen_ball
  have h0V : (0 : A) ∈ V := ⟨h0a, mem_ball_self hb⟩
  have hunit (q : A) (hq : q ∈ V) : IsUnit (φ q) := hbU hq.2
  have hm (k : ℕ) : AnalyticOnNhd ℂ
      (fun q => contourMoment (fun y => F (q, y)) r k) V :=
    analytic_contourMoment hr hV (hφ.mono inter_subset_left) (hψ.mono inter_subset_left)
      (fun q hq => hφe q hq.1) (fun q hq => hψe q hq.1) hunit k
  have hm0 : contourMoment (fun y => F (0, y)) r 0 = (d : ℂ) := by
    have heq : EqOn (fun z => F (0, z))
        (fun z => (∏ a ∈ ({0} : Finset ℂ), (z - a) ^ d) * g z) (closedBall 0 r) := by
      intro z hz
      simpa using (hgeB z hz).2.2
    have hfB : AnalyticOnNhd ℂ (fun z => F (0, z)) (closedBall 0 r) := by
      intro z hz
      exact (hFA (0, z) ⟨h0a, hz⟩).comp (analyticAt_const.prod analyticAt_id)
    simpa using contourMoment_eq_sum hr hfB ({0} : Finset ℂ) (fun _ => d)
      (by intro z hz; have he : z = 0 := Finset.mem_singleton.mp hz;
          subst z; exact mem_ball_self hr)
      (fun z hz => (hgeB z hz).1) (fun z hz => (hgeB z hz).2.1) heq 0
  have hcountN : {q : A | dist (contourMoment (fun y => F (q, y)) r 0) (d : ℂ) < 1}
      ∈ 𝓝 (0 : A) := by
    have hn := (hm 0 0 h0V).continuousAt.preimage_mem_nhds (ball_mem_nhds
      (contourMoment (fun y => F (0, y)) r 0) (show (0 : ℝ) < 1 by norm_num))
    change {q : A | dist (contourMoment (fun y => F (q, y)) r 0)
      (contourMoment (fun y => F (0, y)) r 0) < 1} ∈ 𝓝 (0 : A) at hn
    simpa only [hm0] using hn
  obtain ⟨c, hc, hcU⟩ := Metric.mem_nhds_iff.mp hcountN
  let U : Set A := V ∩ ball 0 c
  have hUV : U ⊆ V := inter_subset_left
  refine ⟨r, U, φ, hr, hV.inter isOpen_ball, ⟨h0V, mem_ball_self hc⟩,
    hFA.mono (fun x hx => ⟨hx.1.1.1, hx.2⟩), hφ.mono (fun q hq => hq.1.1),
    (fun q hq => hφe q hq.1.1), (fun q hq => hunit q hq.1),
    (fun k => (hm k).mono hUV), ?_⟩
  intro q hq
  have hfB : AnalyticOnNhd ℂ (fun z => F (q, z)) (closedBall 0 r) := by
    intro z hz
    exact (hFA (q, z) ⟨hq.1.1, hz⟩).comp (analyticAt_const.prod analyticAt_id)
  have hnB : ∀ z ∈ sphere (0 : ℂ) r, F (q, z) ≠ 0 := by
    intro z hz
    rw [← hφe q hq.1.1 ⟨z, hz⟩]
    exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hunit q hq.1) ⟨z, hz⟩
  obtain ⟨N, _, hN, _⟩ := contour_fiber_factorization hr hfB hnB
  have heNd : N = d := nat_eq_of_complex_dist_lt_one (by rw [← hN]; exact hcU hq.2)
  simpa only [heNd] using hN

 
theorem analytic_contourNewtonCoeff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {s : A → ℕ → ℂ} {U : Set A}
    (hs : ∀ k, AnalyticOnNhd ℂ (fun q => s q k) U) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => contourNewtonCoeff (s q) k) U := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [contourNewtonCoeff] using (analyticOnNhd_const :
        AnalyticOnNhd ℂ (fun _ : A => (1 : ℂ)) U)
    | succ k =>
      intro q hq
      simp only [contourNewtonCoeff]
      apply AnalyticAt.div_const
      apply AnalyticAt.neg
      apply Finset.analyticAt_fun_sum
      intro j _
      exact (ih j (Fin.is_lt j) q hq).mul (hs (k + 1 - j) q hq)

 
theorem analytic_contourPolynomial_coeff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {r : ℝ} {U : Set A}
    (hm : ∀ k, AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U)
    (d k : ℕ) :
    AnalyticOnNhd ℂ (fun q => (contourPolynomial (fun y => F (q, y)) r d).coeff k) U := by
  intro q hq
  simp only [contourPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analytic_contourNewtonCoeff hm j q hq).mul analyticAt_const

 
def contourPolynomialProfile {A : Type*} (F : A × ℂ → ℂ) (r : ℝ) (d : ℕ) (q : A) :
    C(sphere (0 : ℂ) r, ℂ) :=
  ∑ k ∈ Finset.range (d + 1),
    ContinuousMap.const _ (contourNewtonCoeff (contourMoment (fun y => F (q, y)) r) k) *
      (⟨fun z => (z : ℂ), continuous_subtype_val⟩ : C(sphere (0 : ℂ) r, ℂ)) ^ (d - k)

theorem contourPolynomialProfile_apply {A : Type*} (F : A × ℂ → ℂ) (r : ℝ) (d : ℕ)
    (q : A) (z : sphere (0 : ℂ) r) :
    contourPolynomialProfile F r d q z = (contourPolynomial (fun y => F (q, y)) r d).eval (z : ℂ) := by
  simp [contourPolynomialProfile, contourPolynomial, Polynomial.eval_finsetSum]

theorem analytic_contourPolynomialProfile {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {r : ℝ} {U : Set A}
    (hm : ∀ k, AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q, y)) r k) U) (d : ℕ) :
    AnalyticOnNhd ℂ (contourPolynomialProfile F r d) U := by
  intro q hq
  unfold contourPolynomialProfile
  apply Finset.analyticAt_fun_sum
  intro j _
  apply AnalyticAt.mul _ analyticAt_const
  exact ((ContinuousLinearMap.const ℂ (sphere (0 : ℂ) r)).analyticAt _).comp
    (analytic_contourNewtonCoeff hm j q hq)

 
def cauchyKernelProfile (r : ℝ) (y : ℂ) : C(sphere (0 : ℂ) r, ℂ) :=
  ⟨fun z => (z : ℂ), continuous_subtype_val⟩ - ContinuousMap.const _ y

@[simp] theorem cauchyKernelProfile_apply (r : ℝ) (y : ℂ) (z : sphere (0 : ℂ) r) :
    cauchyKernelProfile r y z = (z : ℂ) - y := rfl

theorem cauchyKernelProfile_isUnit {r : ℝ} {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    IsUnit (cauchyKernelProfile r y) := by
  rw [ContinuousMap.isUnit_iff_forall_ne_zero]
  intro z
  apply sub_ne_zero.mpr
  intro he
  have hz : ‖(z : ℂ)‖ = r := by simp
  have hy' : ‖y‖ < r := by simpa using hy
  change (z : ℂ) = y at he
  exact (not_lt_of_ge (by simpa only [he] using hz.ge)) hy'

theorem analytic_cauchyKernelProfile (r : ℝ) : AnalyticOnNhd ℂ (cauchyKernelProfile r) univ := by
  intro y _
  exact analyticAt_const.sub ((ContinuousLinearMap.const ℂ (sphere (0 : ℂ) r)).analyticAt y)

 

def cauchyTransformProfile {A : Type*} (r : ℝ) (hr : 0 < r)
    (κ : A → C(sphere (0 : ℂ) r, ℂ)) (x : A × ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * circleFunctional r hr.le
    (κ x.1 * Ring.inverse (cauchyKernelProfile r x.2))

theorem analytic_cauchyTransformProfile {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℂ A] {r : ℝ} (hr : 0 < r) {U : Set A}
    {κ : A → C(sphere (0 : ℂ) r, ℂ)} (hκ : AnalyticOnNhd ℂ κ U) :
    AnalyticOnNhd ℂ (cauchyTransformProfile r hr κ) (U ×ˢ ball 0 r) := by
  intro x hx
  apply analyticAt_const.mul
  apply ((circleFunctional r hr.le).analyticAt _).comp
  apply (hκ x.1 hx.1).comp analyticAt_fst |>.mul
  have hi : AnalyticAt ℂ (fun y : ℂ => Ring.inverse (cauchyKernelProfile r y)) x.2 :=
    (analyticOnNhd_inverse _ (cauchyKernelProfile_isUnit hx.2)).comp
      (analytic_cauchyKernelProfile r x.2 (mem_univ _))
  exact hi.comp analyticAt_snd

theorem cauchyTransformProfile_eq {A : Type*} {r : ℝ} (hr : 0 < r)
    {κ : A → C(sphere (0 : ℂ) r, ℂ)} {q : A} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 r))
    (he : ∀ z : sphere (0 : ℂ) r, κ q z = g z) {y : ℂ} (hy : y ∈ ball 0 r) :
    cauchyTransformProfile r hr κ (q, y) = g y := by
  have hunit := cauchyKernelProfile_isUnit hy
  have hEq : ∀ z : sphere (0 : ℂ) r,
      (κ q * Ring.inverse (cauchyKernelProfile r y)) z = ((z : ℂ) - y)⁻¹ * g z := by
    intro z
    simp only [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ hunit,
      cauchyKernelProfile_apply, he]
    ring
  rw [cauchyTransformProfile, circleFunctional_eq hr.le _ (fun z => (z - y)⁻¹ * g z) hEq]
  have hdiff : DiffContOnCl ℂ g (ball 0 r) :=
    (hg.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  simpa only [smul_eq_mul] using hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hy

 

theorem fixed_contour_preparation_on_ball {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F 0) {d : ℕ}
    (hd : analyticOrderAt (fun y => F (0, y)) 0 = (d : ℕ∞)) :
    ∃ (r : ℝ) (U : Set A) (g : A × ℂ → ℂ),
      0 < r ∧ IsOpen U ∧ (0 : A) ∈ U ∧
      AnalyticOnNhd ℂ F (U ×ˢ closedBall 0 r) ∧
      AnalyticOnNhd ℂ g (U ×ˢ ball 0 r) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r, g (q, y) ≠ 0) ∧
      (∀ q ∈ U, ∀ y ∈ sphere (0 : ℂ) r, F (q, y) ≠ 0) ∧
      (∀ q ∈ U, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d) ∧
      (∀ k, AnalyticOnNhd ℂ
        (fun q => (contourPolynomial (fun y => F (q, y)) r d).coeff k) U) ∧
      (∀ q ∈ U, ∀ y ∈ ball (0 : ℂ) r,
        F (q, y) = (contourPolynomial (fun y => F (q, y)) r d).eval y * g (q, y)) := by
  classical
  obtain ⟨r, U, φ, hr, hU, h0U, hFA, hφ, hφe, hφu, hm, hm0⟩ := fixed_circle_data hF hd
  have hfB (q : A) (hq : q ∈ U) : AnalyticOnNhd ℂ (fun y => F (q, y)) (closedBall 0 r) := by
    intro y hy
    exact (hFA (q, y) ⟨hq, hy⟩).comp (analyticAt_const.prod analyticAt_id)
  have hnB (q : A) (hq : q ∈ U) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : F (q, z) ≠ 0 := by
    rw [← hφe q hq ⟨z, hz⟩]
    exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hφu q hq) ⟨z, hz⟩
  have hfac (q : A) (hq : q ∈ U) :
      ∃ g : ℂ → ℂ, (contourPolynomial (fun y => F (q, y)) r d).Monic ∧
        (contourPolynomial (fun y => F (q, y)) r d).natDegree = d ∧
        AnalyticOnNhd ℂ g (closedBall 0 r) ∧
        (∀ z ∈ closedBall (0 : ℂ) r, g z ≠ 0) ∧
        EqOn (fun y => F (q, y))
          (fun y => (contourPolynomial (fun y => F (q, y)) r d).eval y * g y) (closedBall 0 r) := by
    obtain ⟨N, g, hN, hM, hD, hg, hgn, hfg⟩ := contour_fiber_factorization hr (hfB q hq) (hnB q hq)
    have hNd : N = d := by exact_mod_cast hN.symm.trans (hm0 q hq)
    subst N
    exact ⟨g, hM, hD, hg, hgn, hfg⟩
  have hpU (q : A) (hq : q ∈ U) : IsUnit (contourPolynomialProfile F r d q) := by
    rw [ContinuousMap.isUnit_iff_forall_ne_zero]
    intro z
    rw [contourPolynomialProfile_apply]
    obtain ⟨g, _, _, _, _, hfg⟩ := hfac q hq
    have he := hfg (sphere_subset_closedBall z.property)
    dsimp only at he
    exact left_ne_zero_of_mul (by rw [← he]; exact hnB q hq z z.property)
  let κ : A → C(sphere (0 : ℂ) r, ℂ) := fun q => φ q * Ring.inverse (contourPolynomialProfile F r d q)
  have hκ : AnalyticOnNhd ℂ κ U := by
    intro q hq
    exact (hφ q hq).mul ((analyticOnNhd_inverse _ (hpU q hq)).comp
      (analytic_contourPolynomialProfile hm d q hq))
  let g : A × ℂ → ℂ := cauchyTransformProfile r hr κ
  have hgFiber (q : A) (hq : q ∈ U) (v : ℂ → ℂ)
      (hv : AnalyticOnNhd ℂ v (closedBall 0 r))
      (hfv : EqOn (fun y => F (q, y))
        (fun y => (contourPolynomial (fun y => F (q, y)) r d).eval y * v y) (closedBall 0 r))
      (y : ℂ) (hy : y ∈ ball (0 : ℂ) r) : g (q, y) = v y := by
    apply cauchyTransformProfile_eq hr hv _ hy
    intro z
    dsimp only [κ]
    rw [ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ (hpU q hq),
      hφe q hq, contourPolynomialProfile_apply]
    have he := hfv (sphere_subset_closedBall z.property)
    dsimp only at he
    rw [he]
    have hn : (contourPolynomial (fun y => F (q, y)) r d).eval (z : ℂ) ≠ 0 := by
      rw [← contourPolynomialProfile_apply]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).1 (hpU q hq) z
    field_simp
  refine ⟨r, U, g, hr, hU, h0U, hFA, analytic_cauchyTransformProfile hr hκ, ?_, hnB, ?_,
    fun k => analytic_contourPolynomial_coeff hm d k, ?_⟩
  · intro q hq y hy
    obtain ⟨v, _, _, hv, hvn, hfv⟩ := hfac q hq
    rw [hgFiber q hq v hv hfv y hy]
    exact hvn y (ball_subset_closedBall hy)
  · intro q hq
    obtain ⟨_, hM, hD, _⟩ := hfac q hq
    exact ⟨hM, hD⟩
  · intro q hq y hy
    obtain ⟨v, _, _, hv, _, hfv⟩ := hfac q hq
    rw [hgFiber q hq v hv hfv y hy]
    exact hfv (ball_subset_closedBall hy)

 
theorem fixed_contour_preparation : FixedContourPreparationStatement := by
  intro n d F hF hd
  obtain ⟨r, U, g, hr, hU, h0, hf, hg, hgn, hfn, hP, hc, he⟩ :=
    fixed_contour_preparation_on_ball hF hd
  have hi : closedBall (0 : ℂ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  exact ⟨r, U, g, hr, hU, h0, hf, hg.mono (fun x hx => ⟨hx.1, hi hx.2⟩),
    (fun q hq y hy => hgn q hq y (hi hy)), hfn, hP, hc,
    (fun q hq y hy => he q hq y (hi hy))⟩

 
def normalizedCircleFunctional (r : ℝ) (hr : 0 < r) : C(sphere (0 : ℂ) r, ℂ) →L[ℂ] ℂ :=
  (2 * Real.pi * I)⁻¹ • circleFunctional r hr.le

 

def dividedCoeffProfile (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (k : ℕ) :
    C(sphere (0 : ℂ) r, ℂ) :=
  ∑ i ∈ Finset.Icc (k + 1) d,
    (⟨fun z => (z : ℂ), continuous_subtype_val⟩ : C(sphere (0 : ℂ) r, ℂ)) ^ (i - (k + 1)) *
      ContinuousMap.const _ (P.coeff i)

theorem dividedCoeffProfile_apply {P : Polynomial ℂ} {d : ℕ} (hd : P.natDegree = d)
    (r : ℝ) (k : ℕ) (z : sphere (0 : ℂ) r) :
    dividedCoeffProfile P d r k z = (P /ₘ (Polynomial.X - Polynomial.C (z : ℂ))).coeff k := by
  rw [Polynomial.coeff_divByMonic_X_sub_C, hd]
  simp [dividedCoeffProfile]

theorem analytic_dividedCoeffProfile {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {P : A → Polynomial ℂ} {U : Set A}
    (hP : ∀ k, AnalyticOnNhd ℂ (fun q => (P q).coeff k) U) (d : ℕ) (r : ℝ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => dividedCoeffProfile (P q) d r k) U := by
  intro q hq
  unfold dividedCoeffProfile
  apply Finset.analyticAt_fun_sum
  intro j _
  apply analyticAt_const.mul
  exact ((ContinuousLinearMap.const ℂ (sphere (0 : ℂ) r)).analyticAt _).comp (hP j q hq)

def divisionRemainder (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (κ : C(sphere (0 : ℂ) r, ℂ)) : Polynomial ℂ :=
  ∑ k : Fin d, Polynomial.C (normalizedCircleFunctional r hr (κ * dividedCoeffProfile P d r k)) *
    Polynomial.X ^ (k : ℕ)

theorem divisionRemainder_degree_lt (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (κ : C(sphere (0 : ℂ) r, ℂ)) : (divisionRemainder P d r hr κ).degree < d :=
  Polynomial.degree_sum_fin_lt _

theorem analytic_divisionRemainder_coeff {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {radius : ℝ} {P : A → Polynomial ℂ} {κ : A → C(sphere (0 : ℂ) radius, ℂ)} {U : Set A}
    (hP : ∀ k, AnalyticOnNhd ℂ (fun q => (P q).coeff k) U) (hκ : AnalyticOnNhd ℂ κ U)
    (d : ℕ) (hr : 0 < radius) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => (divisionRemainder (P q) d radius hr (κ q)).coeff k) U := by
  intro q hq
  simp only [divisionRemainder, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.analyticAt_fun_sum
  intro j _
  apply AnalyticAt.mul _ analyticAt_const
  exact ((normalizedCircleFunctional radius hr).analyticAt _).comp
    ((hκ q hq).mul (analytic_dividedCoeffProfile hP d radius j q hq))

private theorem eval_sum_of_degree_lt {P : Polynomial ℂ} {d : ℕ}
    (hd : P.degree < d) (y : ℂ) : P.eval y = ∑ k : Fin d, P.coeff k * y ^ (k : ℕ) := by
  by_cases hP : P = 0
  · simp [hP]
  · rw [Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt hP).2 hd)]
    exact (Fin.sum_univ_eq_sum_range _ _).symm

def dividedEvaluationProfile (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (y : ℂ) :
    C(sphere (0 : ℂ) r, ℂ) := ∑ k : Fin d, (y ^ (k : ℕ)) • dividedCoeffProfile P d r k

theorem dividedEvaluationProfile_apply {P : Polynomial ℂ} (hP : P.Monic) {d : ℕ}
    (hd : P.natDegree = d) (r : ℝ) (y : ℂ) (z : sphere (0 : ℂ) r) :
    dividedEvaluationProfile P d r y z = (P /ₘ (Polynomial.X - Polynomial.C (z : ℂ))).eval y := by
  have hdeg : (P /ₘ (Polynomial.X - Polynomial.C (z : ℂ))).degree < d := by
    have hi := Polynomial.degree_divByMonic_lt P (Polynomial.X - Polynomial.C (z : ℂ))
      hP.ne_zero (by simp)
    simpa [Polynomial.degree_eq_natDegree hP.ne_zero, hd] using hi
  rw [eval_sum_of_degree_lt hdeg]
  simp only [dividedEvaluationProfile, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, dividedCoeffProfile_apply hd]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem divisionRemainder_eval (P : Polynomial ℂ) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (κ : C(sphere (0 : ℂ) r, ℂ)) (y : ℂ) :
    (divisionRemainder P d r hr κ).eval y =
      normalizedCircleFunctional r hr (κ * dividedEvaluationProfile P d r y) := by
  simp only [divisionRemainder, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, dividedEvaluationProfile,
    Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

theorem fixed_circle_division {P : Polynomial ℂ} (hP : P.Monic) {d : ℕ}
    (hd : P.natDegree = d) {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (closedBall 0 r))
    (hPn : ∀ z ∈ sphere (0 : ℂ) r, P.eval z ≠ 0)
    (κ : C(sphere (0 : ℂ) r, ℂ))
    (hκ : ∀ z : sphere (0 : ℂ) r, κ z = G z / P.eval (z : ℂ))
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) :
    G y = P.eval y * cauchyTransformProfile r hr (fun _ : Unit => κ) ((), y) +
      (divisionRemainder P d r hr κ).eval y := by
  have hk := cauchyKernelProfile_isUnit hy
  let T := κ * Ring.inverse (cauchyKernelProfile r y)
  let R := κ * dividedEvaluationProfile P d r y
  have hboundary : ∀ z : sphere (0 : ℂ) r,
      ((P.eval y) • T + R) z = ((z : ℂ) - y)⁻¹ * G z := by
    intro z
    have hdiff := congrArg (Polynomial.eval y) (P.modByMonic_add_div (Polynomial.X - Polynomial.C (z : ℂ)))
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hdiff
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at hdiff
    have hn : (z : ℂ) - y ≠ 0 :=
      (ContinuousMap.isUnit_iff_forall_ne_zero _).1 hk z
    simp only [T, R, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
      ContinuousMap.mul_apply, continuousMap_ringInverse_apply _ hk,
      cauchyKernelProfile_apply, dividedEvaluationProfile_apply hP hd, hκ]
    field_simp [hPn z z.property, hn]
    linear_combination -(G (z : ℂ)) * hdiff
  have hc : normalizedCircleFunctional r hr ((P.eval y) • T + R) = G y := by
    change (2 * Real.pi * I)⁻¹ * circleFunctional r hr.le ((P.eval y) • T + R) = G y
    rw [circleFunctional_eq hr.le _ (fun z => (z - y)⁻¹ * G z) hboundary]
    have hdiff : DiffContOnCl ℂ G (ball 0 r) :=
      (hG.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
    simpa only [smul_eq_mul] using hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hy
  rw [divisionRemainder_eval, ← hc, map_add, map_smul]
  rfl

end DegeneratingTrees
end

end OAI
