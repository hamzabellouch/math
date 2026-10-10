import OAI.InformationTheory.AmplitudeDamping.SpectralEntropy

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

/-- A finite-spectrum primitive, continuous even at a zero eigenvalue. -/
def logEntropyPrimitive (a t : ℝ) : ℝ :=
  (t + a) * Real.log (t + a) - t * Real.log t - a * Real.log (t + 1)

theorem logEntropyPrimitive_zero (a : ℝ) :
    logEntropyPrimitive a 0 = - Real.negMulLog a := by
  simp [logEntropyPrimitive, Real.negMulLog]

theorem continuousOn_logEntropyPrimitive (a : ℝ) :
    ContinuousOn (logEntropyPrimitive a) (Ici 0) := by
  have h₁ : Continuous (fun t : ℝ ↦ (t + a) * Real.log (t + a)) :=
    Real.continuous_mul_log.comp (continuous_id.add_const a)
  refine (h₁.continuousOn.sub Real.continuous_mul_log.continuousOn).sub ?_
  apply ContinuousOn.const_mul
  refine Real.continuousOn_log.comp (continuous_id.add_const 1).continuousOn ?_
  intro t ht
  change t + 1 ≠ 0
  have ht0 : 0 ≤ t := ht
  linarith

theorem hasDerivAt_logEntropyPrimitive {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (logEntropyPrimitive a)
      (Real.log (1 + a / t) - a / (t + 1)) t := by
  have hta : t + a ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith
  have h₁ := (Real.hasDerivAt_mul_log hta).comp t ((hasDerivAt_id t).add_const a)
  have h₂ := Real.hasDerivAt_mul_log ht.ne'
  have h₃ := ((Real.hasDerivAt_log ht1).comp t ((hasDerivAt_id t).add_const 1)).const_mul a
  convert! (h₁.sub h₂).sub h₃ using 1
  rw [one_add_div ht.ne', Real.log_div hta ht.ne']
  simp only [mul_one, div_eq_mul_inv]
  ring

theorem tendsto_logEntropyPrimitive (a : ℝ) :
    Tendsto (logEntropyPrimitive a) atTop (𝓝 a) := by
  have hdiff := (Real.tendsto_log_comp_add_sub_log a).sub
    (Real.tendsto_log_comp_add_sub_log 1)
  have h := (Real.tendsto_mul_log_one_add_div_atTop a).add (hdiff.const_mul a)
  simp only [sub_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-a)] with t ht hta
  have hne : t + a ≠ 0 := by linarith
  simp only [logEntropyPrimitive, one_add_div ht.ne',
    Real.log_div hne ht.ne']
  ring


theorem entropy_sum_le_of_log_sum_le {ι : Type u_1} [Fintype ι]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (htrace : ∑ i, c i * a i = 0)
    (hlog : ∀ t : ℝ, 0 < t → ∑ i, c i * Real.log (1 + a i / t) ≤ 0) :
    ∑ i, c i * Real.negMulLog (a i) ≤ 0 := by
  let H : ℝ → ℝ := fun t ↦ ∑ i, c i * logEntropyPrimitive (a i) t
  have hcont : ContinuousOn H (Ici 0) :=
    continuousOn_finsetSum _ (fun i _ ↦ (continuousOn_logEntropyPrimitive (a i)).const_mul _)
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt H (∑ i, c i * Real.log (1 + a i / t)) t := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
      (hasDerivAt_logEntropyPrimitive (ha i) ht).const_mul (c i))
    convert! h using 1
    · ext t
      simp only [H, Finset.sum_apply]
    · simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← Finset.sum_div,
        htrace, zero_div, sub_zero]
  have hanti : AntitoneOn H (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
      (fun t ht ↦ (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by rw [(hd t (by simpa using ht)).deriv]; exact hlog t (by simpa using ht))
  have hlim : Tendsto H atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ ↦
      (tendsto_logEntropyPrimitive (a i)).const_mul (c i))
    simpa only [htrace] using h
  have hzero : 0 ≤ H 0 := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hanti (by simp) ht ht)
  simpa only [H, logEntropyPrimitive_zero, mul_neg, Finset.sum_neg_distrib,
    neg_nonneg] using hzero
end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

def logDetShift (r : ℝ) (A : Matrix ι ι ℂ) : ℝ := Real.log ‖(1 + r • A).det‖

theorem det_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).det = A.det := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  rw [Matrix.det_mul, Matrix.det_one] at hu
  calc
    _ = ((U : Matrix ι ι ℂ).det * (star U : Matrix ι ι ℂ).det) * A.det := by ring
    _ = A.det := by simp only [← Unitary.coe_star, hu, one_mul]

theorem logDetShift_eq_sum {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) :
    logDetShift r A = ∑ i, Real.log (1 + r * hA.isHermitian.eigenvalues i) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have he : 1 + r • A = φ (Matrix.diagonal
      (fun i ↦ ((1 + r * hA.isHermitian.eigenvalues i : ℝ) : ℂ))) := by
    have hd : Matrix.diagonal (fun i ↦ ((1 + r * hA.isHermitian.eigenvalues i : ℝ) : ℂ)) =
        1 + r • Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [hd, map_add, map_one]
    have hm : φ (r • Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ))) =
        r • φ (Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ))) :=
      (φ.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul _ _
    rw [hm]
    congr 2
    exact hA.isHermitian.spectral_theorem
  unfold logDetShift
  rw [he, det_unitary_conj, Matrix.det_diagonal, norm_prod]
  have hp (i : ι) : 0 < 1 + r * hA.isHermitian.eigenvalues i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hA.eigenvalues_nonneg i))
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hp _)]
  exact Real.log_prod (fun i _ ↦ (hp i).ne')

/-- Entropy may be compared between unequal matrix sizes by their resolvent determinants. -/
theorem entropy_le_of_logDetShift_le {κ : Type u_3} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A ≤ logDetShift r B) :
    entropy A ≤ entropy B := by
  have htA : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]; simp
  have htB : B.trace.re = ∑ i, hB.isHermitian.eigenvalues i := by
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]; simp
  have hh := entropy_sum_le_of_log_sum_le
    (Sum.elim (fun _ : ι ↦ (1 : ℝ)) (fun _ : κ ↦ -1))
    (Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues) ?_ ?_ ?_
  · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, add_neg_le_iff_le_add, zero_add, entropy_eq_sum hA.isHermitian,
      entropy_eq_sum hB.isHermitian] using hh
  · intro i
    cases i with
    | inl i => exact hA.eigenvalues_nonneg i
    | inr i => exact hB.eigenvalues_nonneg i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, ← htA, ← htB, htrace, add_neg_cancel]
  · intro t ht
    have hh := hlog t⁻¹ (inv_pos.mpr ht)
    rw [logDetShift_eq_sum hA (inv_nonneg.mpr ht.le),
      logDetShift_eq_sum hB (inv_nonneg.mpr ht.le)] at hh
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, add_neg_le_iff_le_add, zero_add, div_eq_mul_inv, mul_comm] using hh

theorem entropy_eq_of_logDetShift_eq {κ : Type u_4} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A = logDetShift r B) :
    entropy A = entropy B :=
  le_antisymm (entropy_le_of_logDetShift_le hA hB htrace (fun r hr ↦ (hlog r hr).le))
    (entropy_le_of_logDetShift_le hB hA htrace.symm (fun r hr ↦ (hlog r hr).ge))

/-- Nonzero spectra, including their entropy, agree for both rectangular Gram matrices. -/
theorem entropy_mul_conjTranspose {κ : Type u_5} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) : entropy (A * Aᴴ) = entropy (Aᴴ * A) := by
  apply entropy_eq_of_logDetShift_eq (Matrix.posSemidef_self_mul_conjTranspose A)
    (Matrix.posSemidef_conjTranspose_mul_self A)
  · exact congrArg Complex.re (Matrix.trace_mul_comm A Aᴴ)
  · intro r _
    dsimp only [logDetShift]
    congr 2
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using
      Matrix.det_one_add_mul_comm (r • A) Aᴴ

end GAD

end

end OAI
