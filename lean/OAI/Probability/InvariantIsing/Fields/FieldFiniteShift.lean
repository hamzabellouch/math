import OAI.Probability.InvariantIsing.Fields.FieldFiniteFamily

namespace OAI

/-! Joint covariance-coordinate chain rules for a single affine
Gaussian mark. These formulas preserve the symmetric height Hessian. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldFiniteVariance_hasFDerivAt {n : ℕ} (a : ℝ) (v : Fin n → ℝ)
    (p : FieldCovariate n) :
    HasFDerivAt (fun q : FieldCovariate n => fieldFiniteVariance a v q.1)
      (fieldFiniteLinear v 0) p := by
  have h := ((fieldFiniteLinear v 0).hasFDerivAt (x := p)).const_add a
  convert h using 1
  funext q
  simp [fieldFiniteVariance]

lemma fieldFiniteRoot_hasFDerivAt {n : ℕ} (a : ℝ) (v : Fin n → ℝ)
    {p : FieldCovariate n} (hp : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (fun q : FieldCovariate n => Real.sqrt (fieldFiniteVariance a v q.1))
      ((1 / (2 * Real.sqrt (fieldFiniteVariance a v p.1))) • fieldFiniteLinear v 0) p := by
  convert (Real.hasDerivAt_sqrt hp.ne').hasFDerivAt.comp p
    (fieldFiniteVariance_hasFDerivAt a v p) using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro q
    simp [mul_comm, Finset.mul_sum]

lemma field_finite_affine_shift_hasFDerivAt {n : ℕ} {I : Set (Fin n → ℝ)}
    {U : FieldCovariate n → ℝ} {A : Fin n → FieldCovariate n → ℝ}
    {B : FieldCovariate n → ℝ}
    (hd : ∀ q, q.1 ∈ I → HasFDerivAt U (fieldFiniteLinear (fun i => A i q) (B q)) q)
    (a : ℝ) (v : Fin n → ℝ) (u : ℝ) {p : FieldCovariate n}
    (hp : p.1 ∈ I) (hv : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (fun q : FieldCovariate n => U (q.1, q.2 + Real.sqrt (fieldFiniteVariance a v q.1) * u))
      (fieldFiniteLinear
        (fun i => A i (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) +
          B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) *
            (fieldFiniteSlope a v p.1 i * u))
        (B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u))) p := by
  have hroot := fieldFiniteRoot_hasFDerivAt a v hv
  have harg := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add (hroot.mul_const u))
  have h := (hd (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) hp).comp p harg
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro q
    simp only [fieldFiniteLinear_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul, fieldFiniteSlope]
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have hs :
        (∑ i, B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) *
          (v i / (2 * Real.sqrt (fieldFiniteVariance a v p.1)) * u) * q.1 i) =
        ∑ i, B (p.1, p.2 + Real.sqrt (fieldFiniteVariance a v p.1) * u) *
          (u * (1 / (2 * Real.sqrt (fieldFiniteVariance a v p.1)) * (v i * q.1 i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring

lemma fieldFiniteSlope_hasFDerivAt {n : ℕ} (a : ℝ) (v : Fin n → ℝ) (i : Fin n)
    {p : FieldCovariate n} (hp : 0 < fieldFiniteVariance a v p.1) :
    HasFDerivAt (fun q : FieldCovariate n => fieldFiniteSlope a v q.1 i)
      (fieldFiniteLinear (fun j => fieldFiniteCurvature a v p.1 i j) 0) p := by
  have hroot := fieldFiniteRoot_hasFDerivAt a v hp
  have hi := ((hasDerivAt_inv (Real.sqrt_pos.mpr hp).ne').hasFDerivAt.comp p hroot).const_mul (v i / 2)
  convert hi using 1
  · funext q
    simp only [fieldFiniteSlope, Function.comp_def]
    ring
  · apply ContinuousLinearMap.ext
    intro q
    simp only [fieldFiniteLinear_apply, ContinuousLinearMap.comp_apply,
      smul_apply, smul_eq_mul, fieldFiniteCurvature, fieldFiniteSlope,
      zero_mul, add_zero, Finset.mul_sum,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [Real.sq_sqrt hp.le]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end InvariantIsing

end

end OAI
