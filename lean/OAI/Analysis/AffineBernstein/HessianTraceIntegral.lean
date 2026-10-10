import Mathlib
import OAI.Analysis.AffineBernstein.HessianMinors
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section HessianTraceIntegral
open Matrix

lemma trace_le_card_mul_det_add_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.trace ≤ (Fintype.card ι:ℝ)*(A+1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q*Qᵀ = 1 := by
    simpa only [Q,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have hsum : A+1 = Q * Matrix.diagonal (fun i => d i+1) * Qᵀ := by
    have he : Matrix.diagonal (fun i => d i+1) = Matrix.diagonal d+1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
    rw [he,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
  have hdet : (A+1).det = ∏ i, (d i+1) := by
    rw [hsum,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
    calc
      _ = (Q.det*Q.det)*(∏ i, (d i+1)) := by ring
      _ = _ := by rw [hdetQ,one_mul]
  have hi (i : ι) : d i ≤ ∏ j, (d j+1) := by
    have hd (j : ι) : 0 ≤ d j := hA.eigenvalues_nonneg j
    have hp : 1 ≤ ∏ j ∈ Finset.univ.erase i, (d j+1) :=
      Finset.one_le_prod₀ (fun j hj => by linarith [hd j])
    rw [← Finset.mul_prod_erase Finset.univ (fun j => d j+1) (Finset.mem_univ i)]
    nlinarith [hd i]
  rw [hdet,hA.isHermitian.trace_eq_sum_eigenvalues]
  simpa [d] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)

lemma continuous_hessian_trace {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun x => (hessian u x).trace) := by
  apply continuous_finsetSum
  intro i hi
  exact (contDiff_dirDeriv (contDiff_dirDeriv hu (coordinateVector n i)) (coordinateVector n i)).continuous

lemma integral_hessian_trace_le_ball {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : IsCompact D) {G R : ℝ}
    (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G) (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫ x in D, (hessian u x).trace) ≤
      (n:ℝ)*(volume (Metric.closedBall (0:Space n) (G+R))).toReal := by
  let F := fun x => gradient u x+x
  have hd (x : Space n) : DifferentiableAt ℝ F x :=
    ((contDiffAt_gradient hu.contDiffAt).differentiableAt (by simp)).add differentiableAt_id
  have hi : Set.InjOn F D :=
    (shiftedGradient_injOn_of_hessian_posSemidef convex_univ (fun x hx => hu.contDiffAt)
      (fun x hx => (hp x).posSemidef)).mono (subset_univ D)
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD.measurableSet
    (fun x hx => (hd x).hasFDerivAt.hasFDerivWithinAt) hi (fun _ : Space n => (1:ℝ≥0∞))
  simp only [lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] at hj
  have himage : F '' D ⊆ Metric.closedBall 0 (G+R) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (hG x hx) (hR x hx))
  have hlin : (∫⁻ x in D, ENNReal.ofReal ((hessian u x).trace)) ≤
      (n:ℝ≥0∞)*volume (Metric.closedBall (0:Space n) (G+R)) := by
    calc
      _ ≤ ∫⁻ x in D, (n:ℝ≥0∞)*ENNReal.ofReal |(fderiv ℝ F x).det| := by
        apply setLIntegral_mono' hD.measurableSet
        intro x hx
        rw [show F = (fun y => gradient u y+y) from rfl,det_fderiv_shiftedGradient hu.contDiffAt,
          abs_of_nonneg ((hp x).posSemidef.add Matrix.PosSemidef.one).det_nonneg,
          ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Fintype.card_fin] using trace_le_card_mul_det_add_one (hp x).posSemidef
      _ = (n:ℝ≥0∞)*(∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ F x).det|) := by
        rw [lintegral_const_mul']; simp
      _ ≤ _ := by rw [← hj]; exact mul_le_mul_right (measure_mono (μ := volume) himage) _
  have hiT : IntegrableOn (fun x => (hessian u x).trace) D volume :=
    ContinuousOn.integrableOn_compact hD (continuous_hessian_trace hu).continuousOn
  have hnon (x : Space n) : 0 ≤ (hessian u x).trace := (hp x).posSemidef.trace_nonneg
  have H := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
    (isCompact_closedBall (0:Space n) (G+R)).measure_lt_top.ne) hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hiT (Filter.Eventually.of_forall hnon),
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hnon),ENNReal.toReal_mul] at H
  simpa using H

end HessianTraceIntegral


end
end AffineBernstein
end

end OAI
