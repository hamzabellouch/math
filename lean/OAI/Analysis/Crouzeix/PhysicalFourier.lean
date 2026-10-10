import Mathlib
import OAI.Analysis.Crouzeix.Faber

namespace OAI

/-! Physical Fourier. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

lemma kernelLp_complex_smul {k : ℕ} (m : CircleKernel) (c : ℂ) (u : BoundaryL2 k) :
    kernelLp m (c • u) = c • kernelLp m u := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (c • u), kernelLp_apply_ae m u,
    Lp.coeFn_smul c (kernelLp m u)] with x hcu hu hsmul
  simp only [hcu, hsmul, Pi.smul_apply, hu, kernelApply]
  calc
    _ = ∫ y, c • (m (x,y) • u y) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with y hy
      rw [hy]
      exact smul_comm (m (x,y)) c (u y)
    _ = _ := integral_smul c _

@[simp] lemma boundaryField_add {k : ℕ} (F G : C(CircleSpace, Coeff k)) :
    boundaryField (F+G) = boundaryField F + boundaryField G := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (F+G), boundaryField_apply_ae F, boundaryField_apply_ae G,
    Lp.coeFn_add (boundaryField F) (boundaryField G)] with t hfg hf hg hsum
  simp only [hfg, hsum, Pi.add_apply, hf, hg, ContinuousMap.add_apply]
  exact (toHSCLM k).map_add _ _

@[simp] lemma boundaryField_smul {k : ℕ} (c : ℂ) (F : C(CircleSpace, Coeff k)) :
    boundaryField (c • F) = c • boundaryField F := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (c • F), boundaryField_apply_ae F,
    Lp.coeFn_smul c (boundaryField F)] with t hcf hf hs
  simp only [hcf, hs, Pi.smul_apply, hf, ContinuousMap.smul_apply]
  exact (toHSCLM k).map_smul _ _

@[simp] lemma boundaryField_zero {k : ℕ} : boundaryField (0 : C(CircleSpace, Coeff k)) = 0 := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (0 : C(CircleSpace, Coeff k)), Lp.coeFn_zero (E := HS k) (p := 2) circleMeasure] with t he hz
  rw [he, hz]
  exact (toHSCLM k).map_zero

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryKernel_complex (w t : CircleSpace) :
    (C.boundaryKernel (w,t) : ℂ) = 1 + C.boundaryCorrection (w,t) + conj (C.boundaryCorrection (w,t)) := by
  change (((1 : ℝ) + 2 * (C.boundaryCorrection (w,t)).re : ℝ) : ℂ) = _
  apply Complex.ext <;> simp [add_re, add_im, mul_re, mul_im]
  ring

lemma correctionMoment_continuous_trace (j : ℕ) :
    Continuous (fun w : CircleSpace => C.correctionMoment j (circleCoordinate w)⁻¹) :=
  (C.differentiableOn_correctionMoment j).continuousOn.comp_continuous
    (circleCoordinate.continuous.inv₀ circleCoordinate_ne_zero) C.circle_inverse_mem

lemma boundaryKernel_moment {j : ℕ} (hj : j ≠ 0) (w : CircleSpace) :
    (∫ t, (C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j ∂circleMeasure) =
      C.correctionMoment j (circleCoordinate w)⁻¹ := by
  have hb : Continuous (fun t => C.boundaryCorrection (w,t)) :=
    C.boundaryCorrection.continuous.comp (continuous_const.prodMk continuous_id)
  have hp := circleCoordinate.continuous.pow j
  have hi1 : Integrable (fun t => (circleCoordinate t)^j) circleMeasure :=
    hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => (circleCoordinate t)^j * C.boundaryCorrection (w,t)) circleMeasure :=
    (hp.mul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable (fun t => conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j) circleMeasure :=
    ((continuous_conj.comp hb).mul hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (∫ t : CircleSpace, ((circleCoordinate t)⁻¹)^j * C.boundaryCorrection (w,t)
      ∂circleMeasure) = 0 := by
    change (∫ t, ((circleCoordinate t)⁻¹)^j *
      C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
    rw [integral_holomorphic_inverse_circleCoordinate
      (f := fun v => v^j * C.correction v (circleCoordinate w)⁻¹)
      ((differentiableOn_id.pow j).mul
        ((C.differentiableOn_correction_left (C.circle_inverse_mem w)).mono C.closed_unit_subset_reciprocalDisk))]
    simp
  have h3 : (∫ t, conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j ∂circleMeasure) = 0 := by
    have he := congrArg conj hz
    rw [← integral_conj] at he
    simp only [map_zero] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [map_mul, map_pow, Complex.inv_eq_conj (norm_circleCoordinate t), conj_conj]
    ring
  have h1 : (∫ t : CircleSpace, (circleCoordinate t)^j ∂circleMeasure) = 0 := by
    rw [integral_holomorphic_circleCoordinate (f := fun z => z^j) (differentiableOn_id.pow j)]
    exact zero_pow hj
  have he (t : CircleSpace) : (C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j =
      (circleCoordinate t)^j + (circleCoordinate t)^j * C.boundaryCorrection (w,t) +
        conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j := by
    rw [C.boundaryKernel_complex]; ring
  simp_rw [he]
  have hi12 : Integrable (fun t => (circleCoordinate t)^j + (circleCoordinate t)^j *
      C.boundaryCorrection (w,t)) circleMeasure := hi1.add hi2
  rw [integral_add hi12 hi3, integral_add hi1 hi2, h1, h3, zero_add, add_zero]
  rfl

lemma boundaryCauchy_complex_smul (hc : Convex ℝ U) {k : ℕ} (c : ℂ) (u : BoundaryL2 k) :
    boundaryCauchy (C.boundaryOperator hc k) (c • u) =
      c • boundaryCauchy (C.boundaryOperator hc k) u := by
  change fourierProjC k 0 (c • u) + fourierProjC k 1 (c • u) +
    fourierProjC k 2 (kernelLp C.boundaryKernel (fourierProjC k 1 (c • u))) =
    c • (fourierProjC k 0 u + fourierProjC k 1 u +
      fourierProjC k 2 (kernelLp C.boundaryKernel (fourierProjC k 1 u)))
  simp only [map_smul, kernelLp_complex_smul, smul_add]

def scalarChannel {k : ℕ} (i l : Fin k) (f : C(CircleSpace, ℂ)) : C(CircleSpace, Coeff k) :=
  ⟨fun t => f t • Matrix.single i l (1 : ℂ), f.continuous.smul continuous_const⟩

def correctionChannel {k : ℕ} (a : ℕ × (Fin k × Fin k)) : C(CircleSpace, Coeff k) :=
  scalarChannel a.2.1 a.2.2
    ⟨fun t => C.correctionMoment a.1 (circleCoordinate t)⁻¹, C.correctionMoment_continuous_trace a.1⟩

lemma kernelLp_fourier_pos (hc : Convex ℝ U) {k : ℕ} (j : ℕ) (hj : j ≠ 0) (i l : Fin k) :
    C.boundaryOperator hc k (matrixFourier ((j : ℤ),i,l)) =
      boundaryField (C.correctionChannel (j,i,l)) := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae C.boundaryKernel (matrixFourier ((j : ℤ),i,l)),
    boundaryField_apply_ae (C.correctionChannel (j,i,l))] with w hw hv
  change kernelLp C.boundaryKernel _ w = _
  rw [hw, hv]
  change (∫ t, C.boundaryKernel (w,t) • matrixFourier ((j : ℤ),i,l) t ∂circleMeasure) =
    toHS (C.correctionMoment j (circleCoordinate w)⁻¹ • Matrix.single i l (1 : ℂ))
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single]
  calc
    _ = ∫ t, ((C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j) •
        EuclideanSpace.single (i,l) (1 : ℂ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [matrixFourier_apply_ae ((j : ℤ),i,l)] with t ht
      rw [ht, circleCoordinate_pow, mul_smul]
      rfl
    _ = _ := by rw [integral_smul_const, C.boundaryKernel_moment hj]

def physicalChannel {k : ℕ} (a : ℤ × (Fin k × Fin k)) : C(CircleSpace, Coeff k) :=
  scalarChannel a.2.1 a.2.2
    ⟨fun t => C.physicalCoefficient a.1 (C.boundaryMap t),
      (C.differentiableOn_physicalCoefficient a.1).continuousOn.comp_continuous
        C.boundaryMap.continuous (fun t => C.closure_subset_outerDomain
          (C.boundaryMap_mem_frontier t).1)⟩

lemma correctionChannel_negative {k : ℕ} (a : ℕ × (Fin k × Fin k)) :
    fourierProjC k 2 (boundaryField (C.correctionChannel a)) =
      boundaryField (C.correctionChannel a) := by
  apply fourierProj_boundaryField_inverse_neg (f := fun v =>
    C.correctionMoment a.1 v • Matrix.single a.2.1 a.2.2 (1 : ℂ))
  · intro i l
    exact ((C.differentiableOn_correctionMoment a.1).mono
      C.closed_unit_subset_reciprocalDisk).mul_const _
  · simp
  · exact fun _ => rfl

lemma boundaryCauchy_matrixFourier (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (a : ℤ × (Fin k × Fin k)) :
    boundaryCauchy (C.boundaryOperator hc k) (matrixFourier a) =
      boundaryField (C.physicalChannel a) := by
  classical
  change fourierProjC k 0 (matrixFourier a) + fourierProjC k 1 (matrixFourier a) +
    fourierProjC k 2 (C.boundaryOperator hc k (fourierProjC k 1 (matrixFourier a))) = _
  simp only [fourierProj_matrixFourier, frequencyPart_zero, frequencyPart_pos]
  rcases a with ⟨j,i,l⟩
  rcases lt_trichotomy j 0 with hj|hj|hj
  · simp only [ne_of_lt hj, not_lt_of_gt hj, ↓reduceIte, map_zero, zero_add]
    have he : C.physicalChannel (j,i,l) = 0 := by
      ext t a b
      obtain ⟨n,hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hj.le)
      have hjn : j = -(n : ℤ) := by omega
      have hn0 : n ≠ 0 := by omega
      change C.physicalCoefficient j (C.boundaryMap t) * _ = _
      rw [hjn, C.physicalCoefficient_closed_neg hU (C.boundaryMap_mem_frontier t).1 hn0]
      simp
    rw [he, boundaryField_zero]
  · subst j
    simp only [lt_self_iff_false, ↓reduceIte, map_zero, add_zero]
    have he : C.physicalChannel (0,i,l) = matrixLaurentMonomial (0,i,l) 1 := by
      ext t a b
      change C.physicalCoefficient 0 (C.boundaryMap t) * _ = _
      rw [C.physicalCoefficient_closed_zero hU (C.boundaryMap_mem_frontier t).1]
      simp [matrixLaurentMonomial]
    rw [he, boundaryField_matrixLaurentMonomial, one_smul]
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hj.le
    have hn : n ≠ 0 := by omega
    simp only [ne_of_gt hj, hj, ↓reduceIte, zero_add]
    rw [C.kernelLp_fourier_pos hc n hn, C.correctionChannel_negative]
    have he : C.physicalChannel ((n : ℤ),i,l) =
        matrixLaurentMonomial ((n : ℤ),i,l) 1 + C.correctionChannel (n,i,l) := by
      ext t a b
      change C.physicalCoefficient (n : ℤ) (C.G (circleCoordinate t)) * _ = _
      rw [C.physicalCoefficient_boundary n (norm_circleCoordinate t)]
      simp only [ContinuousMap.add_apply, matrixLaurentMonomial, correctionChannel,
        scalarChannel, ContinuousMap.coe_mk, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, one_mul, circleCoordinate_pow, add_mul]
    rw [he, boundaryField_add, boundaryField_matrixLaurentMonomial, one_smul]

lemma boundaryCauchy_matrixLaurentMonomial (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    boundaryCauchy (C.boundaryOperator hc k) (boundaryField (matrixLaurentMonomial a c)) =
      boundaryField (c • C.physicalChannel a) := by
  rw [boundaryField_matrixLaurentMonomial, C.boundaryCauchy_complex_smul,
    C.boundaryCauchy_matrixFourier hU hc, boundaryField_smul]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
