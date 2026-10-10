import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildEquation

namespace OAI

/-! Compatibility of finite-jet mild solutions under lossless truncation. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Real MeasureTheory Set ShearFlows
open scoped Topology Interval BigOperators

/-- Truncate every value of a continuous jet path. -/
def truncatePath (k n : ℕ) (hkn : k ≤ n) (T : ℝ) :
    WeaklySingular.Path (Jet n) T →L[ℝ] WeaklySingular.Path (Jet k) T :=
  (WeaklySingular.pathEquiv (Jet k) T).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((BoundedSpatialJets.truncateCLM Plane ℝ k n hkn).compLeftContinuous ℝ (Icc (0 : ℝ) T)).comp
      (WeaklySingular.pathEquiv (Jet n) T).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem truncatePath_apply (k n : ℕ) (hkn : k ≤ n) (T : ℝ)
    (u : WeaklySingular.Path (Jet n) T) (t : Icc (0 : ℝ) T) :
    truncatePath k n hkn T u t = BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (u t) := rfl

theorem extendPath_truncate (k n : ℕ) (hkn : k ≤ n) {T : ℝ} (hT : 0 ≤ T)
    (u : WeaklySingular.Path (Jet n) T) (s : ℝ) :
    WeaklySingular.extendPath (Jet k) hT (truncatePath k n hkn T u) s =
      BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (WeaklySingular.extendPath (Jet n) hT u s) := rfl

/-- Any two jet paths representing the same scalar function agree after truncation. -/
theorem truncatePath_eq_of_functions (k n : ℕ) (hkn : k ≤ n) (T : ℝ)
    (u : WeaklySingular.Path (Jet n) T) (v : WeaklySingular.Path (Jet k) T)
    (h : ∀ t x, BoundedSpatialJets.function Plane ℝ n (u t) x =
      BoundedSpatialJets.function Plane ℝ k (v t) x) :
    truncatePath k n hkn T u = v := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  apply BoundedSpatialJets.function_injective Plane ℝ k
  ext x
  change BoundedSpatialJets.function Plane ℝ k
    (BoundedSpatialJets.truncate Plane ℝ k n hkn (u t)) x = _
  rw [BoundedSpatialJets.function_truncate]
  exact h t x

/-- Representing the same coefficient function forces compatibility of its finite jets. -/
theorem coefficient_truncate_of_functions (k n : ℕ) (hkn : k ≤ n) (T : ℝ)
    (b : C(Icc (0 : ℝ) T, Jet n)) (c : C(Icc (0 : ℝ) T, Jet k))
    (h : ∀ t x, BoundedSpatialJets.function Plane ℝ n (b t) x =
      BoundedSpatialJets.function Plane ℝ k (c t) x) (t : Icc (0 : ℝ) T) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b t) = c t := by
  apply BoundedSpatialJets.function_injective Plane ℝ k
  ext x
  change BoundedSpatialJets.function Plane ℝ k
    (BoundedSpatialJets.truncate Plane ℝ k n hkn (b t)) x = _
  rw [BoundedSpatialJets.function_truncate]
  exact h t x

theorem multiplication_truncate (k n : ℕ) (hkn : k ≤ n) (b u : Jet n) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (multiplication n b u) =
      multiplication k (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn b)
        (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn u) := by
  apply BoundedSpatialJets.function_injective Plane ℝ k
  ext x
  change BoundedSpatialJets.function Plane ℝ k
      (BoundedSpatialJets.truncate Plane ℝ k n hkn (multiplication n b u)) x = _
  simp only [BoundedSpatialJets.function_truncate, multiplication_apply]
  rfl

theorem rawHeatKernel_truncate {ν : ℝ} (hν : 0 < ν) (k n : ℕ) (hkn : k ≤ n)
    (r : ℝ) (u : Jet n) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (rawHeatKernel hν n r u) =
      rawHeatKernel hν k r (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn u) := by
  by_cases hr : 0 < r
  · rw [rawHeatKernel_pos hν n hr, rawHeatKernel_pos hν k hr]
    exact (BoundedSpatialJets.convolution_truncate Plane ℝ k n hkn volume
      (PlaneHeat.kernel (ν*r)) (PlaneHeat.kernel_integrable (mul_pos hν hr)) u).symm
  · simp only [rawHeatKernel_nonpos hν n (not_lt.mp hr),
      rawHeatKernel_nonpos hν k (not_lt.mp hr), zero_apply, map_zero]

theorem gradientKernel_truncate {ν : ℝ} (hν : 0 < ν) (k n : ℕ) (hkn : k ≤ n)
    (j : Fin 2) (r : ℝ) (u : Jet n) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (gradientKernel hν n j r u) =
      gradientKernel hν k j r (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn u) := by
  by_cases hr : 0 < r
  · rw [gradientKernel_pos hν n j hr, gradientKernel_pos hν k j hr]
    exact (BoundedSpatialJets.convolution_truncate Plane ℝ k n hkn volume
      (PlaneHeat.kernelDerivative (ν*r) j)
      (PlaneHeat.kernelDerivative_integrable (mul_pos hν hr) j) u).symm
  · simp only [gradientKernel_nonpos hν n j (not_lt.mp hr),
      gradientKernel_nonpos hν k j (not_lt.mp hr), zero_apply, map_zero]

theorem rawKernels_truncate {ν : ℝ} (hν : 0 < ν) (k n : ℕ) (hkn : k ≤ n)
    (i : Fin 3) (r : ℝ) (u : Jet n) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (rawKernels hν n i r u) =
      rawKernels hν k i r (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn u) := by
  exact Fin.cases (rawHeatKernel_truncate hν k n hkn r u)
    (fun j => gradientKernel_truncate hν k n hkn j r u) i

/-- A continuous source path gives Bochner-integrable heat and gradient integrands. -/
theorem rawKernel_path_integrable {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (u : WeaklySingular.Path (Jet k) T)
    (i : Fin 3) (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => rawKernels hν k i (t.val-s)
      (WeaklySingular.extendPath (Jet k) hT u s)) volume 0 t.val := by
  let v := u
  let z := WeaklySingular.extendPath (Jet k) hT v
  have hz : Continuous z := WeaklySingular.continuous_extendPath (Jet k) hT v
  have hm : AEStronglyMeasurable (fun s => kernels hν k T i (t.val-s) (z s))
      (volume.restrict (Ioc 0 t.val)) := by
    have hc : ContinuousOn (fun s => kernels hν k T i (t.val-s) (z s)) (Ioo 0 t.val) := by
      intro s hs
      have hk : ContinuousAt (fun r : ℝ => kernels hν k T i (t.val-r)) s :=
        ((kernels_continuous hν k T i).continuousAt (Ioi_mem_nhds (sub_pos.mpr hs.2))).comp
          (f := fun r : ℝ => t.val-r) (continuousAt_const.sub continuousAt_id)
      exact (hk.clm_apply hz.continuousAt).continuousWithinAt
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hc.aestronglyMeasurable measurableSet_Ioo
  have hi : IntervalIntegrable (fun s => kernels hν k T i (t.val-s) (z s)) volume 0 t.val := by
    apply WeaklySingular.intervalIntegrable_of_inverseSqrt_bound (Jet k) t.property.1 _
      (kernelConstants ν T i * ‖v‖) hm
    intro s hs
    have hr : 0 ≤ t.val-s := sub_nonneg.mpr hs.2
    calc
      _ ≤ ‖kernels hν k T i (t.val-s)‖ * ‖z s‖ := (kernels hν k T i (t.val-s)).le_opNorm _
      _ ≤ (kernelConstants ν T i * WeaklySingular.inverseSqrt (t.val-s)) * ‖v‖ :=
        mul_le_mul (kernels_bound hν k T i _ hr)
          (WeaklySingular.norm_extendPath_le (Jet k) hT v s) (norm_nonneg _)
          (mul_nonneg (kernelConstants_nonneg ν T i) (WeaklySingular.inverseSqrt_nonneg _))
      _ = _ := by ring
  apply hi.congr
  intro s hs
  rw [uIoc_of_le t.property.1] at hs
  dsimp only
  rw [kernels_eq_raw hν k ((sub_le_self _ hs.1.le).trans t.property.2) i]

/-- The actual coefficient/kernel integrands are integrable at the singular endpoint. -/
theorem mild_integrand_integrable {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (b : C(Icc (0 : ℝ) T, Jet k)) (u : WeaklySingular.Path (Jet k) T)
    (i : Fin 3) (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => rawKernels hν k i (t.val-s)
      (multiplication k (b (projIcc 0 T hT s))
        (WeaklySingular.extendPath (Jet k) hT u s))) volume 0 t.val := by
  exact rawKernel_path_integrable hT hν k
    (WeaklySingular.coefficientOperator (Jet k) (coefficientCurve k b) u) i t

section IntegralTransport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem map_integral_eq (P : E →L[ℝ] F) {f : ℝ → E} {g : ℝ → F}
    {t : ℝ} (hi : IntervalIntegrable f volume 0 t) (he : ∀ s, P (f s) = g s) :
    P (∫ s in 0..t, f s) = ∫ s in 0..t, g s := by
  exact (P.intervalIntegral_comp_comm hi).symm.trans
    (intervalIntegral.integral_congr (fun s _ => he s))

omit [CompleteSpace E] [CompleteSpace F] in
private theorem map_add_finite_sum {ι : Type*} [Fintype ι]
    (P : E →L[ℝ] F) (x : E) (v : ι → E) :
    P (x + ∑ i, v i) = P x + ∑ i, P (v i) := by
  rw [map_add, map_sum]

end IntegralTransport

/-- Truncation commutes with the actual unweighted heat and gradient integrals. -/
theorem rawKernelIntegral_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n) (u : WeaklySingular.Path (Jet n) T)
    (i : Fin 3) (t : Icc (0 : ℝ) T) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (WeaklySingular.extendPath (Jet n) hT u s)) =
      ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (WeaklySingular.extendPath (Jet k) hT (truncatePath k n hkn T u) s) := by
  apply map_integral_eq (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn)
    (rawKernel_path_integrable hT hν n u i t)
  intro s
  exact (rawKernels_truncate hν k n hkn i (t.val-s) _).trans
    (congrArg (rawKernels hν k i (t.val-s))
      (extendPath_truncate k n hkn hT u s).symm)

private theorem truncate_integrand {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n)
    (b : Fin 3 → C(Icc (0 : ℝ) T, Jet n))
    (c : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hbc : ∀ i t, BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b i t) = c i t)
    (u : WeaklySingular.Path (Jet n) T) (i : Fin 3) (t : ℝ) (s : ℝ) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (rawKernels hν n i (t-s) (multiplication n (b i (projIcc 0 T hT s))
        (WeaklySingular.extendPath (Jet n) hT u s))) =
      rawKernels hν k i (t-s)
        (multiplication k (c i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT (truncatePath k n hkn T u) s)) := by
  exact (rawKernels_truncate hν k n hkn i (t-s) _).trans
    (congrArg (rawKernels hν k i (t-s))
      ((multiplication_truncate k n hkn _ _).trans
        (congrArg₂ (fun b u : Jet k => multiplication k b u) (hbc i (projIcc 0 T hT s))
          (extendPath_truncate k n hkn hT u s).symm)))

private theorem truncate_integral_term {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n)
    (b : Fin 3 → C(Icc (0 : ℝ) T, Jet n))
    (c : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hbc : ∀ i t, BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b i t) = c i t)
    (u : WeaklySingular.Path (Jet n) T) (i : Fin 3) (t : Icc (0 : ℝ) T) :
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (multiplication n (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet n) hT u s))) =
      ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (c i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT (truncatePath k n hkn T u) s)) :=
  map_integral_eq (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn)
    (mild_integrand_integrable hT hν n (b i) u i t)
    (truncate_integrand hT hν k n hkn b c hbc u i t.val)

/-- A high-order solution truncates to the low-order equation with truncated data. -/
theorem truncate_mild_equation {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n)
    (b : Fin 3 → C(Icc (0 : ℝ) T, Jet n))
    (c : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hbc : ∀ i t, BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b i t) = c i t)
    (a u : WeaklySingular.Path (Jet n) T)
    (hu : ∀ t : Icc (0 : ℝ) T, u t = a t +
      ∑ i, ∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (multiplication n (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet n) hT u s))) :
    ∀ t : Icc (0 : ℝ) T, truncatePath k n hkn T u t = truncatePath k n hkn T a t +
      ∑ i, ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (c i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT (truncatePath k n hkn T u) s)) := by
  intro t
  let P : Jet n →L[ℝ] Jet k := BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
  change P (u t) = P (a t) + _
  calc
    P (u t) = P (a t + ∑ i, ∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (multiplication n (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet n) hT u s))) := congrArg P (hu t)
    _ = P (a t) + ∑ i, P (∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (multiplication n (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet n) hT u s))) :=
      map_add_finite_sum P (a t) (fun i => ∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (multiplication n (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet n) hT u s)))
    _ = _ := congrArg (fun v : Jet k => P (a t) + v)
      (Finset.sum_congr rfl (fun i _ => truncate_integral_term hT hν k n hkn b c hbc u i t))

/-- Uniqueness identifies solutions at different jet orders, independently of the chosen weight. -/
theorem mild_solutions_compatible {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k n : ℕ) (hkn : k ≤ n)
    (b : Fin 3 → C(Icc (0 : ℝ) T, Jet n))
    (c : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hbc : ∀ i t, BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b i t) = c i t)
    (a u : WeaklySingular.Path (Jet n) T) (v : WeaklySingular.Path (Jet k) T)
    (hu : ∀ t : Icc (0 : ℝ) T, u t = a t +
      ∑ i, ∫ s in 0..t.val, rawKernels hν n i (t.val-s)
        (multiplication n (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet n) hT u s)))
    (hv : ∀ t : Icc (0 : ℝ) T, v t = truncatePath k n hkn T a t +
      ∑ i, ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (c i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT v s))) :
    truncatePath k n hkn T u = v := by
  obtain ⟨w, _, huniq⟩ := exists_unique_mild hT hν k c (truncatePath k n hkn T a)
  exact (huniq _ (truncate_mild_equation hT hν k n hkn b c hbc a u hu)).trans (huniq v hv).symm

end ForcedComputation.PlaneScalarMild

end

end OAI
