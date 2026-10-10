import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildDerivatives
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildData

namespace OAI

/-! Rewrite the scalar mild equation using one heat operator and the effective source. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set MeasureTheory ShearFlows
open scoped Topology Interval BigOperators

/-- A coefficient multiplied by a continuous unknown jet path. -/
def productPath {T : ℝ} (k : ℕ) (b : C(Icc (0 : ℝ) T, Jet k))
    (u : WeaklySingular.Path (Jet k) T) : WeaklySingular.Path (Jet k) T :=
  WeaklySingular.coefficientOperator (Jet k) (coefficientCurve k b) u

@[simp] theorem productPath_apply {T : ℝ} (k : ℕ) (b : C(Icc (0 : ℝ) T, Jet k))
    (u : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    productPath k b u t = multiplication k (b t) (u t) := rfl

theorem productPath_truncate {T : ℝ} (k n : ℕ) (hkn : k ≤ n)
    (b : C(Icc (0 : ℝ) T, Jet n)) (c : C(Icc (0 : ℝ) T, Jet k))
    (hbc : ∀ t, BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (b t) = c t)
    (u : WeaklySingular.Path (Jet n) T) :
    truncatePath k n hkn T (productPath n b u) =
      productPath k c (truncatePath k n hkn T u) := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  change BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (multiplication n (b t) (u t)) = _
  exact (multiplication_truncate k n hkn (b t) (u t)).trans
    (congrArg (fun z : Jet k => multiplication k z
      (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (u t))) (hbc t))

/-- All three raw kernels define bounded source operators on the finite interval. -/
def kernelSourceOperator {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ) (i : Fin 3) :
    WeaklySingular.Path (Jet k) T →L[ℝ] WeaklySingular.Path (Jet k) T :=
  WeaklySingular.integralOperator (Jet k) hT (kernels hν k T i)
    (kernels_continuous hν k T i) (kernelConstants ν T i)
    (kernelConstants_nonneg ν T i) (kernels_bound hν k T i)

@[simp] theorem kernelSourceOperator_apply {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (i : Fin 3) (u : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    kernelSourceOperator hT hν k i u t = ∫ s in 0..t.val,
      rawKernels hν k i (t.val-s) (WeaklySingular.extendPath (Jet k) hT u s) := by
  change (∫ s in 0..t.val, kernels hν k T i (t.val-s)
    (WeaklySingular.extendPath (Jet k) hT u s)) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  exact congrArg (fun L : Jet k →L[ℝ] Jet k => L
    (WeaklySingular.extendPath (Jet k) hT u s))
    (kernels_eq_raw hν k ((sub_le_self _ hs.1).trans t.property.2) i)

@[simp] theorem kernelSourceOperator_zero {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (u : WeaklySingular.Path (Jet k) T) :
    kernelSourceOperator hT hν k 0 u = heatSourcePath hT hν k u := rfl

private theorem gradient_integrand_eq_heat {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (j : Fin 2) (u : WeaklySingular.Path (Jet (k+1)) T) (r s : ℝ) :
    rawKernels hν k j.succ r
      (WeaklySingular.extendPath (Jet k) hT (truncatePath k (k+1) (by omega) T u) s) =
      rawHeatKernel hν k r
        (WeaklySingular.extendPath (Jet k) hT (directionalPath k (Pi.single j 1) T u) s) := by
  change gradientKernel hν k j r
      (WeaklySingular.extendPath (Jet k) hT (truncatePath k (k+1) (by omega) T u) s) = _
  exact (congrArg (gradientKernel hν k j r) (extendPath_truncate k (k+1) (by omega) hT u s)).trans
    ((gradientKernel_eq_heatDerivative hν k j r _).trans
      (congrArg (rawHeatKernel hν k r) (extendPath_directional hT k (Pi.single j 1) u s).symm))

private theorem gradient_integral_eq_heat {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (j : Fin 2) (u : WeaklySingular.Path (Jet (k+1)) T) (t : ℝ) :
    (∫ s in 0..t, rawKernels hν k j.succ (t-s)
      (WeaklySingular.extendPath (Jet k) hT (truncatePath k (k+1) (by omega) T u) s)) =
      ∫ s in 0..t, rawHeatKernel hν k (t-s)
        (WeaklySingular.extendPath (Jet k) hT (directionalPath k (Pi.single j 1) T u) s) :=
  intervalIntegral.integral_congr (fun s _ => gradient_integrand_eq_heat hT hν k j u (t-s) s)

/-- A spatial-gradient source operator equals heat applied to the differentiated source. -/
theorem gradientSource_eq_heatSource {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (j : Fin 2) (u : WeaklySingular.Path (Jet (k+1)) T) :
    kernelSourceOperator hT hν k j.succ (truncatePath k (k+1) (by omega) T u) =
      heatSourcePath hT hν k (directionalPath k (Pi.single j 1) T u) := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  exact (kernelSourceOperator_apply hT hν k j.succ _ t).trans
    ((gradient_integral_eq_heat hT hν k j u t.val).trans
      (heatSourcePath_apply hT hν k (directionalPath k (Pi.single j 1) T u) t).symm)

private theorem path_sum_apply {ι : Type*} [Fintype ι] {T : ℝ} (k : ℕ)
    (u : ι → WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    (∑ i, u i) t = ∑ i, u i t := by
  change (ContinuousMap.evalCLM ℝ t) ((WeaklySingular.pathEquiv (Jet k) T) (∑ i, u i)) = _
  simp only [map_sum]
  rfl

private theorem path_add_apply {T : ℝ} (k : ℕ)
    (u v : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    (u+v) t = u t+v t := rfl

private theorem linear_source_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (a b : E) (v : Fin 2 → E) :
    L a + (L b + ∑ j, L (v j)) = L (a+b+∑ j, v j) := by
  rw [map_add, map_add, map_sum]
  abel

namespace CompatibleData

/-- The unique finite-jet solution used to represent the common scalar function. -/
def solutionJet {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T) (k : ℕ) :
    WeaklySingular.Path (Jet k) T :=
  mildSolution hT hν k (D.coefficient k) (D.affinePath hT hν k)

theorem solutionJet_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k n : ℕ) (hkn : k ≤ n) :
    truncatePath k n hkn T (D.solutionJet hT hν n) = D.solutionJet hT hν k := by
  exact (mildSolution_truncate hT hν k n hkn _ _
    (D.coefficient_truncate k n hkn) (D.affinePath hT hν n)).trans
    (congrArg (mildSolution hT hν k (D.coefficient k)) (D.affinePath_truncate hT hν k n hkn))

/-- The true source after moving the drift derivatives off the heat kernel. -/
def effectiveSource {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T) (k : ℕ) :
    WeaklySingular.Path (Jet k) T :=
  D.source k + productPath k (D.coefficient k 0) (D.solutionJet hT hν k) +
    ∑ j : Fin 2, directionalPath k (Pi.single j 1) T
      (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1)))

private theorem solutionJet_eq_sources {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) :
    D.solutionJet hT hν k = D.affinePath hT hν k +
      ∑ i : Fin 3, kernelSourceOperator hT hν k i
        (productPath k (D.coefficient k i) (D.solutionJet hT hν k)) := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  change D.solutionJet hT hν k t = _
  rw [path_add_apply, path_sum_apply]
  have hu := mildSolution_spec hT hν k (D.coefficient k) (D.affinePath hT hν k) t
  exact hu.trans (congrArg (fun z : Jet k => D.affinePath hT hν k t + z)
    (Finset.sum_congr rfl (fun i _ =>
      (kernelSourceOperator_apply hT hν k i
        (productPath k (D.coefficient k i) (D.solutionJet hT hν k)) t).symm)))

private theorem gradientProduct_eq_heatSource {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (j : Fin 2) :
    kernelSourceOperator hT hν k j.succ
      (productPath k (D.coefficient k j.succ) (D.solutionJet hT hν k)) =
      heatSourcePath hT hν k (directionalPath k (Pi.single j 1) T
        (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1)))) := by
  have hp : truncatePath k (k+1) (by omega) T
      (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1))) =
      productPath k (D.coefficient k j.succ) (D.solutionJet hT hν k) :=
    (productPath_truncate k (k+1) (by omega) _ _
      (D.coefficient_truncate k (k+1) (by omega) j.succ) _).trans
      (congrArg (productPath k (D.coefficient k j.succ))
        (D.solutionJet_truncate hT hν k (k+1) (by omega)))
  exact (congrArg (kernelSourceOperator hT hν k j.succ) hp.symm).trans
    (gradientSource_eq_heatSource hT hν k j _)

/-- The common scalar solution satisfies a pure heat Duhamel equation at every jet order. -/
theorem solutionJet_heat_form {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) :
    D.solutionJet hT hν k = initialHeatPath hν k (D.initial (k+1)) +
      heatSourcePath hT hν k (D.effectiveSource hT hν k) := by
  let H : WeaklySingular.Path (Jet k) T →L[ℝ] WeaklySingular.Path (Jet k) T :=
    WeaklySingular.integralOperator (Jet k) hT (heatKernel hν k T)
      (heatKernel_continuous hν k T) (Real.sqrt (T+1)) (Real.sqrt_nonneg _)
      (heatKernel_bound hν k T)
  let p := productPath k (D.coefficient k 0) (D.solutionJet hT hν k)
  let v : Fin 2 → WeaklySingular.Path (Jet k) T := fun j =>
    directionalPath k (Pi.single j 1) T
      (productPath (k+1) (D.coefficient (k+1) j.succ) (D.solutionJet hT hν (k+1)))
  have hs : (∑ i : Fin 3, kernelSourceOperator hT hν k i
      (productPath k (D.coefficient k i) (D.solutionJet hT hν k))) =
      H p + ∑ j : Fin 2, H (v j) := by
    rw [Fin.sum_univ_succ]
    exact congrArg (fun z => H p + z)
      (Finset.sum_congr rfl (fun j _ => D.gradientProduct_eq_heatSource hT hν k j))
  have hu := D.solutionJet_eq_sources hT hν k
  calc
    D.solutionJet hT hν k =
        (initialHeatPath hν k (D.initial (k+1)) + H (D.source k)) +
          (H p + ∑ j : Fin 2, H (v j)) := by
      exact hu.trans (congrArg (fun z => D.affinePath hT hν k + z) hs)
    _ = initialHeatPath hν k (D.initial (k+1)) +
        (H (D.source k) + (H p + ∑ j : Fin 2, H (v j))) := add_assoc _ _ _
    _ = initialHeatPath hν k (D.initial (k+1)) + H (D.source k+p+∑ j, v j) :=
      congrArg (fun z => initialHeatPath hν k (D.initial (k+1)) + z)
        (linear_source_sum H (D.source k) p v)
    _ = _ := rfl

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI
