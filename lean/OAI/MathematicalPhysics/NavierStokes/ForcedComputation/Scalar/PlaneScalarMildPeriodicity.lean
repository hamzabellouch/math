import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildPointwise
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetTranslation

namespace OAI

/-! Spatial periodicity of the actual scalar mild solution, by translation and uniqueness. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows MeasureTheory
open scoped Topology Interval BigOperators

def translationPath (k : ℕ) (a : Plane) (T : ℝ) :
    WeaklySingular.Path (Jet k) T →L[ℝ] WeaklySingular.Path (Jet k) T :=
  (WeaklySingular.pathEquiv (Jet k) T).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((BoundedSpatialJets.translationCLM Plane ℝ k a).compLeftContinuous ℝ (Icc (0 : ℝ) T)).comp
      (WeaklySingular.pathEquiv (Jet k) T).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem translationPath_apply (k : ℕ) (a : Plane) (T : ℝ)
    (u : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) :
    translationPath k a T u t = BoundedSpatialJets.translationCLM Plane ℝ k a (u t) := rfl

theorem extendPath_translation {T : ℝ} (hT : 0 ≤ T) (k : ℕ) (a : Plane)
    (u : WeaklySingular.Path (Jet k) T) (s : ℝ) :
    WeaklySingular.extendPath (Jet k) hT (translationPath k a T u) s =
      BoundedSpatialJets.translationCLM Plane ℝ k a (WeaklySingular.extendPath (Jet k) hT u s) := rfl

theorem multiplication_translation (k : ℕ) (a : Plane) (b u : Jet k) :
    BoundedSpatialJets.translationCLM Plane ℝ k a (multiplication k b u) =
      multiplication k (BoundedSpatialJets.translationCLM Plane ℝ k a b)
        (BoundedSpatialJets.translationCLM Plane ℝ k a u) := by
  apply BoundedSpatialJets.function_injective Plane ℝ k
  apply BoundedContinuousFunction.ext
  intro x
  simp only [BoundedSpatialJets.translationCLM_apply, BoundedSpatialJets.function_translation,
    multiplication_apply]

theorem rawHeatKernel_translation {ν : ℝ} (hν : 0 < ν) (k : ℕ) (a : Plane)
    (r : ℝ) (u : Jet k) :
    BoundedSpatialJets.translationCLM Plane ℝ k a (rawHeatKernel hν k r u) =
      rawHeatKernel hν k r (BoundedSpatialJets.translationCLM Plane ℝ k a u) := by
  by_cases hr : 0 < r
  · rw [rawHeatKernel_pos hν k hr]
    exact BoundedSpatialJets.translation_convolution Plane ℝ k a volume
      (PlaneHeat.kernel (ν*r)) (PlaneHeat.kernel_integrable (mul_pos hν hr)) u
  · simp only [rawHeatKernel_nonpos hν k (not_lt.mp hr), zero_apply, map_zero]

theorem gradientKernel_translation {ν : ℝ} (hν : 0 < ν) (k : ℕ) (a : Plane)
    (j : Fin 2) (r : ℝ) (u : Jet k) :
    BoundedSpatialJets.translationCLM Plane ℝ k a (gradientKernel hν k j r u) =
      gradientKernel hν k j r (BoundedSpatialJets.translationCLM Plane ℝ k a u) := by
  by_cases hr : 0 < r
  · rw [gradientKernel_pos hν k j hr]
    exact BoundedSpatialJets.translation_convolution Plane ℝ k a volume
      (PlaneHeat.kernelDerivative (ν*r) j)
      (PlaneHeat.kernelDerivative_integrable (mul_pos hν hr) j) u
  · simp only [gradientKernel_nonpos hν k j (not_lt.mp hr), zero_apply, map_zero]

theorem rawKernels_translation {ν : ℝ} (hν : 0 < ν) (k : ℕ) (a : Plane)
    (i : Fin 3) (r : ℝ) (u : Jet k) :
    BoundedSpatialJets.translationCLM Plane ℝ k a (rawKernels hν k i r u) =
      rawKernels hν k i r (BoundedSpatialJets.translationCLM Plane ℝ k a u) :=
  Fin.cases (rawHeatKernel_translation hν k a r u)
    (fun j => gradientKernel_translation hν k a j r u) i

theorem evolutionOperator_translation (k : ℕ) (a : Plane) (r : ℝ) (u : Jet k) :
    BoundedSpatialJets.translationCLM Plane ℝ k a (PlaneHeat.evolutionOperator ℝ k r u) =
      PlaneHeat.evolutionOperator ℝ k r (BoundedSpatialJets.translationCLM Plane ℝ k a u) := by
  by_cases hr : 0 < r
  · simp only [PlaneHeat.evolutionOperator, dite_eq_left hr]
    exact BoundedSpatialJets.translation_convolution Plane ℝ k a volume
      (PlaneHeat.kernel r) (PlaneHeat.kernel_integrable hr) u
  · simp only [PlaneHeat.evolutionOperator, dite_eq_right hr, ContinuousLinearMap.id_apply]

private theorem translate_mild_integrand {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (a : Plane) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hb : ∀ i t, BoundedSpatialJets.translationCLM Plane ℝ k a (b i t) = b i t)
    (u : WeaklySingular.Path (Jet k) T) (i : Fin 3) (t s : ℝ) :
    BoundedSpatialJets.translationCLM Plane ℝ k a
      (rawKernels hν k i (t-s) (multiplication k (b i (projIcc 0 T hT s))
        (WeaklySingular.extendPath (Jet k) hT u s))) =
      rawKernels hν k i (t-s) (multiplication k (b i (projIcc 0 T hT s))
        (WeaklySingular.extendPath (Jet k) hT (translationPath k a T u) s)) := by
  exact (rawKernels_translation hν k a i (t-s) _).trans
    (congrArg (rawKernels hν k i (t-s))
      ((multiplication_translation k a _ _).trans
        (congrArg₂ (fun p q : Jet k => multiplication k p q)
          (hb i _) (extendPath_translation hT k a u s).symm)))

private theorem translate_mild_integral {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (a : Plane) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hb : ∀ i t, BoundedSpatialJets.translationCLM Plane ℝ k a (b i t) = b i t)
    (u : WeaklySingular.Path (Jet k) T) (i : Fin 3) (t : Icc (0 : ℝ) T) :
    BoundedSpatialJets.translationCLM Plane ℝ k a
      (∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (b i (projIcc 0 T hT s)) (WeaklySingular.extendPath (Jet k) hT u s))) =
      ∫ s in 0..t.val, rawKernels hν k i (t.val-s)
        (multiplication k (b i (projIcc 0 T hT s))
          (WeaklySingular.extendPath (Jet k) hT (translationPath k a T u) s)) :=
  map_integral_eq (BoundedSpatialJets.translationCLM Plane ℝ k a)
    (mild_integrand_integrable hT hν k (b i) u i t)
    (translate_mild_integrand hT hν k a b hb u i t.val)

private theorem map_add_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (u : E) (v : Fin 3 → E) :
    P (u + ∑ i, v i) = P u + ∑ i, P (v i) := by
  rw [map_add, map_sum]

/-- A translation preserving the data also preserves the unique mild solution. -/
theorem mildSolution_translation {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (a : Plane) (b : Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hb : ∀ i t, BoundedSpatialJets.translationCLM Plane ℝ k a (b i t) = b i t)
    (g : WeaklySingular.Path (Jet k) T)
    (hg : ∀ t, BoundedSpatialJets.translationCLM Plane ℝ k a (g t) = g t) :
    translationPath k a T (mildSolution hT hν k b g) = mildSolution hT hν k b g := by
  let u := mildSolution hT hν k b g
  have hsol (t : Icc (0 : ℝ) T) := mildSolution_spec hT hν k b g t
  apply (Classical.choose_spec (exists_unique_mild hT hν k b g)).2
  intro t
  change BoundedSpatialJets.translationCLM Plane ℝ k a (u t) = _
  have he := congrArg (BoundedSpatialJets.translationCLM Plane ℝ k a) (hsol t)
  exact he.trans ((map_add_sum _ _ _).trans
    (congrArg₂ (fun x y : Jet k => x+y) (hg t)
      (Finset.sum_congr rfl (fun i _ => translate_mild_integral hT hν k a b hb u i t))))

namespace CompatibleData

private theorem affinePath_translation {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) (a : Plane)
    (hI : BoundedSpatialJets.translationCLM Plane ℝ k a (D.initial k) = D.initial k)
    (hg : ∀ t, BoundedSpatialJets.translationCLM Plane ℝ k a (D.source k t) = D.source k t)
    (t : Icc (0 : ℝ) T) :
    BoundedSpatialJets.translationCLM Plane ℝ k a (D.affinePath hT hν k t) =
      D.affinePath hT hν k t := by
  have hJ : BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) (D.initial (k+1)) =
      D.initial k := D.initial_truncate k (k+1) (by omega)
  have hf : D.affinePath hT hν k t = PlaneHeat.evolutionOperator ℝ k (ν*t.val) (D.initial k) +
      ∫ s in 0..t.val, rawHeatKernel hν k (t.val-s)
        (WeaklySingular.extendPath (Jet k) hT (D.source k) s) := by
    change forcingPath hT hν k (D.initial (k+1)) (D.source k) t = _
    rw [forcingPath_apply, hJ]
  have hi : BoundedSpatialJets.translationCLM Plane ℝ k a
      (∫ s in 0..t.val, rawHeatKernel hν k (t.val-s)
        (WeaklySingular.extendPath (Jet k) hT (D.source k) s)) =
      ∫ s in 0..t.val, rawHeatKernel hν k (t.val-s)
        (WeaklySingular.extendPath (Jet k) hT (D.source k) s) := by
    apply map_integral_eq (BoundedSpatialJets.translationCLM Plane ℝ k a)
      (rawKernel_path_integrable hT hν k (D.source k) 0 t)
    intro s
    exact (rawHeatKernel_translation hν k a (t.val-s) _).trans
      (congrArg (rawHeatKernel hν k (t.val-s)) (hg (projIcc 0 T hT s)))
  have he : BoundedSpatialJets.translationCLM Plane ℝ k a
      (PlaneHeat.evolutionOperator ℝ k (ν*t.val) (D.initial k)) =
      PlaneHeat.evolutionOperator ℝ k (ν*t.val) (D.initial k) :=
    (evolutionOperator_translation k a (ν*t.val) (D.initial k)).trans
      (congrArg (PlaneHeat.evolutionOperator ℝ k (ν*t.val)) hI)
  exact (congrArg (BoundedSpatialJets.translationCLM Plane ℝ k a) hf).trans
    (((BoundedSpatialJets.translationCLM Plane ℝ k a).map_add _ _).trans
      ((congrArg₂ (fun x y : Jet k => x+y) he hi).trans hf.symm))

/-- Periodicity is inherited by the actual compatible mild solution, not merely its data. -/
theorem solution_periodic {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T)
    (hI : ∀ k, PlanePeriodic (BoundedSpatialJets.function Plane ℝ k (D.initial k)))
    (hg : ∀ k t, PlanePeriodic (BoundedSpatialJets.function Plane ℝ k (D.source k t)))
    (hb : ∀ k i t, PlanePeriodic (BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t)))
    (t : Icc (0 : ℝ) T) : PlanePeriodic (D.solution hT hν t) := by
  intro x z
  let a : Plane := fun j => (z j : ℝ)
  have hc (i : Fin 3) (s : Icc (0 : ℝ) T) :
      BoundedSpatialJets.translationCLM Plane ℝ 0 a (D.coefficient 0 i s) = D.coefficient 0 i s :=
    BoundedSpatialJets.translation_eq_self Plane ℝ 0 a _ (fun y => hb 0 i s y z)
  have hsource (s : Icc (0 : ℝ) T) :
      BoundedSpatialJets.translationCLM Plane ℝ 0 a (D.source 0 s) = D.source 0 s :=
    BoundedSpatialJets.translation_eq_self Plane ℝ 0 a _ (fun y => hg 0 s y z)
  have hinitial : BoundedSpatialJets.translationCLM Plane ℝ 0 a (D.initial 0) = D.initial 0 :=
    BoundedSpatialJets.translation_eq_self Plane ℝ 0 a _ (fun y => hI 0 y z)
  have he := mildSolution_translation hT hν 0 a (D.coefficient 0) hc (D.affinePath hT hν 0)
    (D.affinePath_translation hT hν 0 a hinitial hsource)
  have hv := congrArg (fun u : WeaklySingular.Path (Jet 0) T =>
    BoundedSpatialJets.function Plane ℝ 0 (u t) x) he
  change BoundedSpatialJets.function Plane ℝ 0
    (BoundedSpatialJets.translationCLM Plane ℝ 0 a (D.solutionJet hT hν 0 t)) x =
    BoundedSpatialJets.function Plane ℝ 0 (D.solutionJet hT hν 0 t) x at hv
  simpa only [BoundedSpatialJets.translationCLM_apply, BoundedSpatialJets.function_translation,
    D.solutionJet_function hT hν] using hv

/-- Actual periodic field representations supply all translation-invariance hypotheses. -/
theorem solution_periodic_of_representatives {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) {w₀ : Plane → ℝ} (hpw : PlanePeriodic w₀)
    {h : ℝ × Plane → ℝ} (hph : ∀ t, PlanePeriodic (fun x => h (t,x)))
    {b : Fin 3 → ℝ × Plane → ℝ} (hpb : ∀ i t, PlanePeriodic (fun x => b i (t,x)))
    (hinit : ∀ k x, BoundedSpatialJets.function Plane ℝ k (D.initial k) x = w₀ x)
    (hsource : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (D.source k t) x = h (t.val,x))
    (hcoeff : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (D.coefficient k i t) x = b i (t.val,x))
    (t : Icc (0 : ℝ) T) : PlanePeriodic (D.solution hT hν t) := by
  apply D.solution_periodic hT hν
  · intro k x z
    rw [hinit, hinit]
    exact hpw x z
  · intro k s x z
    rw [hsource, hsource]
    exact hph s.val x z
  · intro k i s x z
    rw [hcoeff, hcoeff]
    exact hpb i s.val x z

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI
