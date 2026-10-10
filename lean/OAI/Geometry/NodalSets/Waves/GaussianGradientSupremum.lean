import OAI.Geometry.NodalSets.Charts.MetricFrequencyBounds
import OAI.Geometry.NodalSets.Waves.GaussianCompactSections

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

def vectorMeanSection (M : Fin 4 → C(X,ℝ)) : C(X,EuclideanSpace ℝ (Fin 4)) :=
  ⟨fun x ↦ WithLp.toLp 2 (fun j ↦ M j x),
    (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp (continuous_pi (fun j ↦ (M j).continuous))⟩

def vectorCoeffSection (Z : Fin 4 → ι → C(X,ℂ)) (p : ι × Fin 2) :
    C(X,EuclideanSpace ℝ (Fin 4)) :=
  vectorMeanSection (fun j ↦ if p.2 = 0 then
    ⟨fun x ↦ (Z j p.1 x).re, Complex.continuous_re.comp (Z j p.1).continuous⟩ else
    ⟨fun x ↦ -(Z j p.1 x).im, (Complex.continuous_im.comp (Z j p.1).continuous).neg⟩)

def pairVectorSection (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ))
    (a : ι × Fin 2 → ℝ) : C(X,EuclideanSpace ℝ (Fin 4)) :=
  vectorMeanSection M + ∑ p : ι × Fin 2, a p • vectorCoeffSection Z p

lemma pairVectorSection_apply (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ))
    (a : ι × Fin 2 → ℝ) (x : X) (j : Fin 4) :
    pairVectorSection M Z a x j = M j x+pairLinearSum (fun i ↦ Z j i x) a := by
  classical
  simp only [pairVectorSection,ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,PiLp.add_apply,
    vectorMeanSection,ContinuousMap.coe_mk,pairLinearSum,vectorCoeffSection]
  congr 1
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp [smul_eq_mul,mul_comm]

lemma pairVectorSection_continuous (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ)) :
    Continuous (pairVectorSection M Z) := by
  unfold pairVectorSection
  exact continuous_const.add (continuous_finsetSum _ (fun p _ ↦
    (continuous_apply p).smul continuous_const))

variable [CompactSpace X]

lemma pairVectorSection_integrable (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ)) :
    Integrable (pairVectorSection M Z) gaussianPairs := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  unfold pairVectorSection
  apply (integrable_const (μ := gaussianPairs (ι := ι)) (vectorMeanSection M)).add
  apply integrable_finsetSum
  intro p _
  exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
    (i := p) IsGaussian.integrable_id).smul_const _

variable (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (K : Set Coord) [CompactSpace K]

def gaussianGradientSection (a : ι × Fin 2 → ℝ) : C(K,EuclideanSpace ℝ (Fin 4)) :=
  pairVectorSection (fun j ↦ derivativeSection seed hs K 1 (fun _ ↦ Pi.single j 1))
    (fun j i ↦ derivativeSection (V i) (hV i) K 1 (fun _ ↦ Pi.single j 1)) a

omit [CompactSpace K] in
lemma gaussianGradientSection_apply (a : ι × Fin 2 → ℝ) (x : K) (j : Fin 4) :
    gaussianGradientSection V seed hV hs K a x j =
      fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x (Pi.single j 1) := by
  rw [gaussianGradientSection,pairVectorSection_apply]
  have hh := seeded_gaussian_iterated_apply V seed hV hs a 1 x (fun _ ↦ Pi.single j 1)
  simpa only [derivativeSection,ContinuousMap.coe_mk,iteratedFDeriv_one_apply] using hh.symm

def gaussianGradientSup (a : ι × Fin 2 → ℝ) : ℝ :=
  ‖gaussianGradientSection V seed hV hs K a‖

lemma gaussianGradientSup_continuous : Continuous (gaussianGradientSup V seed hV hs K) :=
  (pairVectorSection_continuous _ _).norm

lemma gaussianGradientSup_integrable : Integrable (gaussianGradientSup V seed hV hs K) gaussianPairs :=
  (pairVectorSection_integrable _ _).norm

lemma gaussianGradientSup_le_iff (a : ι × Fin 2 → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    gaussianGradientSup V seed hV hs K a ≤ C ↔
      ∀ x ∈ K, sourceEuclideanNorm (fun j ↦
        fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x (Pi.single j 1)) ≤ C := by
  unfold gaussianGradientSup
  rw [ContinuousMap.norm_le _ hC]
  have he (x : K) : ‖gaussianGradientSection V seed hV hs K a x‖ =
      sourceEuclideanNorm (fun j ↦
        fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x (Pi.single j 1)) := by
    rw [EuclideanSpace.norm_eq]
    simp only [gaussianGradientSection_apply,Real.norm_eq_abs,sq_abs,sourceEuclideanNorm]
  simp_rw [he]
  exact Subtype.forall

end
end Yau.Geometry

end OAI
