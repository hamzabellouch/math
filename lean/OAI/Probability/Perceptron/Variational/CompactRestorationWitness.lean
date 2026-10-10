import Mathlib
import OAI.Probability.Perceptron.Variational.LabelPairTestValue

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

abbrev WeightedRestorationRange (f : ℝ →ᵇ ℝ) (C : ℝ) := Icc (-C) C × RestorationRange f

def compactWeightedLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (C : ℝ)
    (A : Ω→ℝ) (hA : Measurable A) (Z : Ω→RestorationRange f) (hZ : Measurable Z)
    (hb : ∀ x, |A x|≤C) : ProbabilityMeasure (WeightedRestorationRange f C) :=
  ⟨μ.map (fun x => (⟨A x,abs_le.mp (hb x)⟩,Z x)),
    (Measure.isProbabilityMeasure_map_iff ((hA.subtype_mk).prodMk hZ).aemeasurable).2 inferInstance⟩

lemma compactWeightedLaw_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (C : ℝ)
    (A : Ω→ℝ) (hA : Measurable A) (Z : Ω→RestorationRange f) (hZ : Measurable Z)
    (hb : ∀ x, |A x|≤C) (J : WeightedRestorationRange f C → ℝ) (hJ : Measurable J) :
    (∫ x, J x ∂(compactWeightedLaw μ f C A hA Z hZ hb : Measure _))=
      ∫ x, J (⟨A x,abs_le.mp (hb x)⟩,Z x) ∂μ :=
  integral_map ((hA.subtype_mk).prodMk hZ).aemeasurable hJ.aestronglyMeasurable

lemma compactWeighted_witness {Ω : ℕ→Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ)→Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : ℝ →ᵇ ℝ) (C : ℝ) (A : (n : ℕ)→Ω n→ℝ) (Z : (n : ℕ)→Ω n→RestorationRange f)
    (hA : ∀ n, Measurable (A n)) (hZ : ∀ n, Measurable (Z n)) (hb : ∀ n x, |A n x|≤C)
    (b : ℕ→ℝ) (hm : ∀ j, Tendsto (fun n => ∫ x, A n x*(Z n x).val^j ∂μ n) atTop (𝓝 (b j)))
    (J : C(RestorationRange f,ℝ)) (L : ℝ)
    (hL : Tendsto (fun n => ∫ x, A n x*J (Z n x) ∂μ n) atTop (𝓝 L)) :
    ∃ η : ProbabilityMeasure (WeightedRestorationRange f C),
      (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange f C)))=b j) ∧
      (∫ x, x.1.val*J x.2 ∂(η : Measure (WeightedRestorationRange f C)))=L := by
  let ν n := compactWeightedLaw (μ n) f C (A n) (hA n) (Z n) (hZ n) (hb n)
  obtain ⟨η,-,s,hs,hlim⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (ν n))
  have ht (G : C(WeightedRestorationRange f C,ℝ)) :
      Tendsto (fun n => ∫ x, G x ∂(ν (s n) : Measure (WeightedRestorationRange f C))) atTop (𝓝 (∫ x, G x ∂(η : Measure (WeightedRestorationRange f C)))) := by
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact G)).continuousAt.tendsto.comp hlim
  refine ⟨η,?_,?_⟩
  · intro j
    let G : C(WeightedRestorationRange f C,ℝ) := ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    have hh := ht G
    simp only [ν,compactWeightedLaw_integral _ _ _ _ _ _ _ _ _ G.continuous.measurable] at hh
    exact tendsto_nhds_unique hh ((hm j).comp hs.tendsto_atTop)
  · let G : C(WeightedRestorationRange f C,ℝ) := ⟨fun x => x.1.val*J x.2,
      (continuous_subtype_val.comp continuous_fst).mul (J.continuous.comp continuous_snd)⟩
    have hh := ht G
    simp only [ν,compactWeightedLaw_integral _ _ _ _ _ _ _ _ _ G.continuous.measurable] at hh
    exact tendsto_nhds_unique hh (hL.comp hs.tendsto_atTop)

def pairRestorationBound (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) : ℝ :=
  ‖F‖*(∏ _ : Fin 2, ‖expBCF 1 f*v‖)*(∏ _ : Fin 2, ‖expBCF 1 f*w‖)
lemma pairRestorationBound_nonneg (f v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) :
    0≤pairRestorationBound f v w F := by unfold pairRestorationBound; positivity

lemma sourceLabelRestorationNumerator_pair_bound (n k : ℕ) (f ψ v w : ℝ →ᵇ ℝ)
    (F : CompactOverlap →ᵇ ℝ) (q : Fin (k+1)→Time) (s : ℝ≥0)
    (p e : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (a) :
    |sourceLabelRestorationNumerator n k 2 (fun i => (q i:ℝ)) s f ψ
      (fun _ => v) (fun _ => w) (labelProfilePairTest q F) p e h u a|≤pairRestorationBound ψ v w F := by
  apply (sourceLabelRestorationNumerator_bound n k 2 _ s f ψ (fun _ => v) (fun _ => w)
    (labelProfilePairTest q F) p e h u a).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  exact F.norm_compContinuous_le _

lemma sourceLabelPair_witness (k : ℕ) (q : Fin (k+1)→Time) (hq : Monotone q)
    (f : ℝ →ᵇ ℝ) (g : Jet3) (v w : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ)
    (p e : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i,0≤h n i) (hh : ∀ n,Monotone (h n)) (u : (n : ℕ)→Fin (n+1)→ℝ)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (t : ℕ→ℝ≥0) (s : ℕ→ℕ) {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (e (s n)) (h (s n))
      (u (s n)) z (t (s n))) atTop (𝓝 ν)) :
    ∃ η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v w F)),
      (∀ j, (∫ x, x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v w F))))=
        ∫ Q, labelRestorationBlockMoment (fun i => (q i:ℝ)) g.f (fun _ => v) (fun _ => w)
          (labelProfilePairTest q F) j (compactBlock (2+j) Q) ∂ν) ∧
      (∫ x, x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v w F))))=
        ∑ d, F (timeSpin (q d))*(twoVisitMass k z d).toReal*
          (labelPairCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v d *
           labelPairCoefficient k z (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) w d) := by
  let τ : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩
  apply compactWeighted_witness
    (fun n => ((sourceBaseDataLaw (s n) k z (t (s n))).prod countableGaussianLaw).prod (countableGaussianLaw.prod countableGaussianLaw))
    g.f (pairRestorationBound g.f v w F)
    (fun n => sourceLabelRestorationNumerator (s n) k 2 (fun i => (q i:ℝ)) τ f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) (p (s n)) (e (s n)) (h (s n)) (u (s n)))
    (fun n => sourceLabelRestorationDenominator (s n) k (fun i => (q i:ℝ)) τ f g.f
      (p (s n)) (e (s n)) (h (s n)) (u (s n)))
    (fun n => sourceLabelRestorationNumerator_measurable ..)
    (fun n => sourceLabelRestorationDenominator_measurable ..)
    (fun n a => sourceLabelRestorationNumerator_pair_bound ..) _ ?_ (restorationReciprocal g.f 2) _ ?_
  · intro j
    simp_rw [sourceLabelRestorationPolynomial _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hh0 _) (hh _) j]
    exact sourceLabelRestorationMoment_tendsto k 2 (fun i => (q i:ℝ)) (q 0).prop.1
      (fun i l hil => hq hil) (q (Fin.last k)).prop.2 f g.f (fun _ => v) (fun _ => w)
      (labelProfilePairTest q F) p e h hh0 hh u z t s hlim j
  · change Tendsto (fun n => sourceLabelRestorationRatio (s n) k 2 (fun i => (q i:ℝ)) τ f g.f
      (fun _ => v) (fun _ => w) (labelProfilePairTest q F) (p (s n)) (e (s n)) (h (s n)) (u (s n)) z (t (s n))) atTop _
    simp_rw [sourceLabelRestorationRatio_pair_value _ k f g _ _ _ (hh0 _) (hh _) _ q τ v w F z hz hz0 hz1]
    exact tendsto_const_nhds

lemma labelPairCoefficient_one (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (d : Fin (k+1)) :
    labelPairCoefficient k z q g s 1 d=1 := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  simp only [labelPairCoefficient,labelResidualObservable,residualResponse_one]
  exact rootPathCorrelation_one _ _ k _ hκ d

def labelSingleCoefficient (k : ℕ) (z : Fin k→ℝ) (q : Fin (k+1)→ℝ)
    (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) : ℝ :=
  rootPathMean (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) k
    (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
      (gaussianLinearMarkStep (labelGaussianStep q)) (z i)
      (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
        (gaussianLinearMarkStep (labelGaussianStep q)) k z (fun x => labelProfileTerminal g s (x 0)) i))
    (fun x => labelResidualObservable s g.f v (x 0))

lemma labelPairCoefficient_bounds (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) :
    (∀ d,0≤labelPairCoefficient k z q g s v d) ∧
    Monotone (labelPairCoefficient k z q g s v) ∧
    (∀ d, labelPairCoefficient k z q g s v d≤labelSingleCoefficient k z q g s (v*v)) ∧
    labelSingleCoefficient k z q g s (v*v)≤‖v‖^2 := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  exact residual_path_pair_coefficients (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) (by fun_prop) k _ hκ
    (fun x => labelEvaluation (x 0)) (by unfold labelEvaluation; fun_prop) s g.f v

end SphericalPerceptronFreeEnergy
end

end OAI
