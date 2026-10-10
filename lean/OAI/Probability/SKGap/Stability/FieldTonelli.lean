import Mathlib
import OAI.Probability.SKGap.Stability.FieldIntegralReduction

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma fieldIntegral_indicator {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    fieldIntegral j σ J h E=∫⁻ y, ENNReal.ofReal (fieldMollifier j σ J h y)*E.indicator (fun _=>1) y := by
  rw [fieldIntegral,← lintegral_indicator hE]
  apply lintegral_congr
  intro y
  by_cases hy : y∈E <;> simp [hy]

theorem field_integral_gaussian_reduction {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) :
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=
    ∫⁻ y, ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
      conditionalFieldWeight j t σ E y := by
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let H : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p=>ENNReal.ofReal (fieldMollifier j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1))
      (fun i=>t+p.1.2 i) p.2)* E.indicator (fun _=>1) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)
  have hsJ : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1)) :=
    ((goeMatrix_pi_lipschitz (j/(n:ℝ))).continuous.comp (continuous_fst.comp continuous_fst)).add continuous_const
  have htime : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (fun i=>t+p.1.2 i)) := by
    apply continuous_pi
    intro i
    exact continuous_const.add ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1),((fun i=>t+p.1.2 i),p.2))) :=
    hsJ.prodMk (htime.prodMk continuous_snd)
  have hφ := ((continuous_fieldMollifier j σ).comp hmap).measurable.ennreal_ofReal
  have hI : Measurable (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      E.indicator (fun _=>(1 : ℝ≥0∞)) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)) := by
    apply (measurable_const.indicator hE).comp
    unfold goeMatrix
    fun_prop
  have hH : Measurable H := hφ.mul hI
  have he (g : MatrixCoordinates (Fin n) → ℝ) (x : Fin n → ℝ) :
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E}=
      ∫⁻ y,H ((g,x),y) := by
    have hs : MeasurableSet {y : Fin n → ℝ | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E} := hE.preimage (by fun_prop)
    erw [fieldIntegral_indicator _ _ _ _ _ hs]
    apply lintegral_congr
    intro y
    dsimp [H]
    by_cases hy : ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E <;> simp [hy]
  simp_rw [he]
  change (∫⁻ g,∫⁻ x,∫⁻ y,H ((g,x),y) ∂volume ∂ν ∂μ)=_
  rw [← lintegral_prod _ hH.lintegral_prod_right'.aemeasurable,
    lintegral_lintegral_swap hH.aemeasurable]
  apply lintegral_congr
  intro y
  have hh : Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ) => H (p,y)) := hH.comp (by fun_prop)
  rw [lintegral_prod _ hh.aemeasurable]
  exact field_reduction_fixed hj ht hσ E hE y
end SKGap
end
end

end OAI
