import Mathlib
import OAI.Probability.SKGap.Stability.FieldTonelli
import OAI.Probability.SKGap.Localization.ConditionalIntegralRate

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma measurable_fieldIntegral {n : ℕ} (j t σ : ℝ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) :
    Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)=>
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) {y | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E}) := by
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
  have he (p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) :
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) {y | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E}=
      ∫⁻ y,H (p,y) := by
    have hs : MeasurableSet {y : Fin n → ℝ | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E} := hE.preimage (by fun_prop)
    erw [fieldIntegral_indicator _ _ _ _ _ hs]
    apply lintegral_congr
    intro y
    dsimp [H]
    by_cases hy : ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E <;> simp [hy]
  simp_rw [he]
  exact hH.lintegral_prod_right'

lemma measurableSet_badField_section {n : ℕ} (j A ε m : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    MeasurableSet {y : Field n | (W,y)∈badFieldSet n j A ε m} := by
  have hm : Measurable (fun z : Fin n → ℝ=>((fun q : Fin n × Fin n=>W q.1 q.2),z)) :=
    measurable_const.prodMk measurable_id
  have hs := (measurableSet_badFieldFlat n j A ε m).preimage hm
  convert hs using 1
  ext y
  rfl

lemma measurable_fieldIntegral_cylinder {n : ℕ} (j t σ : ℝ)
    (E : Set (Field n)) (hE : MeasurableSet E) :
    Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)=>
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) E) := by
  simpa only [mem_prod,mem_univ,true_and,ofPred_mem_eq] using
    measurable_fieldIntegral j t σ (Set.univ ×ˢ E) (MeasurableSet.univ.prod hE)

lemma measureReal_union_detector {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E D : Set Ω) (F : Ω → ℝ≥0∞)
    (b p q : ℝ) (hbD : μ.real D ≤ p)
    (hbF : μ.real {x | ENNReal.ofReal b ≤ F x} ≤ q)
    (hdet : ∀ x ∈ E, x∉D → ENNReal.ofReal b ≤ F x) : μ.real E ≤ p+q := by
  apply (measureReal_mono (s₂ := D ∪ {x | ENNReal.ofReal b ≤ F x}) ?_ (measure_ne_top _ _)).trans
  · exact (measureReal_union_le _ _).trans (add_le_add hbD hbF)
  · intro x hx
    by_cases hd : x∈D
    · exact Or.inl hd
    · exact Or.inr (hdet x hx hd)

lemma markov_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F : Ω → ℝ≥0∞} (hF : Measurable F) {a b d : ℝ}
    (hb : ∫⁻ x,F x ∂μ ≤ ENNReal.ofReal (exp (-a*d))) :
    μ.real {x | ENNReal.ofReal (exp (-b*d)) ≤ F x} ≤ exp (-(a-b)*d) := by
  have hm := meas_ge_le_lintegral_div (μ := μ) (ε := ENNReal.ofReal (exp (-b*d))) hF.aemeasurable
    (ENNReal.ofReal_pos.mpr (exp_pos _)).ne' ENNReal.ofReal_ne_top
  have he : ENNReal.ofReal (exp (-a*d))/ENNReal.ofReal (exp (-b*d))=
      ENNReal.ofReal (exp (-(a-b)*d)) := by
    rw [← ENNReal.ofReal_div_of_pos (exp_pos _),← exp_sub]
    congr 2
    ring
  have hx := hm.trans ((ENNReal.div_le_div_right hb _).trans_eq he)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq (ENNReal.toReal_ofReal (exp_pos _).le)
end SKGap
end
end

end OAI
