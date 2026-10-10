import Mathlib
import OAI.Probability.Perceptron.Variational.IntegrableGibbs
import OAI.Probability.Perceptron.Cascade.EnrichedPoissonVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma tilt_log_add_bounded {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (H F : S→ℝ)
    (hH : Measurable H) (hF : Measurable F) {C : ℝ} (hC : ∀ x, |F x|≤C)
    (he : Integrable (fun x => Real.exp (H x)) μ) :
    Real.log (tiltPartition μ (fun x => H x+F x) 1)-Real.log (tiltPartition μ H 1)=
      Real.log (tiltMean μ H (fun x => Real.exp (F x)) 1) := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  have hi : Integrable (fun x => Real.exp (H x+F x)) μ := by
    apply (he.mul_const (Real.exp C)).mono' ((hH.add hF).exp.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Pi.add_apply,Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((abs_le.mp (hC x)).2)) (Real.exp_pos _).le
  have hi1 : Integrable (fun x => Real.exp (1*(H x+F x))) μ := by simpa only [one_mul] using hi
  have hp := tilt_partition_pos_of_integrable μ he1
  have hp' := tilt_partition_pos_of_integrable μ hi1
  have heq : tiltMean μ H (fun x => Real.exp (F x)) 1=
      tiltPartition μ (fun x => H x+F x) 1/tiltPartition μ H 1 := by
    simp only [tiltMean,tiltIntegral,tiltPartition,one_mul,Real.exp_add]
  rw [heq,Real.log_div hp'.ne' hp.ne']


lemma patternPrefix_fresh_preserving (N M : ℕ) :
    MeasurePreserving (fun g : ℕ→Fin N→ℝ =>
      (patternPrefix N M g,WithLp.toLp 2 (g M)))
      (infinitePatternRowsLaw N)
      ((finitePatternRowsLaw N M).prod (stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
  let ρ : Measure (Fin N→ℝ) := Measure.pi fun _ => gaussianReal 0 1
  have hfinite := measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => ρ) (Fin.last M)
  have hp := hfinite.comp (patternPrefix_measurePreserving N (M+1))
  have hrow : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→EuclideanSpace ℝ (Fin N))
      ρ (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    exact ⟨(PiLp.continuous_toLp 2 _).measurable,map_pi_eq_stdGaussian⟩
  have h := (((MeasurePreserving.id (finitePatternRowsLaw N M)).prod hrow).comp
    (Measure.measurePreserving_swap (μ := ρ) (ν := finitePatternRowsLaw N M))).comp hp
  convert h using 1
  funext g
  simp only [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply]
  apply Prod.ext
  · funext i j
    simp [Fin.init, patternPrefix]
  · rfl

lemma normalizedPatternEnergy_prefix_exact (N M : ℕ) (f : ℝ →ᵇℝ)
    (g : ℕ→Fin N→ℝ) (x : NormalizedSpin N) :
    normalizedPatternEnergy N (M+1) f (patternPrefix N (M+1) g) x=
      normalizedPatternEnergy N M f (patternPrefix N M g) x+
        f (inner ℝ x.val (WithLp.toLp 2 (g M))) := by
  unfold normalizedPatternEnergy
  rw [Fin.sum_univ_castSucc]
  congr 1

def patternExtend (N M : ℕ) (a : Fin M→Fin N→ℝ) : ℕ→Fin N→ℝ :=
  fun i => if hi : i<M then a ⟨i,hi⟩ else 0

lemma patternExtend_measurable (N M : ℕ) : Measurable (patternExtend N M) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i<M
  · simpa only [patternExtend,hi,dite_eq_left] using (measurable_pi_apply (⟨i,hi⟩ : Fin M))
  · simpa only [patternExtend, dite_eq_right hi] using (measurable_const : Measurable (fun _ : Fin M→Fin N→ℝ => (0 : Fin N→ℝ)))

lemma patternPrefix_extend (N M : ℕ) (a : Fin M→Fin N→ℝ) :
    patternPrefix N M (patternExtend N M a)=a := by
  funext i
  simp [patternPrefix,patternExtend,i.isLt]

lemma patternPrefix_fresh_integral (N M : ℕ)
    (F : (Fin M→Fin N→ℝ) × EuclideanSpace ℝ (Fin N) → ℝ) (hF : Measurable F)
    (hi : Integrable (fun a => F (patternPrefix N M a,WithLp.toLp 2 (a M))) (infinitePatternRowsLaw N)) :
    (∫ a, F (patternPrefix N M a,WithLp.toLp 2 (a M)) ∂infinitePatternRowsLaw N)=
      ∫ a, ∫ g, F (patternPrefix N M a,g) ∂stdGaussian (EuclideanSpace ℝ (Fin N))
        ∂infinitePatternRowsLaw N := by
  have hp := patternPrefix_fresh_preserving N M
  have hfi : Integrable F ((finitePatternRowsLaw N M).prod (stdGaussian (EuclideanSpace ℝ (Fin N)))) := by
    rw [← hp.map_eq]
    exact (integrable_map_measure hF.aestronglyMeasurable hp.measurable.aemeasurable).mpr hi
  have hmap := integral_map (μ := infinitePatternRowsLaw N) (φ := fun a =>
    (patternPrefix N M a,WithLp.toLp 2 (a M))) (f := F) hp.measurable.aemeasurable
    (by rw [hp.map_eq]; exact hF.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  rw [← hmap,integral_prod _ hfi]
  have hm : Measurable (fun a => ∫ g, F (a,g) ∂stdGaussian (EuclideanSpace ℝ (Fin N))) :=
    (StronglyMeasurable.integral_prod_right (f := fun a g => F (a,g)) hF.stronglyMeasurable).measurable
  have hprefix := patternPrefix_measurePreserving N M
  have hi' := integral_map (μ := infinitePatternRowsLaw N) (φ := patternPrefix N M)
    (f := fun a => ∫ g, F (a,g) ∂stdGaussian (EuclideanSpace ℝ (Fin N)))
    hprefix.measurable.aemeasurable hm.aestronglyMeasurable
  rwa [hprefix.map_eq] at hi'

lemma patternPrefix_fresh_product_integral {B : Type*} [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν] (N M : ℕ)
    (F : ((Fin M→Fin N→ℝ) × EuclideanSpace ℝ (Fin N)) × B → ℝ) (hF : Measurable F)
    (hi : Integrable (fun a => F ((patternPrefix N M a.1,WithLp.toLp 2 (a.1 M)),a.2))
      ((infinitePatternRowsLaw N).prod ν)) :
    (∫ a, F ((patternPrefix N M a.1,WithLp.toLp 2 (a.1 M)),a.2)
      ∂(infinitePatternRowsLaw N).prod ν)=
      ∫ a, ∫ g, F ((patternPrefix N M a.1,g),a.2) ∂stdGaussian (EuclideanSpace ℝ (Fin N))
        ∂(infinitePatternRowsLaw N).prod ν := by
  let R := infinitePatternRowsLaw N
  let G := stdGaussian (EuclideanSpace ℝ (Fin N))
  let T := ((finitePatternRowsLaw N M).prod G).prod ν
  have hp : MeasurePreserving (fun a : (ℕ→Fin N→ℝ) × B =>
      ((patternPrefix N M a.1,WithLp.toLp 2 (a.1 M)),a.2)) (R.prod ν) T :=
    (patternPrefix_fresh_preserving N M).prod (MeasurePreserving.id ν)
  have hfi : Integrable F T := by
    rw [← hp.map_eq]
    exact (integrable_map_measure hF.aestronglyMeasurable hp.measurable.aemeasurable).mpr hi
  have hrotate : MeasurePreserving (fun a : ((ℕ→Fin N→ℝ) × B) × EuclideanSpace ℝ (Fin N) =>
      ((a.1.1,a.2),a.1.2)) ((R.prod ν).prod G) ((R.prod G).prod ν) :=
    (measurePreserving_prodAssoc R G ν).symm.comp
      (((MeasurePreserving.id R).prod (Measure.measurePreserving_swap (μ := ν) (ν := G))).comp
        (measurePreserving_prodAssoc R ν G))
  have hq : MeasurePreserving (fun a : ((ℕ→Fin N→ℝ) × B) × EuclideanSpace ℝ (Fin N) =>
      ((patternPrefix N M a.1.1,a.2),a.1.2)) ((R.prod ν).prod G) T :=
    (((patternPrefix_measurePreserving N M).prod (MeasurePreserving.id G)).prod (MeasurePreserving.id ν)).comp hrotate
  have hiq := hq.integrable_comp_of_integrable hfi
  have hpint := integral_map (φ := fun a : (ℕ→Fin N→ℝ) × B =>
      ((patternPrefix N M a.1,WithLp.toLp 2 (a.1 M)),a.2)) (f := F)
    hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hfi.aestronglyMeasurable)
  have hqint := integral_map (φ := fun a : ((ℕ→Fin N→ℝ) × B) × EuclideanSpace ℝ (Fin N) =>
      ((patternPrefix N M a.1.1,a.2),a.1.2)) (f := F)
    hq.measurable.aemeasurable (by rw [hq.map_eq]; exact hfi.aestronglyMeasurable)
  rw [hp.map_eq] at hpint
  rw [hq.map_eq] at hqint
  rw [← hpint,hqint]
  exact integral_prod _ hiq

end SphericalPerceptronFreeEnergy
end

end OAI
