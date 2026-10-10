import Mathlib
import OAI.Probability.LogConcave.Numerics.ChildNoise

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical BigOperators

variable {d : ℕ}

lemma gaussian_pair_sum_law (a b s : ℝ) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => a • z.1+b • z.2)=
      (stdGaussian (Point d)).map (fun z => s • z) := by
  have h := MeanTree.weighted_gaussian_law (E:=Point d) ![a,b] s (by simpa using hs)
  rw [←(measurePreserving_finTwoArrow (stdGaussian (Point d))).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin 2 => stdGaussian (Point d))).map
    (fun z => a • z 0+b • z 1)=_
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

lemma gaussian_pair_shift_law (m : Point d) (a b s : ℝ) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => (m+a • z.1)+b • z.2)=
      (stdGaussian (Point d)).map (fun z => m+s • z) := by
  have h := congrArg (Measure.map (fun z => m+z)) (gaussian_pair_sum_law (d:=d) a b s hs)
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [comp_def,add_assoc] using h

lemma law_add_gaussian {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (u : X → Point d) (hu : Measurable u)
    (m : Point d) (a b s : ℝ) (hs : a^2+b^2=s^2)
    (hlaw : μ.map u=(stdGaussian (Point d)).map (fun z => m+a • z)) :
    (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+b • z.2)=
      (stdGaussian (Point d)).map (fun z => m+s • z) := by
  have h := congrArg (fun η : Measure (Point d) =>
    (η.prod (stdGaussian (Point d))).map (fun z => z.1+b • z.2)) hlaw
  have left : (μ.map u).prod (stdGaussian (Point d))=
      (μ.prod (stdGaussian (Point d))).map (Prod.map u id) := by
    rw [←Measure.map_prod_map _ _ hu measurable_id,Measure.map_id]
  have right : ((stdGaussian (Point d)).map (fun z => m+a • z)).prod (stdGaussian (Point d))=
      ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
        (Prod.map (fun z => m+a • z) id) := by
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
  rw [left,right,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h.trans (gaussian_pair_shift_law m a b s hs)

lemma smoothing_add_gaussian {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]
    (μ : Measure X) [IsProbabilityMeasure μ] (θ : Measure W) [IsProbabilityMeasure θ]
    (u : X → Point d) (f : W → Point d) (hu : Measurable u) (hf : Measurable f)
    (a b s : ℝ) (hs : a^2+b^2=s^2)
    (hlaw : μ.map u=(θ.prod (stdGaussian (Point d))).map (fun z => f z.1+a • z.2)) :
    (μ.prod (stdGaussian (Point d))).map (fun z => u z.1+b • z.2)=
      (θ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2) := by
  let γ := stdGaussian (Point d)
  have h := congrArg (fun η : Measure (Point d) => (η.prod γ).map (fun z => z.1+b • z.2)) hlaw
  have hl : (μ.map u).prod γ=(μ.prod γ).map (Prod.map u id) := by
    rw [←Measure.map_prod_map _ _ hu measurable_id,Measure.map_id]
  have hr : ((θ.prod γ).map (fun z => f z.1+a • z.2)).prod γ=
      ((θ.prod γ).prod γ).map (Prod.map (fun z => f z.1+a • z.2) id) := by
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
  rw [hl,hr,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  apply h.trans
  have hassoc := (measurePreserving_prodAssoc θ γ γ).map_eq
  have hsum : (θ.prod (γ.prod γ)).map
      (fun z => (z.1,a • z.2.1+b • z.2.2))=
      θ.prod (γ.map (fun z => s • z)) := by
    rw [show (fun z : W × (Point d × Point d) => (z.1,a • z.2.1+b • z.2.2))=
      Prod.map id (fun z => a • z.1+b • z.2) from rfl]
    rw [←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id]
    rw [gaussian_pair_sum_law a b s hs]
  have hsum' := congrArg (Measure.map (fun z : W × Point d => f z.1+z.2)) hsum
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hsum'
  have he := congrArg (Measure.map (fun z : W × (Point d × Point d) =>
    f z.1+(a • z.2.1+b • z.2.2))) hassoc
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
  have hfinal : (θ.prod (γ.map (fun z => s • z))).map (fun z => f z.1+z.2)=
      (θ.prod γ).map (fun z => f z.1+s • z.2) := by
    rw [show θ.prod (γ.map (fun z => s • z))=(θ.prod γ).map
      (Prod.map id (fun z => s • z)) by
        rw [←Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id]]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hh := he.trans (hsum'.trans hfinal)
  change ((θ.prod γ).prod γ).map (fun z => f z.1.1+(a • z.1.2+b • z.2))=_ at hh
  change ((θ.prod γ).prod γ).map (fun z => (f z.1.1+a • z.1.2)+b • z.2)=_
  simpa only [add_assoc] using hh
end LogConcaveSampling

end

end

end OAI
