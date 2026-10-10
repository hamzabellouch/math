import OAI.Probability.SLE.Stochastic.PlanarKernelMean
import OAI.Probability.SLE.Stochastic.PlanarWienerFiltration

namespace OAI

/-! Exact Gaussian averaging for every event in the planar Wiener past. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planarWiener_set_integral_average
    (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0)
    (A : Set (Driver×Driver)) (hA : MeasurableSet[planarWienerFiltration s] A)
    (f : ℝ×ℝ → ℝ) (hf : Continuous f) (C : ℝ≥0) (hb : ∀ z, |f z|≤C) :
    (∫ b in A, f (planarWiener (s+δ) b) ∂W.prod W) =
      ∫ b in A, planarGaussianMean δ f (planarWiener s b).1 (planarWiener s b).2 ∂W.prod W := by
  classical
  let P := W.prod W
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let Z (b : Driver×Driver) : (ℝ×ℝ)×Bool := (planarWiener s b,if b∈A then true else false)
  let Y (b : Driver×Driver) := planarWiener (s+δ) b-planarWiener s b
  have hZm : Measurable[planarWienerFiltration s] Z :=
    ((Filtration.stronglyAdapted_natural (fun t =>
      (measurable_planarWiener t).stronglyMeasurable)).adapted s).prodMk
      (Measurable.ite hA measurable_const measurable_const)
  have hZ : Measurable Z := hZm.mono (planarWienerFiltration.le s) le_rfl
  have hY : Measurable Y := (measurable_planarWiener _).sub (measurable_planarWiener _)
  have hind : IndepFun Z Y P := by
    apply (IndepFun_iff_Indep _ _ _).mpr
    exact indep_of_indep_of_le (planarWiener_increment_indep_filtration W hW s δ)
      hZm.comap_le le_rfl
  let H (p : ((ℝ×ℝ)×Bool)×(ℝ×ℝ)) : ℝ := if p.1.2=true then f (p.1.1+p.2) else 0
  have hH : Measurable H := Measurable.ite
    (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const)
    (hf.measurable.comp ((measurable_fst.comp measurable_fst).add measurable_snd)) measurable_const
  have hHb (p : ((ℝ×ℝ)×Bool)×(ℝ×ℝ)) : |H p|≤C := by
    dsimp only [H]
    split_ifs
    · exact hb _
    · simp
  have hi := independent_planar_gaussian_integral Z Y hZ hY δ
    (planarWiener_increment_law W hW s δ) hind H hH C hHb
  have hG (z : ℝ×ℝ) :
      (∫ y, f (z+y) ∂(gaussianReal 0 δ).prod (gaussianReal 0 δ)) =
      planarGaussianMean δ f z.1 z.2 := by
    have hfi : Integrable (fun y : ℝ×ℝ => f (z+y))
        ((gaussianReal 0 δ).prod (gaussianReal 0 δ)) :=
      Integrable.of_bound (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable C
        (Eventually.of_forall fun y => by simpa only [Function.comp_apply,Pi.add_apply,id_eq,Real.norm_eq_abs] using hb (z+y))
    exact integral_prod_symm _ hfi
  have hleft (b : Driver×Driver) : H (Z b,Y b)=A.indicator (fun b => f (planarWiener (s+δ) b)) b := by
    by_cases ha : b∈A
    · simp only [H,Z,Y,ha,ite_true,Set.indicator_of_mem,add_sub_cancel]
    · simp [H,Z,ha]
  have hright (b : Driver×Driver) :
      (∫ y, H (Z b,y) ∂(gaussianReal 0 δ).prod (gaussianReal 0 δ)) =
        A.indicator (fun b => planarGaussianMean δ f (planarWiener s b).1 (planarWiener s b).2) b := by
    by_cases ha : b∈A
    · simpa only [H,Z,ha,ite_true,Set.indicator_of_mem] using hG (planarWiener s b)
    · simp [H,Z,ha]
  have hAm : MeasurableSet A := planarWienerFiltration.le s A hA
  simpa only [hleft,hright,integral_indicator hAm] using hi

end SLEExactGauge

end

end OAI
