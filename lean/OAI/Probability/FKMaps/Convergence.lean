import OAI.Probability.FKMaps.MetricLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

/-- The original map observable converges under its exact marked code law. -/
theorem actual_map_tests (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
    (hI : iIndepFun (fun i ω t => B i t ω) μ)
    (F : FKCRT.MetricMeasureData → ℝ) (hF : FKCRT.IsGHPTest F) :
    Tendsto (fun n => ∫ x,FKCRT.markedMapTest (edgeScale P n) n F x ∂actualDrawLaw P n)
      atTop (𝓝 (FKCRT.brownianExpectation μ B F)) := by
  have hp := local_probability_transfer (actualHeight_CLT P hB hI)
    (fun _ => measurable_of_countable _) (fun n => FKCRT.markedMapTest (edgeScale P n) n F)
    (fun f => F (FKCRT.treeSpace f)) (metricBad P)
    (fun a ha => metricBad_limit P (hB 0) ha) (metric_test_local P F hF)
  have hh := (actualHeight_CLT P hB hI).continuous_comp hF.continuous_treeSpace
  have hy : TendstoInDistribution (fun n => FKCRT.markedMapTest (edgeScale P n) n F) atTop
      (fun ω => F (FKCRT.treeSpace (excursionPath B ω))) (actualDrawLaw P) μ := by
    apply tendstoInDistribution_of_close hh (fun _ => (measurable_of_countable _).aemeasurable)
    intro ε hε
    simpa only [Function.comp_def,Real.dist_eq,abs_sub_comm] using hp ε hε
  obtain ⟨C,hC⟩ := hF.1
  have hC0 : 0≤C := (abs_nonneg (F (FKCRT.treeSpace (0 : C(unitInterval,ℝ))))).trans (hC _)
  let clip : ℝ → ℝ := fun x => max (-C) (min C x)
  have hclip : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hclipB : ∀ x,‖clip x‖≤C := by
    intro x
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  have hclipId : ∀ x,|x|≤C → clip x=x := by
    intro x hx
    rw [abs_le] at hx
    exact max_eq_right (hx.1.trans_eq (min_eq_right hx.2).symm) |>.trans (min_eq_right hx.2)
  have hY : ∀ n x,clip (FKCRT.markedMapTest (edgeScale P n) n F x)=
      FKCRT.markedMapTest (edgeScale P n) n F x := by
    intro n x
    apply hclipId
    unfold FKCRT.markedMapTest
    split
    · exact hC _
    · simpa only [abs_zero] using hC0
  have hz : ∀ ω,clip (F (FKCRT.treeSpace (excursionPath B ω)))=F (FKCRT.treeSpace (excursionPath B ω)) :=
    fun _ => hclipId _ (hC _)
  have hi := integral_tendsto_of_tendstoInDistribution hy hclip hclipB
  simp only [hY,hz] at hi
  have he : (fun ω => F (FKCRT.treeSpace (excursionPath B ω)))=ᵐ[μ]
      (fun ω => F (FKCRT.treeSpace (FKCRT.standardExcursion B ω))) := by
    filter_upwards [excursionPath_ae_eq hB] with ω hω
    exact congrArg (fun e => F (FKCRT.treeSpace e)) hω
  simpa only [integral_congr_ae he,FKCRT.brownianExpectation] using hi

end FKCRT.Inventory
namespace FKCRT
open Inventory

/-- GHP convergence of the finite FK laws to the
standard Brownian-excursion CRT, through every positive edge count. -/
theorem finite_fk_maps_converge_to_brownian_crt : MainStatement := by
  intro q hq
  let P := Parameters.ofQ q hq
  refine ⟨crtScale P,crtScale_pos P,?_⟩
  intro Ω mΩ μ hμ B hB hI F hF
  have hh := actual_map_tests P hB hI F hF
  convert hh using 1
  ext n
  exact finiteExpectation_marked q hq (edgeScale P n) n F

end FKCRT
end

end OAI
