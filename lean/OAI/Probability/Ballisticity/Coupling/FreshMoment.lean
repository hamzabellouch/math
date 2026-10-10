import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetMeasurable
import OAI.Probability.Ballisticity.Estimates.CappedLoss

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma independent_random_moment_bound {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (F : A × B → ℝ≥0∞) (hF : Measurable F)
    (w : A → ℝ≥0∞) (hw : Measurable w) (c : ℝ≥0∞)
    (hbound : ∀ a, (∫⁻ b, F (a,b) ∂μ.map V)≤c) :
    (∫⁻ ω, w (U ω)*F (U ω,V ω) ∂μ) ≤ c*(∫⁻ ω, w (U ω) ∂μ) := by
  have hG : Measurable (fun p : A×B => w p.1*F p) := (hw.comp measurable_fst).mul hF
  rw [← lintegral_map hG (hU.prodMk hV),
    hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable,
    lintegral_prod _ hG.aemeasurable]
  calc
    _ ≤ ∫⁻ a, w a*c ∂μ.map U := by
      apply lintegral_mono
      intro a
      change (∫⁻ b, w a*F (a,b) ∂μ.map V)≤w a*c
      have hFa : Measurable (fun b => F (a,b)) := hF.comp measurable_prodMk_left
      rw [lintegral_const_mul (w a) hFa]
      simpa only [mul_comm] using mul_le_mul_left (hbound a) (w a)
    _ = c*(∫⁻ ω, w (U ω) ∂μ) := by
      simp_rw [mul_comm (w _) c]
      rw [lintegral_const_mul c hw,lintegral_map hw hU]

lemma fresh_rows_moment_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (F : Environment d × Environment d → ℝ≥0∞)
    (hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _ F)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞) (hbound : ∀ η, (∫⁻ ω, F (η,ω) ∂environmentLaw ν)≤c) :
    (∫⁻ ω, w ω*F (ω,ω) ∂environmentLaw ν)≤c*(∫⁻ ω, w ω ∂environmentLaw ν) := by
  have hU : @Measurable (Environment d) (Environment d) inferInstance (rowSigma S) id :=
    measurable_id.mono le_rfl (rowSigma_le S)
  have hV : @Measurable (Environment d) (Environment d) inferInstance (rowSigma T) id :=
    measurable_id.mono le_rfl (rowSigma_le T)
  have hb (η : Environment d) : (∫⁻ ω, F (η,ω) ∂
      @Measure.map (Environment d) (Environment d) inferInstance (rowSigma T) id (environmentLaw ν))≤c := by
    have hm := @lintegral_map (Environment d) (Environment d) inferInstance (rowSigma T)
      (environmentLaw ν) (fun ω => F (η,ω)) id (hF.comp measurable_prodMk_left) hV
    rw [hm]
    exact hbound η
  exact @independent_random_moment_bound (Environment d) (Environment d) (Environment d)
    inferInstance (rowSigma S) (rowSigma T) (environmentLaw ν) inferInstance
    id id hU hV
    (@indepFun_of_disjoint_rows d (Environment d) (Environment d) (rowSigma S) (rowSigma T)
      ν _ S T hST id id measurable_id measurable_id) F hF w hw c hb

lemma fresh_budget_capped_moment {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (base G : ℝ) (H : ℕ) (b a t : ℝ)
    {S T : Set (Lattice d)} (hST : Disjoint S T)
    (hstrip : ∀ x, dot (realPosition x) (realPosition (step e))=base →
      Strip (realPosition (step e)) x H ⊆ T)
    (π : Environment d → BudgetProfile (k:=k) e f base G)
    (hπ : @Measurable _ _ (rowSigma S) _ π)
    (w : Environment d → ℝ≥0∞) (hw : @Measurable _ _ (rowSigma S) _ w)
    (c : ℝ≥0∞)
    (hb : ∀ p : BudgetProfile (k:=k) e f base G,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (t*cappedLogLoss a
        (relativeBudgetMass e f H b p.val ω))) ∂environmentLaw ν)≤c) :
    (∫⁻ ω, w ω*ENNReal.ofReal (Real.exp (t*cappedLogLoss a
      (relativeBudgetMass e f H b (π ω).val ω))) ∂environmentLaw ν)≤
      c*(∫⁻ ω, w ω ∂environmentLaw ν) := by
  let F := fun p : Environment d×Environment d => ENNReal.ofReal
    (Real.exp (t*cappedLogLoss a (relativeBudgetMass e f H b (π p.1).val p.2)))
  have hQ : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _
      (fun p : Environment d×Environment d => relativeBudgetMass e f H b (π p.1).val p.2) :=
    (budgetProfileMass_joint_rows e f base G H b T (fun x hx j => hstrip (x j) (hx j))).comp
      ((hπ.comp measurable_fst).prodMk measurable_snd)
  have hF : @Measurable _ _ (MeasurableSpace.prod (rowSigma S) (rowSigma T)) _ F :=
    (Real.measurable_exp.comp ((@measurable_cappedLogLoss (Environment d×Environment d)
      (MeasurableSpace.prod (rowSigma S) (rowSigma T)) a _ hQ).const_mul t)).ennreal_ofReal
  exact fresh_rows_moment_bound ν hST F hF w hw c (fun η => hb (π η))

end DirectionalTransience

end

end OAI
