import OAI.Analysis.LipschitzHilbert.Phase.AngularCommonTranslation
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryScales

namespace OAI

/-! Measurability of the actual path and boundary masses as the common
angular-grid origin varies. The top weights are held fixed here. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

@[fun_prop] theorem measurable_index_withOrigin (g : AngularGrid) (i : ℕ) (s : ℝ) :
    Measurable (fun origin => (g.withOrigin origin).index i s) := by
  unfold index withOrigin
  fun_prop

@[fun_prop] theorem measurable_center_withOrigin (g : AngularGrid) (i : ℕ) (s : ℝ) :
    Measurable (fun origin => (g.withOrigin origin).center i ((g.withOrigin origin).index i s)) := by
  change Measurable (fun origin => origin+g.width i*((g.withOrigin origin).index i s)+g.width i/2)
  fun_prop

theorem measurable_path_mass_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (i : ℕ) (s : ℝ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).mass tops slope precision cutoff weight
      i ((g.withOrigin origin).index i s) x) := by
  simp only [mass,cellTops,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hc : MeasurableSet {origin : ℝ | (g.withOrigin origin).index i (slope t) =
      (g.withOrigin origin).index i s} :=
    measurableSet_eq_fun (g.measurable_index_withOrigin i (slope t)) (g.measurable_index_withOrigin i s)
  by_cases he : g.eligible cutoff (precision t) i
  · simp only [show ∀ origin, (g.withOrigin origin).eligible cutoff (precision t) i from fun _ => he,
      and_true]
    exact measurable_const.piecewise hc measurable_const
  · have he' : ∀ origin, ¬(g.withOrigin origin).eligible cutoff (precision t) i := fun _ => he
    simp only [he',and_false,ite_false]
    exact measurable_const

theorem measurable_boundary_mass_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (base i : ℕ) (gap s : ℝ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).boundaryMass tops slope precision cutoff weight
      base i gap s x) := by
  simp_rw [boundary_mass_eq]
  apply (g.measurable_path_mass_withOrigin tops slope precision cutoff weight i s x).add
  simp only [outsideNearTops,cellTops,Finset.filter_filter,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hbase : MeasurableSet {origin : ℝ | (g.withOrigin origin).index base (slope t) =
      (g.withOrigin origin).index base s} :=
    measurableSet_eq_fun (g.measurable_index_withOrigin base (slope t)) (g.measurable_index_withOrigin base s)
  have hparent : MeasurableSet {origin : ℝ | (g.withOrigin origin).index i (slope t) ≠
      (g.withOrigin origin).index i s} :=
    (measurableSet_eq_fun (g.measurable_index_withOrigin i (slope t)) (g.measurable_index_withOrigin i s)).compl
  have hnear : MeasurableSet {origin : ℝ | (g.withOrigin origin).neighbors (i+1) gap
      ((g.withOrigin origin).index (i+1) s) ((g.withOrigin origin).index (i+1) (slope t))} := by
    change MeasurableSet {origin : ℝ | |(g.withOrigin origin).center (i+1) ((g.withOrigin origin).index (i+1) s)-
      (g.withOrigin origin).center (i+1) ((g.withOrigin origin).index (i+1) (slope t))| < gap+g.width (i+1)}
    exact measurableSet_lt
      (continuous_abs.measurable.comp ((g.measurable_center_withOrigin (i+1) s).sub (g.measurable_center_withOrigin (i+1) (slope t))))
      measurable_const
  have hel (j : ℕ) : MeasurableSet {origin : ℝ | (g.withOrigin origin).eligible cutoff (precision t) j} := by
    change MeasurableSet {origin : ℝ | g.eligible cutoff (precision t) j}
    by_cases hh : g.eligible cutoff (precision t) j <;> simp only [hh,Set.ofPred_true,Set.ofPred_false] <;> measurability
  exact measurable_const.piecewise ((hbase.inter (hel base)).inter ((hel (i+1)).inter (hnear.inter hparent))) measurable_const

theorem measurable_source_boundary_log_loss_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (i : ℕ) (s : ℝ) (x : X) :
    Measurable (fun origin => Real.log
      ((g.withOrigin origin).sourceBoundaryMass tops slope precision cutoff weight K gap i
        ((g.withOrigin origin).index (i+1) s) x /
       (g.withOrigin origin).mass tops slope precision cutoff weight i ((g.withOrigin origin).index i s) x)) := by
  simp_rw [sourceBoundaryMass_path _ tops slope precision cutoff weight hK gap]
  exact ((g.measurable_boundary_mass_withOrigin tops slope precision cutoff weight (i+1-K) i (gap i) s x).div
    (g.measurable_path_mass_withOrigin tops slope precision cutoff weight i s x)).log

end LipschitzHilbert.AngularGrid

end

end OAI
