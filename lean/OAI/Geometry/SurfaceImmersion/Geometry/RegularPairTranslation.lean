import OAI.Geometry.SurfaceImmersion.Atlas.PairChartSard

namespace OAI

/-! Arbitrarily small translations make two smooth surface patches
transverse at every coincidence. This is the local perturbation used in
the finite global double-locus regularization. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_regular_pair_translation {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (U V : Set Base) (hU : IsOpen U) (hV : IsOpen V)
    (A : Set (ProjectionTarget 3)) (hA : IsOpen A) (hAn : A.Nonempty) :
    ∃ a ∈ A, ∀ x ∈ U, ∀ y ∈ V, f x-g y = a →
      Function.Surjective (fderiv ℝ (fun z : Base × Base => f z.1-g z.2) (x,y)) := by
  let h : Base × Base → ProjectionTarget 3 := fun z => f z.1-g z.2
  let B := h '' {z | z ∈ U ×ˢ V ∧ ¬ Function.Surjective (fderiv ℝ h z)}
  have hh : ContDiff ℝ ∞ h := (hf.comp contDiff_fst).sub (hg.comp contDiff_snd)
  have hnull : volume B = 0 := pair_chart_local_critical_values_null (hU.prod hV) hh.contDiffOn
  have hae : ∀ᵐ a ∂volume, a ∉ B := by
    simp only [ae_iff,not_not]
    exact hnull
  obtain ⟨a,haA,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty A hA hAn
  refine ⟨a,haA,?_⟩
  intro x hx y hy he
  by_contra hn
  exact ha ⟨(x,y),⟨⟨hx,hy⟩,hn⟩,he⟩

theorem exists_small_transverse_translation {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (U V : Set Base) (hU : IsOpen U) (hV : IsOpen V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ProjectionTarget 3, ‖a‖ < ε ∧
      ∀ x ∈ U, ∀ y ∈ V, f x+a = g y →
        Function.Surjective (fderiv ℝ (fun z : Base × Base => f z.1-g z.2) (x,y)) := by
  obtain ⟨a,ha,hreg⟩ := exists_regular_pair_translation hf hg U V hU hV
    (Metric.ball 0 ε) Metric.isOpen_ball ⟨0,Metric.mem_ball_self hε⟩
  refine ⟨-a,?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using ha
  · intro x hx y hy he
    apply hreg x hx y hy
    apply sub_eq_iff_eq_add.mpr
    calc
      f x = (f x + -a) + a := by abel
      _ = g y + a := by rw [he]
      _ = a + g y := add_comm _ _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
