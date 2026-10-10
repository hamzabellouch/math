import OAI.Probability.DilutedSpin.PatternComparison
import OAI.Probability.DilutedSpin.PhysicalInsertionComparison

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open Filter
open scoped Topology BigOperators
variable {p : ℕ}

lemma logSeries_tail_tendsto (D : ℝ) :
    Tendsto (fun K : ℕ => 2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1))) atTop (𝓝 0) := by
  have hh := (tendsto_sum_nat_add (fun k : ℕ => |insertionRadius D|^(k+1)/((k:ℝ)+1))).const_mul 2
  simpa only [Nat.cast_add,mul_zero] using hh

lemma reservoirTrialLog_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |trialLog L (reservoirTrialLaw M C H N L u)
      (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)|≤D := by
  exact (trialLog_continuous_bound L _ (FiniteLaw.spinLog_continuous F) (FiniteLaw.spinLog_bound F hF)
    _ (fun i => gridExponents_pos L i.castSucc)).2 _

/-- Every uniformly bounded finite insertion has vanishing comparison error in
 the manuscript's ordered limits, on the single controlling physical sequence. -/
theorem reservoirInsertion_comparison_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L))
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hD : 0≤D) (hF : ∀ s, |F s|≤D) :
    Tendsto (fun L => limsup (fun n =>
      |reservoirInsertion M C H (Ns L n+1) L (us L n) a F-
        trialLog L (reservoirTrialLaw M C H (Ns L n+1) L (us L n))
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog F)|) atTop) atTop (𝓝 0) := by
  let f := fun k L n => qExpect (grid (L+1) 0 (L+1))
    (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  have hf (k L : ℕ) : IsBoundedUnder (·≤·) atTop (f k L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact reservoirShapeDeviation_bound _ _ _ _ _ _ _
  apply series_double_limit _ f (fun k => |insertionRadius D|^(k+1)/(k+1)*(a:ℝ))
    (fun K => 2*(∑' k : ℕ, |insertionRadius D|^(k+K+1)/(k+K+1)))
  · intros; exact abs_nonneg _
  · intro L
    refine isBoundedUnder_of_eventually_le (a := 2*D) (Eventually.of_forall (fun n => ?_))
    have h1 := reservoirInsertion_bound M C H (Ns L n+1) L (us L n) a F hF
    have h2 := reservoirTrialLog_bound M C H (Ns L n+1) L (us L n) a F hF
    exact (abs_sub _ _).trans (by linarith)
  · intro k; positivity
  · exact hf
  · exact reservoirShapeError_tendsto M hα C H Ns hNs us hcontrol
  · exact logSeries_tail_tendsto D
  · intro K L n
    simpa only [f,mul_assoc] using reservoirInsertion_comparison M C H (Ns L n+1) L
      (by omega) (us L n) a F hD hF K
end DilutedSpinGlass.UniversalDictionary

end

end OAI
