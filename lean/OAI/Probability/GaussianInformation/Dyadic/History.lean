import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.TranscriptLaw

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace RepeatedLocalization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
lemma history_analysis_realized {n N t : ℕ} (hn : 0 < n) (rules : Rules n N t)
    (L : ℝ) (hcost : UniformBlockCost n N L) :
    ∃ s : AnalysisState n, ∃ f : s.Index → History N t,
      s.channel.coarsen f = historyChannel rules ∧
      s.potential ≤ (t:ℝ)*(L+2*Real.log 2+1) ∧ Nonempty (Realization s f) := by
  classical
  have := cubePrior_isProbabilityMeasure hn
  induction t with
  | zero =>
    refine ⟨initialState hn,(fun _ => Fin.elim0),?_,?_,⟨initialRealization hn⟩⟩
    · apply FiniteChannel.ext_prob
      funext w z
      have hw : (Fin.elim0 : History N 0) = w := Subsingleton.elim _ _
      simp only [initialState,FiniteChannel.coarsen,historyChannel,historyLikelihood,hw,
        Finset.prod_empty,Finset.univ_eq_empty,Finset.sum_const]
      norm_num [Finset.card_univ,Fintype.card_unique]
      change @Fintype.card Unit _ = 1
      exact Fintype.card_unique
    · rw [initialState_potential]; simp
  | succ t ih =>
    obtain ⟨s,f,hf,hs,⟨R⟩⟩ := ih (initRules rules)
    let r := fun w : History N t => blockChannel (rules (Fin.last t) w)
    let q := fun i : s.Index => r (f i)
    have H (i : s.Index) (hi : 0 < scoreMass (cubePrior n) (s.channel.prob i)) :
        finiteInformation (scorePosterior (cubePrior n) (s.channel.prob i)) (q i).prob ≤
          L+Real.log (s.B i) := by
      have hp := scorePosterior_probability (cubePrior n) _ (s.channel.measurable i)
        (s.channel.nonneg i) (s.channel.le_one i) hi
      exact hcost _ hp _ _ (s.support i hi) (s.B_one i) (s.spread i hi) (rules (Fin.last t) (f i))
    obtain ⟨s',g,hg,hs',⟨E⟩⟩ := analysis_extension_realized hn s q L H
    let F : s.Index × Fin N → History N t × Fin N := fun i => (f i.1,i.2)
    let f' := appendHistoryEquiv N t ∘ F ∘ g
    refine ⟨s',f',?_,?_,⟨extendRealization R E⟩⟩
    · apply FiniteChannel.ext_prob
      have hg' := FiniteChannel.ext_prob hg
      have hmap : (s.channel.bind q).coarsen F = (s.channel.coarsen f).bind r :=
        FiniteChannel.ext_prob (s.channel.coarsen_bind_map f r)
      calc
        (s'.channel.coarsen f').prob =
            (((s'.channel.coarsen g).coarsen F).coarsen (appendHistoryEquiv N t)).prob := by
          rw [FiniteChannel.coarsen_comp,FiniteChannel.coarsen_comp]
          rfl
        _ = (((historyChannel (initRules rules)).bind r).coarsen (appendHistoryEquiv N t)).prob := by
          rw [hg',hmap,hf]
        _ = (historyChannel rules).prob := historyChannel_succ rules
    · rw [Nat.cast_succ]
      linarith

end RepeatedLocalization

end OAI
