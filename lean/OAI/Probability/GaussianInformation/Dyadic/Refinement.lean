import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.StateInformation

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

structure ExtensionWitness {n N : ℕ} (s : AnalysisState n)
    (q : s.Index → FiniteChannel (Coordinate n) (Fin N))
    (s' : AnalysisState n) (f : s'.Index → s.Index × Fin N) where
  choose : (s.Index × Fin N) → Coordinate n → s'.Index
  choose_fiber : ∀ i j, MeasurableSet {z | choose i z = j}
  erase_choose : ∀ i z, f (choose i z) = i
  chosen : ∀ j z, 0 < s'.channel.prob j z → choose (f j) z = j
  positive_parent : ∀ j z, 0 < s'.channel.prob j z → 0 < s.channel.prob (f j).1 z
  contains : ∀ i z, z ∈ cellSet (s.cell i.1) → z ∈ cellSet (s'.cell (choose i z))
  subset : ∀ j, cellSet (s'.cell j) ⊆ cellSet (s.cell (f j).1)

lemma analysis_extension_realized {n N : ℕ} (hn : 0 < n) (s : AnalysisState n)
    (q : s.Index → FiniteChannel (Coordinate n) (Fin N)) (L : ℝ)
    (hcost : ∀ i,0 < scoreMass (cubePrior n) (s.channel.prob i) →
      finiteInformation (scorePosterior (cubePrior n) (s.channel.prob i)) (q i).prob ≤ L+Real.log (s.B i)) :
    ∃ s' : AnalysisState n, ∃ f : s'.Index → (s.Index × Fin N),
      (s'.channel.coarsen f).prob = (s.channel.bind q).prob ∧
      s'.potential ≤ s.potential+L+2*Real.log 2+1 ∧ Nonempty (ExtensionWitness s q s' f) := by
  classical
  let μ := cubePrior n
  have := cubePrior_isProbabilityMeasure hn
  let r := s.channel.bind q
  have hparentsupport (i : s.Index × Fin N) (hi : 0 < scoreMass μ (r.prob i)) :
      scorePosterior μ (r.prob i) (cellSet (s.cell i.1)) = 1 := by
    have hP := s.channel.bind_positive_parent q μ i hi
    have := scorePosterior_probability μ _ (r.measurable i) (r.nonneg i) (r.le_one i) hi
    have := scorePosterior_probability μ _ (s.channel.measurable i.1) (s.channel.nonneg i.1) (s.channel.le_one i.1) hP
    have hz := (scorePosterior_null_iff μ _ (s.channel.measurable i.1) (s.channel.nonneg i.1) hP
      _ (measurableSet_cellSet (s.cell i.1)).compl).mp
        ((prob_compl_eq_zero_iff (measurableSet_cellSet (s.cell i.1))).mpr (s.support i.1 hP))
    apply (prob_compl_eq_zero_iff (measurableSet_cellSet (s.cell i.1))).mp
    apply (scorePosterior_null_iff μ _ (r.measurable i) (r.nonneg i) hi _
      (measurableSet_cellSet (s.cell i.1)).compl).mpr
    filter_upwards [hz] with x hx
    intro hnot
    change s.channel.prob i.1 x*(q i.1).prob i.2 x = 0
    rw [hx hnot,zero_mul]
  have hex (i : s.Index × Fin N) : Nonempty (HeavyRefinement n (scorePosterior μ (r.prob i)) (s.cell i.1)) := by
    by_cases h : 0 < scoreMass μ (r.prob i)
    · have := scorePosterior_probability μ _ (r.measurable i) (r.nonneg i) (r.le_one i) h
      exact exists_heavy_refinement hn (scorePosterior μ (r.prob i)) (s.cell i.1) (hparentsupport i h)
        (div_nonneg zero_le_one h.le) (posterior_cube_domination hn r i h)
    · have hz : scoreMass μ (r.prob i) = 0 := le_antisymm (le_of_not_gt h) (scoreMass_nonneg μ _ (r.nonneg i))
      rw [scorePosterior_of_mass_zero μ _ hz]
      exact zero_heavy_refinement n (s.cell i.1)
  let R := fun i => Classical.choice (hex i)
  let a := r.dbind (fun i => (R i).channel)
  have hpost (i : Sigma (fun i => (R i).Index)) (hi : 0 < scoreMass μ (a.prob i)) :
      scorePosterior μ (a.prob i) = scorePosterior (scorePosterior μ (r.prob i.1)) ((R i.1).channel.prob i.2) :=
    (scorePosterior_assoc μ _ _ (r.measurable i.1) ((R i.1).channel.measurable i.2)
      (r.nonneg i.1) ((R i.1).channel.nonneg i.2)
      (r.dbind_positive_parent _ μ i hi) (r.dbind_positive_conditional _ μ i hi)).symm
  let s' : AnalysisState n := {
    Index := Sigma (fun i => (R i).Index)
    channel := a
    cell := fun i => (R i.1).cell i.2
    B := fun i => (R i.1).B i.2
    B_one := fun i => (R i.1).B_one i.2
    support := fun i hi => by
      rw [hpost i hi]
      exact (R i.1).support i.2 (r.dbind_positive_conditional _ μ i hi)
    spread := fun i hi => by
      rw [hpost i hi]
      exact (R i.1).spread i.2 (r.dbind_positive_conditional _ μ i hi) }
  refine ⟨s',Sigma.fst,?_,?_,?_⟩
  · exact r.coarsen_dbind_fst (fun i => (R i).channel)
  ·
    let δ := fun i j => (((R i).cell j).1-(s.cell i.1).1:ℕ)
    let D := r.expectation μ (fun i => (R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => δ i j))
    have hdepth : s'.depth = s.depth+D := by
      have he : (fun i : Sigma (fun i => (R i).Index) => (((R i.1).cell i.2).1:ℝ)) =
          fun i => ((s.cell i.1.1).1:ℝ)+(δ i.1 i.2:ℝ) := by
        funext i
        dsimp only [δ]
        rw [Nat.cast_sub ((R i.1).level_ge i.2)]
        ring
      change a.expectation μ _ = s.depth+D
      rw [he,FiniteChannel.expectation_add]
      change (r.dbind (fun i => (R i).channel)).expectation μ _ +
        (r.dbind (fun i => (R i).channel)).expectation μ _ = _
      rw [r.expectation_dbind_fst (fun i => (R i).channel) μ (fun i => ((s.cell i.1).1:ℝ)),
        r.expectation_dbind (fun i => (R i).channel) μ]
      change r.expectation μ (fun i => ((s.cell i.1).1:ℝ))+D = s.depth+D
      change (s.channel.bind q).expectation μ (fun i => ((s.cell i.1).1:ℝ))+D = s.depth+D
      rw [s.channel.expectation_bind_fst q μ (fun i => ((s.cell i).1:ℝ))]
      rfl
    have href (i : s.Index × Fin N) :
        finiteInformation (scorePosterior μ (r.prob i)) (R i).channel.prob+
          (R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => Real.log ((R i).B j)) ≤
        ((n:ℝ)/2+2)*Real.log 2*((R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => δ i j))+2*Real.log 2+1 := by
      have h1 := (R i).entropy_bound
      have h2 := (R i).concentration_bound
      change _ ≤ _ at h1
      change _ ≤ _ at h2
      dsimp only [FiniteChannel.expectation,δ]
      linarith
    have hrefsum := r.expectation_mono μ href
    rw [r.expectation_add μ] at hrefsum
    have hright : r.expectation μ (fun i =>
        ((n:ℝ)/2+2)*Real.log 2*((R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => δ i j))+2*Real.log 2+1) =
        ((n:ℝ)/2+2)*Real.log 2*D+2*Real.log 2+1 := by
      rw [r.expectation_add μ,r.expectation_add μ,r.expectation_const_mul μ,r.expectation_const μ,r.expectation_const μ]
    rw [hright] at hrefsum
    have hinfo : s'.information = finiteInformation μ r.prob+
        r.expectation μ (fun i => finiteInformation (scorePosterior μ (r.prob i)) (R i).channel.prob) :=
      r.information_dbind (fun i => (R i).channel) μ
    have hconc : s'.concentration = r.expectation μ (fun i =>
        (R i).channel.expectation (scorePosterior μ (r.prob i)) (fun j => Real.log ((R i).B j))) := r.expectation_dbind (fun i => (R i).channel) μ (fun i => Real.log ((R i.1).B i.2))
    have hblock : finiteInformation μ r.prob ≤ s.information+s.concentration+L := by
      rw [s.channel.information_bind q μ]
      have hs : (∑ i,scoreMass μ (s.channel.prob i)*finiteInformation (scorePosterior μ (s.channel.prob i)) (q i).prob) ≤
          s.channel.expectation μ (fun i => L+Real.log (s.B i)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : scoreMass μ (s.channel.prob i) = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (hcost i
            (lt_of_le_of_ne (scoreMass_nonneg μ _ (s.channel.nonneg i)) (Ne.symm h)))
            (scoreMass_nonneg μ _ (s.channel.nonneg i))
      rw [s.channel.expectation_add μ,s.channel.expectation_const μ] at hs
      change _ ≤ L+s.concentration at hs
      change s.information+_ ≤ _
      linarith
    unfold AnalysisState.potential
    rw [hinfo,hconc,hdepth]
    linarith
  · refine ⟨{
      choose := fun i z => ⟨i,(R i).select z⟩
      choose_fiber := ?_
      erase_choose := fun _ _ => rfl
      chosen := ?_
      positive_parent := ?_
      contains := fun i z hz => (R i).select_mem z hz
      subset := fun j => (R j.1).cell_subset j.2 }⟩
    · intro i j
      obtain ⟨k,j⟩ := j
      by_cases h : i = k
      · subst i
        change MeasurableSet {z | (⟨k,(R k).select z⟩ : Sigma (fun i => (R i).Index)) = ⟨k,j⟩}
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using (R k).select_fiber j
      · have he : {z | (⟨i,(R i).select z⟩ : Sigma (fun i => (R i).Index)) = ⟨k,j⟩} = ∅ := by
          ext z
          simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
          intro h'
          exact h (congrArg Sigma.fst h')
        rw [he]
        exact MeasurableSet.empty
    · intro j z hz
      change 0 < r.prob j.1 z*(R j.1).channel.prob j.2 z at hz
      have hpos : 0 < (R j.1).channel.prob j.2 z :=
        pos_of_mul_pos_right hz (r.nonneg j.1 z)
      exact congrArg (Sigma.mk j.1) ((R j.1).chosen j.2 z hpos)
    · intro j z hz
      change 0 < (s.channel.prob j.1.1 z*(q j.1.1).prob j.1.2 z)*(R j.1).channel.prob j.2 z at hz
      have hr : 0 < s.channel.prob j.1.1 z*(q j.1.1).prob j.1.2 z :=
        pos_of_mul_pos_left hz ((R j.1).channel.nonneg j.2 z)
      exact pos_of_mul_pos_left hr ((q j.1.1).nonneg j.1.2 z)
end RepeatedLocalization

end OAI
