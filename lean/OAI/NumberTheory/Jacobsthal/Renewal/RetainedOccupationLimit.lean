import OAI.NumberTheory.Jacobsthal.Partitions.SourceNodeCoordinates
import OAI.NumberTheory.Jacobsthal.Primes.LiteralUniformPrimeTail

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CompactLogOccupationTest

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels CompactInverseTest
open CompactTestGeometry CompactTestMeasurable ActualCouplingUpdates
open CycleResponse AdmissibleCycleTests ArrivalKernelGeometry RegeneratingInverseBands
open NormalizedOccupationLimit EvenStartOccupation

noncomputable def logTest (H : Side → ℝ×ℝ → ℝ) (x : ℝ×State) : ℝ :=
  inverseTest H (stateSide x.2) (Real.exp x.1,stateRatio x.2)

theorem logTest_measurable {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) : Measurable (logTest H) := by
  have hcoord : Measurable (fun x : ℝ×State => (Real.exp x.1,stateRatio x.2)) :=
    (Real.measurable_exp.comp measurable_fst).prodMk (stateRatio_measurable.comp measurable_snd)
  have hside : MeasurableSet {x : ℝ×State | stateSide x.2 = .even} :=
    measurable_snd (side_set_measurable .even)
  have heq : logTest H = (fun x => if stateSide x.2 = .even then inverseTest H .even (Real.exp x.1,stateRatio x.2)
      else inverseTest H .odd (Real.exp x.1,stateRatio x.2)) := by
    funext x
    rcases x with ⟨u,s⟩
    cases s <;> rfl
  rw [heq]
  exact Measurable.ite hside ((inverseTest_continuous hH .even).measurable.comp hcoord)
    ((inverseTest_continuous hH .odd).measurable.comp hcoord)

theorem logTest_continuous_shift {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) (s : State) :
    Continuous (fun u => logTest H (u,s)) := by
  change Continuous (fun u : ℝ => inverseTest H (stateSide s) (Real.exp u,stateRatio s))
  exact (inverseTest_continuous hH (stateSide s)).comp (Real.continuous_exp.prodMk continuous_const)

theorem logTest_compact_bound {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : HasCompactBound (logTest H) := by
  obtain ⟨A,hA,hbound⟩ := inverseTest_bounded hH hcompact
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨A,M,hA,hM,?_,?_⟩
  · intro x
    simpa only [logTest,Real.norm_eq_abs] using hbound (stateSide x.2) (Real.exp x.1,stateRatio x.2)
  · rintro ⟨u,s⟩ hu
    have hcase : u < Real.log a ∨ Real.log b < u := by
      by_contra hn
      push Not at hn
      have hlo := neg_abs_le (Real.log a)
      have hup := le_abs_self (Real.log b)
      have hle : |u| ≤ M := abs_le.mpr ⟨by dsimp [M]; linarith [abs_nonneg (Real.log b)],by dsimp [M]; linarith [abs_nonneg (Real.log a)]⟩
      exact (not_lt_of_ge hle) hu
    have hzero : H (stateSide s) (Real.exp u,stateRatio s) = 0 := by
      apply hsupport
      rcases hcase with h | h
      · exact Or.inl (by simpa only [Real.exp_log ha] using Real.exp_lt_exp.mpr h)
      · exact Or.inr (by simpa only [Real.exp_log hb] using Real.exp_lt_exp.mpr h)
    simp [logTest,inverseTest,hzero]

theorem logTest_admissible {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : Admissible (logTest H) :=
  Admissible.base (logTest_measurable hH) (logTest_continuous_shift hH)
    (logTest_compact_bound hH hcompact ha hb hsupport)

noncomputable def arrivalTest (ell : ℝ) (H : Side → ℝ×ℝ → ℝ) : Test :=
  AdmissibleCycleTests.mask {x | stateRatio x.2 < Real.exp x.1/ell} (logTest H)

theorem arrivalTest_admissible {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) : Admissible (arrivalTest ell H) :=
  (logTest_admissible hH hcompact ha hb hsupport).arrival ell hell

theorem logTest_shift_eq (H : Side → ℝ×ℝ → ℝ) (v : ℝ) (z : CostState) :
    logTest H (v-z.2,z.1) = continuousTest v (inverseTest H) (.inl z) := rfl

theorem arrivalTest_shift_eq (H : Side → ℝ×ℝ → ℝ) (v : ℝ) {ell : ℝ} (hell : 0 < ell) (z : CostState) :
    arrivalTest ell H (v-z.2,z.1) =
      (arrivalSet v ell).indicator (fun y => continuousTest v (inverseTest H) (.inl y)) z := by
  classical
  rw [arrivalSet_eq_cutoff v hell]
  rfl

theorem source_inverse_log_limit {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) :
    ∀ ε : ℝ,0 < ε → ∃ V : ℝ,∀ v : ℝ,V ≤ v → ∀ s : EvenState,
      (199/100:ℝ) ≤ s.1 → s.1 ≤ 23/10 →
      ‖evenResponse (arrivalTest ell H) s v-invariantAverage (arrivalTest ell H)‖ < ε :=
  source_compact_occupation_limit (arrivalTest_admissible hH hcompact ha hb hell hsupport)

end NumberTheoryLean.CompactLogOccupationTest

end

section

namespace NumberTheoryLean.ContinuousOccupationIdentification

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures TransitionKernels CompactInverseTest CompactLogOccupationTest
open CycleResponse AdmissibleCycleTests EvenStartOccupation OriginalHarmonicOccupation
open CostPrefixTransport OccupationDecomposition ContinuousCompactHighError
open CompactTestGeometry CompactTestMeasurable FiniteAdmittedOccupation SignedCompletedPowers
open AdmittedHarmonicPaths ArrivalKernelGeometry LowStateHorizon SignedCompactTransfer

theorem evenResponse_eq_inclusive {F : Test} (hF : Measurable F) (hB : HasCompactBound F)
    (s : EvenState) (v : ℝ) :
    evenResponse F s v = ∫ y : CostState,F (v-y.2,y.1) ∂inclusiveOccupation (.inl s,0) := by
  have hm := shiftedTest_measurable hF v
  obtain ⟨C,M,hC,hM,hbound,hsupp⟩ := hB
  have hi : Integrable (fun y : CostState => F (v-y.2,y.1)) (Measure.dirac (.inl s,0)) :=
    bounded_integrable hm (fun y => by simpa only [Real.norm_eq_abs] using hbound (v-y.2,y.1))
  have hf := even_full_test_integrable hF ⟨C,M,hC,hM,hbound,hsupp⟩ s v
  rw [inclusiveOccupation,_root_.add_apply,Kernel.id_apply,integral_add_measure hi hf,
    integral_dirac' _ _ hm.stronglyMeasurable]
  simp only [sub_zero,evenResponse]

theorem full_admitted_eq_response {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 0 < ell)
    (hsupport : ∀ i : FinitePathGeometry.Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (s : EvenState) (v : ℝ) (hstart : (.inl s,0) ∈ arrivalSet v ell) :
    (∫ z,inverseReward v H z ∂occupation (admittedTilted v ell) (.inl s,0)) =
      evenResponse (arrivalTest ell H) s v := by
  have htest := arrivalTest_admissible hH hcompact ha hb hell hsupport
  rw [admitted_tilted_occupation v ell (.inl s,0) hstart,← integral_indicator (arrivalSet_measurable v ell)]
  have he : (fun y : CostState => arrivalTest ell H (v-y.2,y.1)) =
      (arrivalSet v ell).indicator (inverseReward v H) := by
    funext y
    exact arrivalTest_shift_eq H v hell y
  rw [← he]
  exact (evenResponse_eq_inclusive htest.measurable htest.compactBound s v).symm

theorem low_occupation_eq_expectation {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : RegeneratingInverseBands.gapValue v z ≤ (23/10:ℝ)*B) :
    (∫ y,inverseReward v H y ∂occupation (lowKernel costKernel v ell S) z) =
      continuousExpectation (inverseTest H) v ell S z (sourceHorizon S B) := by
  obtain ⟨A,hA,hbound⟩ := inverseTest_bounded hH hcompact
  have hG : ∀ y : CostState,|inverseReward v H y| ≤ A := fun y => hbound _ _
  have hm := inverseReward_measurable v hH
  rw [low_occupation_integral_eq_source_sum v ell S B hell hS hB z hgap hm hG]
  apply Finset.sum_congr rfl
  intro n _hn
  have he : liftReal (inverseReward v H) = continuousTest v (inverseTest H) := by
    funext y
    cases y <;> rfl
  rw [← he]
  exact (continuous_signed_power v ell S n z hm hA hG).symm

end NumberTheoryLean.ContinuousOccupationIdentification

end

section

namespace NumberTheoryLean.ContinuousLowOccupationLimit

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels CompactInverseTest
open CompactLogOccupationTest SourceLowRemoval ContinuousOccupationIdentification
open ContinuousCompactHighError RegeneratingInverseBands ArrivalKernelGeometry
open OriginalHarmonicOccupation AdmittedHarmonicPaths LowStateHorizon
open SignedCompactTransfer NormalizedOccupationLimit EvenStartOccupation

theorem source_continuous_low_limit {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0) :
    ∀ ε : ℝ,0 < ε → ∃ B₀ : ℝ,0 < B₀ ∧ ∀ B : ℝ,B₀ ≤ B → ∀ v : ℝ,∀ s : EvenState,
      (199/100:ℝ) ≤ s.1 → s.1 ≤ 23/10 → currentExponent v (.inl s,0)=B →
      |continuousExpectation (inverseTest H) v ell ((Real.log B)^2) (.inl s,0)
        (sourceHorizon ((Real.log B)^2) B)-invariantAverage (arrivalTest ell H)| ≤ ε := by
  intro ε hε
  obtain ⟨C,hC,hremove⟩ := source_low_removal hH hcompact (K:=b) (fun i r s h => hsupport i r s (Or.inr h))
  obtain ⟨BR,hBR⟩ := eventually_atTop.mp hremove
  obtain ⟨V,hV⟩ := source_inverse_log_limit hH hcompact ha hb (show 0 < ell by linarith) hsupport (ε/2) (by linarith)
  let B₀ := max BR (max (Real.exp 2) (max (ell+1) (max (Real.exp V) (2*C/ε))))
  have hExpB₀ : Real.exp 2 ≤ B₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨B₀,(Real.exp_pos 2).trans_le hExpB₀,?_⟩
  intro B hB v s hsL hsU hcut
  have hBR' : BR ≤ B := (le_max_left _ _).trans hB
  have hBexp : Real.exp 2 ≤ B := hExpB₀.trans hB
  have hBell : ell+1 ≤ B :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBV : Real.exp V ≤ B :=
    (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBC : 2*C/ε ≤ B :=
    (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBp : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hS : 0 < (Real.log B)^2 := by nlinarith
  have hstart : (.inl s,0) ∈ arrivalSet v ell := by change ell < currentExponent v (.inl s,0); rw [hcut]; linarith
  have hv : V ≤ v := by
    have he : Real.exp v = B*s.1 := by
      change Real.exp (v-0)/s.1=B at hcut
      rw [sub_zero] at hcut
      exact (div_eq_iff (show s.1 ≠ 0 by linarith [s.2])).mp hcut
    apply Real.exp_le_exp.mp
    rw [he]
    have hBmul : B ≤ B*s.1 := by nlinarith
    exact hBV.trans hBmul
  have hfull := full_admitted_eq_response hH hcompact ha hb (show 0 < ell by linarith) hsupport s v hstart
  have hscale := source_scale_upper hBp s hsU hcut
  have hlow := low_occupation_eq_expectation hH hcompact v ell ((Real.log B)^2) B hell hS hBp (.inl s,0) hscale.2
  have hrem := hBR B hBR' v ell s hsL hsU hell (by linarith) hcut
  rw [hfull,hlow] at hrem
  have hsmall : C/B ≤ ε/2 := by
    apply (div_le_iff₀ hBp).mpr
    have hh := (div_le_iff₀ hε).mp hBC
    nlinarith
  have hlimit := hV v hv s hsL hsU
  rw [Real.norm_eq_abs] at hlimit
  have htri := abs_sub_le
    (continuousExpectation (inverseTest H) v ell ((Real.log B)^2) (.inl s,0) (sourceHorizon ((Real.log B)^2) B))
    (evenResponse (arrivalTest ell H) s v) (invariantAverage (arrivalTest ell H))
  rw [abs_sub_comm _ (evenResponse (arrivalTest ell H) s v)] at htri
  linarith

end NumberTheoryLean.ContinuousLowOccupationLimit

end

section

namespace NumberTheoryLean.RetainedOccupationLimit

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open LiteralPrimeOccupation SourceNodeCoordinates CompactInverseTest
open CorrectedCompactTransfer ContinuousLowOccupationLimit CompactLogOccupationTest
open SourceSuccessfulTail SignedCompactTransfer NormalizedOccupationLimit LowStateHorizon UniformBudgetRate

theorem retained_original_occupation_limit {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |familyValue H w ell ((Real.log B)^2) start-invariantAverage (arrivalTest ell H)| ≤ ε := by
  obtain ⟨BC,hBC,hcontinuous⟩ := source_continuous_low_limit hH hcompact ha hb hell hsupport (ε/2) (by linarith)
  obtain ⟨wP,hwP,hprime⟩ := source_inverse_compact_transfer H hH hcompact hb.le
    (fun i r s h => hsupport i r s (Or.inr h)) d (ε/2) hd (by linarith)
  obtain ⟨wScale,hwScale⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  refine ⟨max BC (Real.exp 2),max wP (max normalizationThreshold wScale),
    hBC.trans_le (le_max_left _ _),hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBC' : BC ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := hBC.trans_le hBC'
  have hBexp : Real.exp 2 ≤ B := (le_max_right _ _).trans hB
  have hlogB : 2 ≤ Real.log B := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hscale := source_scale_bound
    (hwScale w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)) hlogB hcomp
  obtain ⟨hs,hr,_,hsize⟩ := source_node_bounds hBpos start hi h199 h23 hcons hcut
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  obtain ⟨s,hsv,hcost⟩ := even_source_cost_state hs hi
  have hcurrent := source_currentExponent hr hs hcons
  rw [hcost,hcut] at hcurrent
  have hc := hcontinuous B hBC' (Real.log start.gap) s
    (by simpa only [hsv] using h199) (by simpa only [hsv] using h23) hcurrent
  have hp := hprime w ((le_max_left _ _).trans hw) ell B start hs hell hBpos hlogB hcomp hr h23 hcons hsize
  have hidentity := literal_corrected_occupation hnorm hell (sq_nonneg (Real.log B)) hscale.1 hr hs hsS hBpos hsize H
  dsimp only at hp
  rw [← hidentity,hcost] at hp
  have htri := abs_sub_le (familyValue H w ell ((Real.log B)^2) start)
    (continuousExpectation (inverseTest H) (Real.log start.gap) ell ((Real.log B)^2) (.inl s,0)
      (sourceHorizon ((Real.log B)^2) B)) (invariantAverage (arrivalTest ell H))
  linarith

end NumberTheoryLean.RetainedOccupationLimit

end

end Erdos970

end OAI
