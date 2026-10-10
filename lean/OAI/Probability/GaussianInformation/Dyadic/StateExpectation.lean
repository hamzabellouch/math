import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.ChannelEntropy

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
namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

noncomputable def expectation (p : FiniteChannel α ι) (μ : Measure α) (f : ι → ℝ) : ℝ :=
  ∑ i,scoreMass μ (p.prob i)*f i

lemma expectation_const (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    p.expectation μ (fun _ => c) = c := by
  rw [expectation,← Finset.sum_mul,p.mass_total μ,one_mul]

lemma expectation_add (p : FiniteChannel α ι) (μ : Measure α) (f g : ι → ℝ) :
    p.expectation μ (fun i => f i+g i) = p.expectation μ f+p.expectation μ g := by
  simp [expectation,mul_add,Finset.sum_add_distrib]

lemma expectation_const_mul (p : FiniteChannel α ι) (μ : Measure α) (c : ℝ) (f : ι → ℝ) :
    p.expectation μ (fun i => c*f i) = c*p.expectation μ f := by
  simp only [expectation,Finset.mul_sum]; congr 1; funext i; ring

lemma expectation_mono (p : FiniteChannel α ι) (μ : Measure α) {f g : ι → ℝ} (h : ∀ i,f i ≤ g i) :
    p.expectation μ f ≤ p.expectation μ g :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (scoreMass_nonneg μ _ (p.nonneg i)))

lemma sum_mass_dbind {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : ι) :
    (∑ j,scoreMass μ ((p.dbind q).prob ⟨i,j⟩)) = scoreMass μ (p.prob i) := by
  unfold scoreMass
  rw [← integral_finsetSum _ (fun j _ => (p.dbind q).integrable μ ⟨i,j⟩)]
  simp [dbind,← Finset.mul_sum,FiniteChannel.total]

lemma expectation_dbind {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (f : Sigma κ → ℝ) :
    (p.dbind q).expectation μ f = p.expectation μ (fun i =>
      (q i).expectation (scorePosterior μ (p.prob i)) (fun j => f ⟨i,j⟩)) := by
  unfold expectation
  rw [Fintype.sum_sigma]
  simp_rw [p.mass_dbind q μ,mul_assoc,← Finset.mul_sum]

lemma expectation_dbind_fst {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (f : ι → ℝ) :
    (p.dbind q).expectation μ (fun i => f i.1) = p.expectation μ f := by
  unfold expectation
  rw [Fintype.sum_sigma]
  simp_rw [← Finset.sum_mul,p.sum_mass_dbind q μ]

lemma expectation_bind_fst {κ : Type*} [Fintype κ]
    (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsFiniteMeasure μ] (f : ι → ℝ) :
    (p.bind q).expectation μ (fun i => f i.1) = p.expectation μ f := by
  have hm (i : ι) : (∑ j,scoreMass μ ((p.bind q).prob (i,j))) = scoreMass μ (p.prob i) := by
    unfold scoreMass
    rw [← integral_finsetSum _ (fun j _ => (p.bind q).integrable μ (i,j))]
    simp [bind,← Finset.mul_sum,FiniteChannel.total]
  unfold expectation
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul,hm]

lemma bind_positive_parent {κ : Type*} [Fintype κ]
    (p : FiniteChannel α ι) (q : ι → FiniteChannel α κ)
    (μ : Measure α) [IsFiniteMeasure μ] (i : ι × κ)
    (hi : 0 < scoreMass μ ((p.bind q).prob i)) : 0 < scoreMass μ (p.prob i.1) :=
  hi.trans_le (scoreMass_mul_le μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2))

lemma dbind_positive_parent {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : Sigma κ)
    (hi : 0 < scoreMass μ ((p.dbind q).prob i)) : 0 < scoreMass μ (p.prob i.1) :=
  hi.trans_le (scoreMass_mul_le μ _ _ (p.measurable i.1) ((q i.1).measurable i.2)
    (p.nonneg i.1) ((q i.1).nonneg i.2) (p.le_one i.1) ((q i.1).le_one i.2))

lemma dbind_positive_conditional {κ : ι → Type*} [∀ i,Fintype (κ i)]
    (p : FiniteChannel α ι) (q : ∀ i,FiniteChannel α (κ i))
    (μ : Measure α) [IsFiniteMeasure μ] (i : Sigma κ)
    (hi : 0 < scoreMass μ ((p.dbind q).prob i)) :
    0 < scoreMass (scorePosterior μ (p.prob i.1)) ((q i.1).prob i.2) := by
  rw [p.mass_dbind q μ i] at hi
  exact (mul_pos_iff_of_pos_left (p.dbind_positive_parent q μ i (by rw [p.mass_dbind q μ i]; exact hi))).mp hi

end FiniteChannel

lemma zero_heavy_refinement (n : ℕ) (Q : Cell n) : Nonempty (HeavyRefinement n 0 Q) := by
  let q : FiniteChannel (Coordinate n) Unit := {
    prob := fun _ _ => 1
    measurable := fun _ => measurable_const
    nonneg := fun _ _ => zero_le_one
    total := fun _ => by simp }
  refine ⟨{ Index := Unit
            channel := q
            cell := fun _ => Q
            B := fun _ => 1
            B_one := fun _ => le_refl _
            select := fun _ => ()
            select_fiber := fun i => by simp only [Subsingleton.elim () i, Set.ofPred_true]; exact MeasurableSet.univ
            chosen := fun i z hz => Subsingleton.elim _ _
            cell_subset := fun _ => Subset.rfl
            select_mem := fun z hz => hz
            level_ge := fun _ => le_refl _
            support := ?_
            spread := ?_
            entropy_bound := ?_
            concentration_bound := ?_ }⟩
  · intro i hi; simp [scoreMass] at hi
  · intro i hi; simp [scoreMass] at hi
  · simp [finiteInformation,infoContribution,scoreMass,xlog_zero]
    exact Real.log_nonneg (by norm_num)
  · simp [scoreMass]
    positivity

structure AnalysisState (n : ℕ) where
  Index : Type
  [finiteIndex : Fintype Index]
  channel : FiniteChannel (Coordinate n) Index
  cell : Index → Cell n
  B : Index → ℝ
  B_one : ∀ i,1 ≤ B i
  support : ∀ i,0 < scoreMass (cubePrior n) (channel.prob i) →
    scorePosterior (cubePrior n) (channel.prob i) (cellSet (cell i)) = 1
  spread : ∀ i,0 < scoreMass (cubePrior n) (channel.prob i) →
    DyadicSpread (scorePosterior (cubePrior n) (channel.prob i)) (cell i) (B i)

attribute [instance] AnalysisState.finiteIndex

namespace AnalysisState
variable {n : ℕ}
noncomputable def information (s : AnalysisState n) : ℝ := finiteInformation (cubePrior n) s.channel.prob
noncomputable def depth (s : AnalysisState n) : ℝ := s.channel.expectation (cubePrior n) (fun i => (s.cell i).1)
noncomputable def concentration (s : AnalysisState n) : ℝ := s.channel.expectation (cubePrior n) (fun i => Real.log (s.B i))
noncomputable def potential (s : AnalysisState n) : ℝ :=
  s.information+s.concentration-((n:ℝ)/2+2)*Real.log 2*s.depth

lemma depth_nonneg (s : AnalysisState n) : 0 ≤ s.depth :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (scoreMass_nonneg _ _ (s.channel.nonneg i)) (Nat.cast_nonneg _))

lemma concentration_nonneg (s : AnalysisState n) : 0 ≤ s.concentration :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (scoreMass_nonneg _ _ (s.channel.nonneg i)) (Real.log_nonneg (s.B_one i)))

lemma information_lower (hn : 0 < n) (s : AnalysisState n) :
    (n:ℝ)*Real.log 2*s.depth ≤ s.information := by
  have := cubePrior_isProbabilityMeasure hn
  change (n:ℝ)*Real.log 2*(∑ i,scoreMass (cubePrior n) (s.channel.prob i)*((s.cell i).1:ℝ)) ≤
    ∑ i,infoContribution (cubePrior n) (s.channel.prob i)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : scoreMass (cubePrior n) (s.channel.prob i) = 0
  · simp only [h,zero_mul,mul_zero]
    exact infoContribution_nonneg _ _ (s.channel.measurable i) (s.channel.nonneg i) (s.channel.le_one i)
  have hP : 0 < scoreMass (cubePrior n) (s.channel.prob i) :=
    lt_of_le_of_ne (scoreMass_nonneg _ _ (s.channel.nonneg i)) (Ne.symm h)
  have := scorePosterior_probability _ _ (s.channel.measurable i) (s.channel.nonneg i) (s.channel.le_one i) hP
  have hval : (cubePrior n).real (cellSet (s.cell i)) = (1/2:ℝ)^(n*(s.cell i).1) := by
    rw [measureReal_def,cubePrior_cellSet hn,ENNReal.toReal_ofReal (by positivity)]
  have hz := (scorePosterior_null_iff (cubePrior n) _ (s.channel.measurable i) (s.channel.nonneg i) hP
    _ (measurableSet_cellSet (s.cell i)).compl).mp
      ((prob_compl_eq_zero_iff (measurableSet_cellSet (s.cell i))).mpr (s.support i hP))
  have hl := infoContribution_support_lower (cubePrior n) _ (s.channel.measurable i) (s.channel.nonneg i) (s.channel.le_one i)
    _ (measurableSet_cellSet (s.cell i)) (by rw [hval]; positivity) hz
  rw [hval,Real.log_pow] at hl
  have he : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  rw [he] at hl
  push_cast at hl
  nlinarith

lemma information_of_potential (hn : 8 ≤ n) (s : AnalysisState n) {A : ℝ}
    (h : s.potential ≤ A) : s.information ≤ 4*A := by
  have hl := s.information_lower (by omega)
  have hc := s.concentration_nonneg
  have hd := s.depth_nonneg
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hb : (((n:ℝ)/2+2)*Real.log 2)*s.depth ≤ (3/4:ℝ)*((n:ℝ)*Real.log 2*s.depth) := by
    nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-8 by linarith) (mul_nonneg hlog.le hd)]
  unfold potential at h
  linarith

end AnalysisState

lemma scorePosterior_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    scorePosterior μ (fun _ => 1) = μ := by simp [scorePosterior,scoreMass]

lemma cubePrior_spread_root {n : ℕ} (hn : 0 < n) : DyadicSpread (cubePrior n) (rootCell n) 1 := by
  intro j R hR hsub
  have hlev : R.1 = j := by simpa [rootCell] using hR
  rw [cubePrior_cellSet hn,hlev,one_mul]
  change ENNReal.ofReal ((1/2:ℝ)^(n*j)) ≤ ENNReal.ofReal (heavyThreshold n j)
  apply ENNReal.ofReal_le_ofReal
  rw [← heavyThreshold_sq]
  have hle : heavyThreshold n j ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn0 hj0]
  have hp := (heavyThreshold_pos n j).le
  nlinarith

noncomputable def initialState {n : ℕ} (hn : 0 < n) : AnalysisState n := by
  letI := cubePrior_isProbabilityMeasure hn
  let p : FiniteChannel (Coordinate n) Unit := {
    prob := fun _ _ => 1
    measurable := fun _ => measurable_const
    nonneg := fun _ _ => zero_le_one
    total := fun _ => by simp }
  exact {
    Index := Unit
    channel := p
    cell := fun _ => rootCell n
    B := fun _ => 1
    B_one := fun _ => le_refl _
    support := fun _ _ => by
      change scorePosterior (cubePrior n) (fun _ => 1) (cellSet (rootCell n)) = 1
      rw [scorePosterior_one,cubePrior_cellSet hn]; simp [rootCell]
    spread := fun _ _ => by
      change DyadicSpread (scorePosterior (cubePrior n) (fun _ => 1)) (rootCell n) 1
      rw [scorePosterior_one]; exact cubePrior_spread_root hn }

lemma initialState_potential {n : ℕ} (hn : 0 < n) : (initialState hn).potential = 0 := by
  have := cubePrior_isProbabilityMeasure hn
  simp [initialState,AnalysisState.potential,AnalysisState.information,AnalysisState.concentration,
    AnalysisState.depth,FiniteChannel.expectation,finiteInformation,infoContribution,scoreMass,xlog_one,rootCell]

lemma posterior_cube_domination {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (p : FiniteChannel (Coordinate n) ι) (i : ι)
    (hi : 0 < scoreMass (cubePrior n) (p.prob i)) (R : Cell n) :
    (scorePosterior (cubePrior n) (p.prob i)).real (cellSet R) ≤
      (1/scoreMass (cubePrior n) (p.prob i))*(1/2:ℝ)^(n*R.1) := by
  have h := scorePosterior_apply_le (cubePrior n) _ (p.le_one i) hi _ (measurableSet_cellSet R)
  rw [cubePrior_cellSet hn] at h
  have he := ENNReal.toReal_mono (by finiteness) h
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/scoreMass (cubePrior n) (p.prob i)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1/2:ℝ)^(n*R.1))] using he

def appendHistoryEquiv (N t : ℕ) : (History N t × Fin N) ≃ History N (t+1) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin N))

lemma appendHistoryEquiv_apply {N t : ℕ} (w : History N t) (v : Fin N) :
    appendHistoryEquiv N t (w,v) = Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v := rfl

def initRules {n N t : ℕ} (rules : Rules n N (t+1)) : Rules n N t :=
  fun i => rules i.castSucc

lemma past_snoc_castSucc {N t : ℕ} (w : History N t) (v : Fin N) (i : Fin t) :
    past (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) i.castSucc = past w i := by
  funext j
  change Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v (Fin.castSucc ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩) = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (t+1) => Fin N) v w ⟨j.val,Nat.lt_trans j.isLt i.isLt⟩

lemma past_snoc_last {N t : ℕ} (w : History N t) (v : Fin N) :
    past (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) (Fin.last t) = w := by
  funext j
  change Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v j.castSucc = _
  simp

lemma historyLikelihood_snoc {n N t : ℕ} (rules : Rules n N (t+1))
    (z : Coordinate n) (w : History N t) (v : Fin N) :
    historyLikelihood rules z (Fin.snoc (α := fun _ : Fin (t+1) => Fin N) w v) =
      historyLikelihood (initRules rules) z w * blockProbability (rules (Fin.last t) w) z v := by
  rw [historyLikelihood,Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,past_snoc_castSucc,past_snoc_last]
  rfl

lemma historyLikelihood_sum {n N t : ℕ} (rules : Rules n N t) (z : Coordinate n) :
    ∑ w,historyLikelihood rules z w = 1 := by
  induction t with
  | zero => simp [historyLikelihood]
  | succ t ih =>
    rw [← Equiv.sum_comp (appendHistoryEquiv N t),Fintype.sum_prod_type]
    simp_rw [appendHistoryEquiv_apply,historyLikelihood_snoc,← Finset.mul_sum,blockProbability_sum,mul_one]
    exact ih (initRules rules)

noncomputable def blockChannel {n N : ℕ} (rule : BlockRule n N) : FiniteChannel (Coordinate n) (Fin N) where
  prob := fun w z => blockProbability rule z w
  measurable := measurable_blockProbability rule
  nonneg := fun w z => blockProbability_nonneg rule z w
  total := blockProbability_sum rule

noncomputable def historyChannel {n N t : ℕ} (rules : Rules n N t) : FiniteChannel (Coordinate n) (History N t) where
  prob := fun w z => historyLikelihood rules z w
  measurable := measurable_historyLikelihood rules
  nonneg := fun w z => historyLikelihood_nonneg rules z w
  total := historyLikelihood_sum rules

end RepeatedLocalization

end OAI
