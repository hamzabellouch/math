import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.StateExpectation

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

variable {α ι κ η : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ] [Fintype η]

lemma coarsen_equiv (p : FiniteChannel α ι) (e : ι ≃ κ) (j : κ) (x : α) :
    (p.coarsen e).prob j x = p.prob (e.symm j) x := by
  classical
  change (∑ i,if e i = j then p.prob i x else 0) = _
  have he (i : ι) : e i = j ↔ i = e.symm j := by
    constructor
    · intro h; simpa using congrArg e.symm h
    · intro h; rw [h]; simp
  simp_rw [he]
  simp

lemma coarsen_bind_map (p : FiniteChannel α ι) (f : ι → κ) (q : κ → FiniteChannel α η) :
    ((p.bind (fun i => q (f i))).coarsen (fun i => (f i.1,i.2))).prob =
      ((p.coarsen f).bind q).prob := by
  classical
  funext k x
  rcases k with ⟨k,v⟩
  simp only [coarsen,bind,Fintype.sum_prod_type,Prod.mk.injEq]
  have he (i : ι) : (∑ j : η,if f i = k ∧ j = v then p.prob i x*(q (f i)).prob j x else 0) =
      if f i = k then p.prob i x*(q k).prob v x else 0 := by
    by_cases h : f i = k <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : f i = k <;> simp [h]

lemma coarsen_congr_prob {p q : FiniteChannel α ι} (h : p.prob = q.prob) (f : ι → κ) :
    (p.coarsen f).prob = (q.coarsen f).prob := by
  classical
  funext i x
  change (∑ j,if f j = i then p.prob j x else 0) = (∑ j,if f j = i then q.prob j x else 0)
  rw [h]

lemma bind_congr_prob {p q : FiniteChannel α ι} (h : p.prob = q.prob) (r : ι → FiniteChannel α κ) :
    (p.bind r).prob = (q.bind r).prob := by
  funext i x
  change p.prob i.1 x*(r i.1).prob i.2 x = q.prob i.1 x*(r i.1).prob i.2 x
  rw [h]

end FiniteChannel

lemma historyChannel_succ {n N t : ℕ} (rules : Rules n N (t+1)) :
    (((historyChannel (initRules rules)).bind (fun w => blockChannel (rules (Fin.last t) w))).coarsen
      (appendHistoryEquiv N t)).prob = (historyChannel rules).prob := by
  funext w z
  obtain ⟨⟨h,v⟩,rfl⟩ := (appendHistoryEquiv N t).surjective w
  rw [FiniteChannel.coarsen_equiv]
  simp only [Equiv.symm_apply_apply]
  exact (historyLikelihood_snoc rules z h v).symm

lemma FiniteChannel.ext_prob {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {p q : FiniteChannel α ι} (h : p.prob = q.prob) : p = q := by
  cases p
  cases q
  cases h
  rfl

def UniformBlockCost (n N : ℕ) (L : ℝ) : Prop :=
  ∀ (μ : Measure (Coordinate n)), IsProbabilityMeasure μ → ∀ (Q : Cell n) (B : ℝ),
    μ (cellSet Q) = 1 → 1 ≤ B → DyadicSpread μ Q B → ∀ rule : BlockRule n N,
      finiteInformation μ (blockChannel rule).prob ≤ L+Real.log B

lemma experimentLaw_eq_law {n N t : ℕ} (hn : 0 < n) (rules : Rules n N t) :
    experimentLaw rules = (historyChannel rules).law (cubePrior n) := by
  have := cubePrior_isProbabilityMeasure hn
  rw [FiniteChannel.law_eq_sum]
  rfl

lemma experimentLaw_probability {n N t : ℕ} (hn : 0 < n) (rules : Rules n N t) :
    IsProbabilityMeasure (experimentLaw rules) := by
  have := cubePrior_isProbabilityMeasure hn
  rw [experimentLaw_eq_law hn]
  infer_instance

lemma mutualInformation_experiment {n N t : ℕ} (hn : 0 < n) (rules : Rules n N t) :
    mutualInformation (experimentLaw rules) =
      ENNReal.ofReal (finiteInformation (cubePrior n) (historyChannel rules).prob) := by
  have := cubePrior_isProbabilityMeasure hn
  rw [experimentLaw_eq_law hn,mutualInformation,FiniteChannel.klDiv_law]

lemma mutualInformation_map_right {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) [IsFiniteMeasure μ] (g : β → γ) (hg : Measurable g) :
    mutualInformation (μ.map (Prod.map id g)) ≤ mutualInformation μ := by
  have hm : Measurable (Prod.map (id : α → α) g) := measurable_id.prodMap hg
  have hf : (μ.map (Prod.map id g)).map Prod.fst = μ.map Prod.fst := by
    rw [Measure.map_map measurable_fst hm]
    rfl
  have hs : (μ.map (Prod.map id g)).map Prod.snd = (μ.map Prod.snd).map g := by
    rw [Measure.map_map measurable_snd hm,Measure.map_map hg measurable_snd]
    rfl
  have he : (μ.map Prod.fst).prod ((μ.map Prod.snd).map g) =
      ((μ.map Prod.fst).prod (μ.map Prod.snd)).map (Prod.map id g) := by
    simpa using Measure.map_prod_map (μ.map Prod.fst) (μ.map Prod.snd) measurable_id hg
  unfold mutualInformation
  rw [hf,hs,he]
  exact InformationTheory.klDiv_map_le _ _ hm

lemma actual_uniform_blockCost {n N : ℕ} (hn : 32 ≤ n) (hN : 1 ≤ N)
    {C₀ : ℝ} (halphabet : (2/(n/8:ℕ)+Real.exp (-(1/2:ℝ)*(n/16:ℕ)))*Real.log N ≤ C₀*(n+1)) :
    UniformBlockCost n N ((blockInformationConstant+C₀)*(n+1)) := by
  intro μ hμ Q B hsupport hB hspread rule
  have := hμ
  have hs : μ (cellSet Q)ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_cellSet Q)).mpr hsupport
  have h := actual_block_information hn hN Q μ hs hB hspread rule
  have he : (-(n/16:ℕ)/2:ℝ) = -(1/2:ℝ)*(n/16:ℕ) := by ring
  rw [he] at h
  change finiteInformation μ (fun w z => blockProbability rule z w) ≤ _
  linarith

end RepeatedLocalization

end OAI
