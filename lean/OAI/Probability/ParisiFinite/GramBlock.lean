import Mathlib
import OAI.Probability.ParisiFinite.LowBlock

namespace OAI

/-! Gram Block. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def GramBlock (r : ℕ) : Set (OverlapBlock r) := {T |
  (∀ i j, T i j=T j i) ∧ (∀ i, (T i i:ℝ)=1) ∧
  ∀ c : Fin r → ℝ, 0≤∑ i,∑ j,c i*c j*(T i j:ℝ)}

lemma isClosed_GramBlock (r : ℕ) : IsClosed (GramBlock r) := by
  unfold GramBlock
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun c => isClosed_le continuous_const (by fun_prop)))

lemma GramArrays_block {R : OverlapArray} (h : R∈GramArrays) (r : ℕ) : blockOfArray r R∈GramBlock r :=
  ⟨fun i j => h.1 i j,fun i => h.2.1 i,h.2.2 r⟩

lemma blockSupport_Gram {μ : ProbabilityMeasure OverlapArray} (hG : (μ : Measure OverlapArray) GramArrays=1)
    (r : ℕ) : (blockLaw μ r).support ⊆ GramBlock r := by
  apply Measure.support_subset_of_isClosed (isClosed_GramBlock r)
  apply ae_iff.mpr
  change blockLaw μ r (GramBlock r)ᶜ=0
  rw [blockLaw,Measure.map_apply (continuous_blockOfArray r).measurable (isClosed_GramBlock r).measurableSet.compl]
  apply measure_mono_null (show (blockOfArray r) ⁻¹' (GramBlock r)ᶜ ⊆ GramArraysᶜ from
    fun R hR h => hR (GramArrays_block h r))
  rw [measure_compl isClosed_GramArrays.measurableSet (measure_ne_top _ _),hG]
  simp

lemma support_event_nonempty {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [HereditarilyLindelofSpace Ω] (ν : Measure Ω) {E : Set Ω} (hE : 0<ν E) : (E∩ν.support).Nonempty := by
  by_contra hn
  have hs : E⊆ν.supportᶜ := by
    intro x hx hx'
    exact hn ⟨x,hx,hx'⟩
  exact (ne_of_gt hE) (measure_mono_null hs ν.measure_compl_support)

def rowBall {r : ℕ} (x : Fin r → OverlapEntry) (ε : ℝ) : Set (Fin r → OverlapEntry) :=
  {y | ∀ i, |(y i:ℝ)-(x i:ℝ)|<ε}

def blockBall {r : ℕ} (T : OverlapBlock r) (ε : ℝ) : Set (OverlapBlock r) :=
  {U | ∀ i j, |(U i j:ℝ)-(T i j:ℝ)|<ε}

lemma isOpen_rowBall {r : ℕ} (x : Fin r → OverlapEntry) (ε : ℝ) : IsOpen (rowBall x ε) := by
  unfold rowBall
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const

lemma isOpen_blockBall {r : ℕ} (T : OverlapBlock r) (ε : ℝ) : IsOpen (blockBall T ε) := by
  unfold blockBall
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

lemma isOpen_patternBlock {r : ℕ} {C : Set (OverlapBlock r)} {B : Set (Fin r → OverlapEntry)}
    (hC : IsOpen C) (hB : IsOpen B) : IsOpen (patternBlock r C B) :=
  (hC.preimage (continuous_initialBlock _)).inter (hB.preimage (continuous_newRow _))

 

lemma exists_supported_approx_duplication {μ : ProbabilityMeasure OverlapArray} (hG : (μ : Measure OverlapArray) GramArrays=1)
    (hgg : GGIdentities μ) (hex : FiniteExchangeable μ) {r : ℕ} (hr : 0<r)
    {A : OverlapBlock (r+1)} (hA : A∈(blockLaw μ (r+1)).support) (q : ℝ)
    (hrow : ∀ i : Fin r, (A (Fin.last r) i.castSucc:ℝ)≤q)
    {ε : ℝ} (hε : 0<ε) : ∃ T : OverlapBlock (r+2),
    T∈(blockLaw μ (r+2)).support ∧
    (∀ i j : Fin (r+1), |(T i.castSucc j.castSucc:ℝ)-(A i j:ℝ)|<ε) ∧
    (∀ i : Fin r, |(T (Fin.last (r+1)) i.castSucc.castSucc:ℝ)-(A (Fin.last r) i.castSucc:ℝ)|<ε) ∧
    (T (Fin.last r).castSucc (Fin.last (r+1)):ℝ)≤q+ε := by
  let C := blockBall (initialBlock (Nat.le_succ r) A) ε
  let B := rowBall (newRow A (0:Fin 1)) ε
  have hC : IsOpen C := isOpen_blockBall _ _
  have hB : IsOpen B := isOpen_rowBall _ _
  have ha : A∈patternBlock r C B := by
    constructor <;> intro i
    · intro j; simpa only [sub_self,abs_zero] using hε
    · simpa only [sub_self,abs_zero] using hε
  have hp := (Measure.mem_support_iff_forall A).mp hA (patternBlock r C B)
    ((isOpen_patternBlock hC hB).mem_nhds ha)
  have hp' : 0<(μ : Measure OverlapArray).real ((blockOfArray (r+1)) ⁻¹' patternBlock r C B) := by
    rw [blockLaw,Measure.map_apply (continuous_blockOfArray _).measurable (isOpen_patternBlock hC hB).measurableSet] at hp
    exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _)
  have hb : ∀ x∈B, ∀ i, (x i:ℝ)≤q+ε := by
    intro x hx i
    have hh := (abs_lt.mp (hx i)).2
    have hi := hrow i
    change (A (Fin.last r) i.castSucc:ℝ)≤q at hi
    change (x i:ℝ)-(A (Fin.last r) i.castSucc:ℝ)<ε at hh
    linarith
  have hd := GG_duplication_of_positive hgg hex hr hC.measurableSet hB.measurableSet (q+ε) hb hp'
  have he : 0<blockLaw μ (r+2) (doubleMarkBlock r C B (q+ε)) := by
    rw [blockLaw,Measure.map_apply (continuous_blockOfArray _).measurable (measurableSet_doubleMarkBlock hC.measurableSet hB.measurableSet _)]
    change 0<(μ : Measure OverlapArray) (doubleMarkAt r (r+1) C B (q+ε))
    exact ENNReal.toReal_pos_iff.mp hd |>.1
  obtain ⟨T,hT,hTs⟩ := support_event_nonempty _ he
  have hGT := blockSupport_Gram hG (r+2) hTs
  have hGA := blockSupport_Gram hG (r+1) hA
  refine ⟨T,hTs,?_,hT.2.2.1,hT.2.2.2⟩
  intro i j
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [hGT.2.1,hGA.2.1]; simpa using hε
    · exact hT.2.1 b
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · rw [hGT.1,hGA.1]; exact hT.2.1 a
    · exact hT.1 a b

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

theorem exists_supported_duplication_last {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ) (hex : FiniteExchangeable μ)
    {r : ℕ} (hr : 0<r) {A : OverlapBlock (r+1)} (hA : A∈(blockLaw μ (r+1)).support) (q : ℝ)
    (hrow : ∀ i : Fin r, (A (Fin.last r) i.castSucc:ℝ)≤q) :
    ∃ T : OverlapBlock (r+2), T∈(blockLaw μ (r+2)).support ∧
      (∀ i j : Fin (r+1), T i.castSucc j.castSucc=A i j) ∧
      (∀ i : Fin r, T (Fin.last (r+1)) i.castSucc.castSucc=A (Fin.last r) i.castSucc) ∧
      (T (Fin.last r).castSucc (Fin.last (r+1)):ℝ)≤q := by
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  choose T hTs hTo hTn hTq using fun n =>
    exists_supported_approx_duplication hG hgg hex hr hA q hrow (hε n)
  obtain ⟨U,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq T
  have heps : Tendsto (fun k => ε (φ k)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hφ.tendsto_atTop
  have hcoord (i j : Fin (r+2)) : Tendsto (fun k => (T (φ k) i j:ℝ)) atTop (𝓝 (U i j:ℝ)) :=
    (show Continuous (fun V : OverlapBlock (r+2) => (V i j:ℝ)) by fun_prop).continuousAt.tendsto.comp hlim
  have heq (i j : Fin (r+2)) (a : OverlapEntry)
      (h : ∀ k, |(T (φ k) i j:ℝ)-(a:ℝ)|<ε (φ k)) : U i j=a := by
    apply Subtype.ext
    have hh : |(U i j:ℝ)-(a:ℝ)|≤0 :=
      le_of_tendsto_of_tendsto' ((hcoord i j).sub_const (a:ℝ) |>.abs) heps (fun k => le_of_lt (h k))
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  refine ⟨U,(blockLaw μ (r+2)).isClosed_support.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => hTs (φ k)),?_,?_,?_⟩
  · intro i j
    exact heq _ _ _ (fun k => hTo (φ k) i j)
  · intro i
    exact heq _ _ _ (fun k => hTn (φ k) i)
  · have hh := le_of_tendsto_of_tendsto' (hcoord (Fin.last r).castSucc (Fin.last (r+1)))
      (tendsto_const_nhds.add heps) (fun k => hTq (φ k))
    simpa only [add_zero] using hh

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def permBlock {r : ℕ} (p : Equiv.Perm (Fin r)) (T : OverlapBlock r) : OverlapBlock r :=
  fun i j => T (p i) (p j)

lemma continuous_permBlock {r : ℕ} (p : Equiv.Perm (Fin r)) : Continuous (permBlock p) := by
  unfold permBlock
  fun_prop

lemma blockLaw_map_perm {μ : ProbabilityMeasure OverlapArray} (hex : FiniteExchangeable μ)
    {r : ℕ} (p : Equiv.Perm (Fin r)) : (blockLaw μ r).map (permBlock p)=blockLaw μ r := by
  rw [blockLaw,Measure.map_map (continuous_permBlock p).measurable (continuous_blockOfArray r).measurable]
  exact hex r (fun i => (p i:ℕ)) (Fin.val_injective.comp p.injective)

lemma permBlock_support {μ : ProbabilityMeasure OverlapArray} (hex : FiniteExchangeable μ)
    {r : ℕ} (p : Equiv.Perm (Fin r)) {T : OverlapBlock r} (hT : T∈(blockLaw μ r).support) :
    permBlock p T∈(blockLaw μ r).support := by
  rw [Measure.support_eq_forall_isOpen] at hT ⊢
  intro U hU hOpen
  have hh := hT ((permBlock p) ⁻¹' U) hU (hOpen.preimage (continuous_permBlock p))
  have he := congrArg (fun ν : Measure (OverlapBlock r) => ν U) (blockLaw_map_perm hex p)
  rw [Measure.map_apply (continuous_permBlock p).measurable hOpen.measurableSet] at he
  rwa [he] at hh

def headPerm {r : ℕ} (p : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr p (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] lemma headPerm_old {r : ℕ} (p : Equiv.Perm (Fin r)) (i : Fin r) :
    headPerm p i.castSucc=(p i).castSucc := by simp [headPerm]; rfl

@[simp] lemma headPerm_last {r : ℕ} (p : Equiv.Perm (Fin r)) :
    headPerm p (Fin.last r)=Fin.last r := by
  change headPerm p (Fin.natAdd r (0:Fin 1))=Fin.natAdd r (0:Fin 1)
  simp [headPerm]

 

theorem exists_supported_duplication {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ) (hex : FiniteExchangeable μ)
    {r : ℕ} (hr : 0<r) {A : OverlapBlock (r+1)} (hA : A∈(blockLaw μ (r+1)).support)
    (i : Fin (r+1)) (q : ℝ) (hrow : ∀ j : Fin (r+1), j≠i → (A i j:ℝ)≤q) :
    ∃ T : OverlapBlock (r+2), T∈(blockLaw μ (r+2)).support ∧
      (∀ j k : Fin (r+1), T j.castSucc k.castSucc=A j k) ∧
      (∀ j : Fin (r+1), j≠i → T (Fin.last (r+1)) j.castSucc=A i j) ∧
      (T i.castSucc (Fin.last (r+1)):ℝ)≤q := by
  let p := Equiv.swap i (Fin.last r)
  have hp : p (Fin.last r)=i := by simp [p]
  have hpi : p.symm i=Fin.last r := by simp [p]
  have hrb (j : Fin r) : (permBlock p A (Fin.last r) j.castSucc:ℝ)≤q := by
    change (A (p (Fin.last r)) (p j.castSucc):ℝ)≤q
    rw [hp]
    apply hrow
    intro he
    have hh : p j.castSucc=p (Fin.last r) := he.trans hp.symm
    exact Fin.castSucc_ne_last j (p.injective hh)
  obtain ⟨V,hV,hold,hnew,hq⟩ := exists_supported_duplication_last hG hgg hex hr
    (permBlock_support hex p hA) q hrb
  let T := permBlock (headPerm p.symm) V
  refine ⟨T,permBlock_support hex _ hV,?_,?_,?_⟩
  · intro j k
    dsimp [T,permBlock]
    rw [headPerm_old,headPerm_old,hold]
    simp [permBlock]
  · intro j hji
    have hj : p.symm j≠Fin.last r := by
      intro he
      have : j=p (Fin.last r) := by simpa using congrArg p he
      exact hji (this.trans hp)
    obtain ⟨k,hk⟩ := Fin.exists_castSucc_eq.mpr hj
    dsimp [T,permBlock]
    rw [headPerm_last,headPerm_old,← hk,hnew]
    change A (p (Fin.last r)) (p k.castSucc)=A i j
    rw [hp,hk,p.apply_symm_apply]
  · dsimp [T,permBlock]
    rw [headPerm_old,headPerm_last,hpi]
    exact hq

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def gramForm {r : ℕ} (T : OverlapBlock r) (u v : Fin r → ℝ) : ℝ :=
  ∑ i,∑ j,u i*v j*(T i j:ℝ)

def gramDelta {r : ℕ} (i : Fin r) : Fin r → ℝ := fun j => if j=i then 1 else 0

lemma gramForm_symm {r : ℕ} {T : OverlapBlock r} (hT : T∈GramBlock r) (u v : Fin r → ℝ) :
    gramForm T u v=gramForm T v u := by
  unfold gramForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hT.1 j i]
  ring

@[simp] lemma gramForm_delta_left {r : ℕ} (T : OverlapBlock r) (i : Fin r) (v : Fin r → ℝ) :
    gramForm T (gramDelta i) v=∑ j,v j*(T i j:ℝ) := by
  simp [gramForm,gramDelta,ite_mul]

@[simp] lemma gramForm_delta_delta {r : ℕ} (T : OverlapBlock r) (i j : Fin r) :
    gramForm T (gramDelta i) (gramDelta j)=(T i j:ℝ) := by
  simp [gramDelta,gramForm,ite_mul]

lemma gramForm_sub_left {r : ℕ} (T : OverlapBlock r) (u v w : Fin r → ℝ) :
    gramForm T (u-v) w=gramForm T u w-gramForm T v w := by
  simp [gramForm,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma gramForm_sub_right {r : ℕ} (T : OverlapBlock r) (u v w : Fin r → ℝ) :
    gramForm T u (v-w)=gramForm T u v-gramForm T u w := by
  simp [gramForm,Pi.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

lemma gramForm_smul_left {r : ℕ} (T : OverlapBlock r) (u v : Fin r → ℝ) (a : ℝ) :
    gramForm T (a • u) v=a*gramForm T u v := by
  simp only [gramForm,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

lemma gramForm_smul_right {r : ℕ} (T : OverlapBlock r) (u v : Fin r → ℝ) (a : ℝ) :
    gramForm T u (a • v)=a*gramForm T u v := by
  unfold gramForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change u i*(a*v j)*(T i j:ℝ)=a*(u i*v j*(T i j:ℝ))
  ring

lemma gramForm_sum_left {r : ℕ} {ι : Type*} [Fintype ι] (T : OverlapBlock r)
    (u : ι → Fin r → ℝ) (v : Fin r → ℝ) :
    gramForm T (∑ a,u a) v=∑ a,gramForm T (u a) v := by
  simp only [gramForm,Finset.sum_apply,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a, ∑ j, u a i*v j*(T i j:ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma gramForm_sum_right {r : ℕ} {ι : Type*} [Fintype ι] (T : OverlapBlock r)
    (u : Fin r → ℝ) (v : ι → Fin r → ℝ) :
    gramForm T u (∑ a,v a)=∑ a,gramForm T u (v a) := by
  simp only [gramForm,Finset.sum_apply,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a, ∑ j, u i*v a j*(T i j:ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

 

lemma gramForm_coordinate_sq_le {r : ℕ} {T : OverlapBlock r} (hT : T∈GramBlock r)
    (i : Fin r) (u : Fin r → ℝ) : (gramForm T (gramDelta i) u)^2≤gramForm T u u := by
  let a := gramForm T (gramDelta i) u
  have hh := hT.2.2 (u-a • gramDelta i)
  change 0≤gramForm T (u-a • gramDelta i) (u-a • gramDelta i) at hh
  rw [gramForm_sub_left,gramForm_sub_right,gramForm_sub_right,
    gramForm_smul_right,gramForm_smul_left,gramForm_smul_left,gramForm_smul_right,
    gramForm_delta_delta,hT.2.1,gramForm_symm hT u (gramDelta i)] at hh
  change 0≤gramForm T u u-a*a-(a*a-a*(a*1)) at hh
  nlinarith only [hh]

def gramCluster {r m : ℕ} (e : Fin m → Fin r) : Fin r → ℝ := ∑ j,gramDelta (e j)

lemma gramForm_clusters {r m k : ℕ} (T : OverlapBlock r) (e : Fin m → Fin r) (f : Fin k → Fin r) :
    gramForm T (gramCluster e) (gramCluster f)=∑ i,∑ j,(T (e i) (f j):ℝ) := by
  unfold gramCluster
  simp_rw [gramForm_sum_left,gramForm_sum_right,gramForm_delta_delta]

lemma gramForm_delta_cluster {r m : ℕ} (T : OverlapBlock r) (i : Fin r) (e : Fin m → Fin r) :
    gramForm T (gramDelta i) (gramCluster e)=∑ j,(T i (e j):ℝ) := by
  unfold gramCluster
  simp_rw [gramForm_sum_right,gramForm_delta_delta]

lemma gramCluster_norm_bound {r m : ℕ} {T : OverlapBlock r} (hT : T∈GramBlock r)
    (hm : 0 < m) (e : Fin m → Fin r) {c : ℝ}
    (he : ∀ i j, i≠j → (T (e i) (e j):ℝ)≤c) :
    gramForm T (gramCluster e) (gramCluster e)≤(m:ℝ)*(1+((m:ℝ)-1)*c) := by
  have hr (i : Fin m) : (∑ j,(T (e i) (e j):ℝ))≤1+((m:ℝ)-1)*c := by
    calc
      _ = (∑ j∈Finset.univ.erase i,(T (e i) (e j):ℝ))+(T (e i) (e i):ℝ) :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
      _ ≤ (∑ j∈Finset.univ.erase i,c)+1 := add_le_add
        (Finset.sum_le_sum fun j hj => he i j (Finset.ne_of_mem_erase hj).symm) (le_of_eq (hT.2.1 (e i)))
      _ = _ := by simp [Nat.cast_sub (show 1 ≤ m by omega)]; ring
  rw [gramForm_clusters]
  calc
    _ ≤ ∑ _i : Fin m, (1+((m:ℝ)-1)*c) := Finset.sum_le_sum fun i _ => hr i
    _ = _ := by simp; ring

 

theorem gram_two_cluster_bound {r m : ℕ} {T : OverlapBlock r} (hT : T∈GramBlock r)
    (hm : 0 < m) (i : Fin r) (e f : Fin m → Fin r) (a b c : ℝ)
    (ha : ∀ j,(T i (e j):ℝ)=a) (hb : ∀ j,(T i (f j):ℝ)=b)
    (hc : ∀ j k,(T (e j) (f k):ℝ)=c)
    (he : ∀ j k,j≠k → (T (e j) (e k):ℝ)≤c)
    (hf : ∀ j k,j≠k → (T (f j) (f k):ℝ)≤c) :
    (m:ℝ)^2*(a-b)^2≤2*(m:ℝ)*(1-c) := by
  have hx : gramForm T (gramCluster e) (gramCluster f)=(m:ℝ)^2*c := by
    rw [gramForm_clusters]
    simp_rw [hc]
    simp
    ring
  have hpa : gramForm T (gramDelta i) (gramCluster e)=(m:ℝ)*a := by
    rw [gramForm_delta_cluster]
    simp_rw [ha]
    simp
  have hpb : gramForm T (gramDelta i) (gramCluster f)=(m:ℝ)*b := by
    rw [gramForm_delta_cluster]
    simp_rw [hb]
    simp
  have hs := gramForm_coordinate_sq_le hT i (gramCluster e-gramCluster f)
  rw [gramForm_sub_right,hpa,hpb,gramForm_sub_left,gramForm_sub_right,gramForm_sub_right,
    gramForm_symm hT (gramCluster f) (gramCluster e),hx] at hs
  have h₁ := gramCluster_norm_bound hT hm e he
  have h₂ := gramCluster_norm_bound hT hm f hf
  nlinarith only [hs,h₁,h₂]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma duplication_preserves_low {r : ℕ} {A : OverlapBlock (r+1)} {T : OverlapBlock (r+2)}
    (hT : T∈GramBlock (r+2)) (i : Fin (r+1)) {c : ℝ}
    (hA : ∀ j k, j≠k → (A j k:ℝ)≤c)
    (hold : ∀ j k : Fin (r+1), T j.castSucc k.castSucc=A j k)
    (hnew : ∀ j : Fin (r+1), j≠i → T (Fin.last (r+1)) j.castSucc=A i j)
    (hq : (T i.castSucc (Fin.last (r+1)):ℝ)≤c) :
    ∀ j k, j≠k → (T j k:ℝ)≤c := by
  intro j k
  refine Fin.lastCases ?_ (fun a => ?_) j
  · refine Fin.lastCases (fun h => (h rfl).elim) (fun b _ => ?_) k
    by_cases hb : b=i
    · subst b; rw [hT.1]; exact hq
    · rw [hnew b hb]; exact hA i b (Ne.symm hb)
  · refine Fin.lastCases (fun _ => ?_) (fun b hab => ?_) k
    · rw [hT.1]
      by_cases ha : a=i
      · subst a; rw [hT.1]; exact hq
      · rw [hnew a ha]; exact hA i a (Ne.symm ha)
    · rw [hold]
      exact hA a b (fun he => hab (congrArg Fin.castSucc he))

structure TwoClusters (μ : ProbabilityMeasure OverlapArray) (m k : ℕ) (a b c : ℝ) where
  r : ℕ
  r_pos : 0<r
  block : OverlapBlock (r+1)
  supported : block∈(blockLaw μ (r+1)).support
  root : Fin (r+1)
  left : Fin m → Fin (r+1)
  right : Fin k → Fin (r+1)
  left_inj : Function.Injective left
  right_inj : Function.Injective right
  left_root : ∀ j, left j≠root
  right_root : ∀ j, right j≠root
  disjoint : ∀ j l, left j≠right l
  low : ∀ j l, j≠l → (block j l:ℝ)≤c
  root_left : ∀ j, (block root (left j):ℝ)=a
  root_right : ∀ j, (block root (right j):ℝ)=b
  cross : ∀ j l, (block (left j) (right l):ℝ)=c

namespace TwoClusters
variable {μ : ProbabilityMeasure OverlapArray} {m k : ℕ} {a b c : ℝ}

def swap (hG : (μ : Measure OverlapArray) GramArrays=1) (S : TwoClusters μ m k a b c) :
    TwoClusters μ k m b a c where
  r := S.r
  r_pos := S.r_pos
  block := S.block
  supported := S.supported
  root := S.root
  left := S.right
  right := S.left
  left_inj := S.right_inj
  right_inj := S.left_inj
  left_root := S.right_root
  right_root := S.left_root
  disjoint := fun j l => (S.disjoint l j).symm
  low := S.low
  root_left := S.root_right
  root_right := S.root_left
  cross := fun j l => by rw [(blockSupport_Gram hG _ S.supported).1]; exact S.cross l j

 

noncomputable def growLeft (hG : (μ : Measure OverlapArray) GramArrays=1)
    (hgg : GGIdentities μ) (hex : FiniteExchangeable μ) (hm : 0 < m)
    (S : TwoClusters μ m k a b c) : TwoClusters μ (m+1) k a b c := by
  let i := S.left ⟨0,hm⟩
  let h := exists_supported_duplication hG hgg hex S.r_pos S.supported i c
    (fun j hj => S.low i j hj.symm)
  let T := h.choose
  obtain ⟨hTs,hold,hnew,hq⟩ := h.choose_spec
  change T∈(blockLaw μ (S.r+2)).support at hTs
  change (∀ j l, T j.castSucc l.castSucc=S.block j l) at hold
  change (∀ j, j≠i → T (Fin.last (S.r+1)) j.castSucc=S.block i j) at hnew
  change (T i.castSucc (Fin.last (S.r+1)):ℝ)≤c at hq
  have hTG := blockSupport_Gram hG _ hTs
  let e : Fin (m+1) → Fin (S.r+2) := Fin.lastCases (Fin.last (S.r+1)) (fun j => (S.left j).castSucc)
  let f : Fin k → Fin (S.r+2) := fun j => (S.right j).castSucc
  have eold (j : Fin m) : e j.castSucc=(S.left j).castSucc := by simp [e]
  have enew : e (Fin.last m)=Fin.last (S.r+1) := by simp [e]
  refine ⟨S.r+1,by omega,T,hTs,S.root.castSucc,e,f,?_,?_,?_,?_,?_,
    duplication_preserves_low hTG i S.low hold hnew hq,?_,?_,?_⟩
  · intro j l
    refine Fin.lastCases ?_ (fun u => ?_) j
    · refine Fin.lastCases (fun _ => rfl) (fun v hv => ?_) l
      rw [enew,eold] at hv
      exact (Fin.castSucc_ne_last _ hv.symm).elim
    · refine Fin.lastCases (fun hu => ?_) (fun v huv => ?_) l
      · rw [eold,enew] at hu
        exact (Fin.castSucc_ne_last _ hu).elim
      · rw [eold,eold] at huv
        exact congrArg Fin.castSucc (S.left_inj ((Fin.castSucc_injective _) huv))
  · exact (Fin.castSucc_injective _).comp S.right_inj
  · intro j
    refine Fin.lastCases ?_ (fun u => ?_) j
    · rw [enew]; exact (Fin.castSucc_ne_last _).symm
    · rw [eold]; exact fun he => S.left_root u ((Fin.castSucc_injective _) he)
  · intro j he
    exact S.right_root j ((Fin.castSucc_injective _) he)
  · intro j l
    refine Fin.lastCases ?_ (fun u => ?_) j
    · rw [enew]; exact (Fin.castSucc_ne_last _).symm
    · rw [eold]; exact fun he => S.disjoint u l ((Fin.castSucc_injective _) he)
  · intro j
    refine Fin.lastCases ?_ (fun u => ?_) j
    · rw [enew,hTG.1,hnew S.root (S.left_root ⟨0,hm⟩).symm]
      rw [(blockSupport_Gram hG _ S.supported).1]
      exact S.root_left ⟨0,hm⟩
    · rw [eold,hold]; exact S.root_left u
  · intro j
    change (T S.root.castSucc (S.right j).castSucc:ℝ)=b
    rw [hold]; exact S.root_right j
  · intro j l
    refine Fin.lastCases ?_ (fun u => ?_) j
    · rw [enew]
      change (T (Fin.last (S.r+1)) (S.right l).castSucc:ℝ)=c
      rw [hnew _ (S.disjoint ⟨0,hm⟩ l).symm]
      exact S.cross ⟨0,hm⟩ l
    · rw [eold]
      change (T (S.left u).castSucc (S.right l).castSucc:ℝ)=c
      rw [hold]; exact S.cross u l

noncomputable def growRight (hG : (μ : Measure OverlapArray) GramArrays=1)
    (hgg : GGIdentities μ) (hex : FiniteExchangeable μ) (hk : 0 < k)
    (S : TwoClusters μ m k a b c) : TwoClusters μ m (k+1) a b c :=
  ((S.swap hG).growLeft hG hgg hex hk).swap hG

end TwoClusters
end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

namespace TwoClusters
variable {μ : ProbabilityMeasure OverlapArray} {a b c : ℝ}

noncomputable def replicate (hG : (μ : Measure OverlapArray) GramArrays=1)
    (hgg : GGIdentities μ) (hex : FiniteExchangeable μ)
    (S : TwoClusters μ 1 1 a b c) : (n : ℕ) → TwoClusters μ (n+1) (n+1) a b c
  | 0 => S
  | n+1 => ((replicate hG hgg hex S n).growLeft hG hgg hex (by omega)).growRight hG hgg hex (by omega)

 
theorem root_overlap_eq (hG : (μ : Measure OverlapArray) GramArrays=1)
    (hgg : GGIdentities μ) (hex : FiniteExchangeable μ)
    (S : TwoClusters μ 1 1 a b c) : a=b := by
  by_contra hab
  have hd : 0<(a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  obtain ⟨n,hn⟩ := exists_nat_gt (2*(1-c)/(a-b)^2)
  have hn' : 2*(1-c)<(n:ℝ)*(a-b)^2 := (div_lt_iff₀ hd).mp hn
  let V := S.replicate hG hgg hex n
  have hs := gram_two_cluster_bound (blockSupport_Gram hG _ V.supported)
    (show 0 < n+1 by omega) V.root V.left V.right a b c V.root_left V.root_right V.cross
    (fun j k hjk => V.low _ _ (fun he => hjk (V.left_inj he)))
    (fun j k hjk => V.low _ _ (fun he => hjk (V.right_inj he)))
  have hm : (0:ℝ)<n+1 := by positivity
  have hf : 0<((n:ℝ)+1)*(((n:ℝ)+1)*(a-b)^2-2*(1-c)) := mul_pos hm (by nlinarith only [hn',hd])
  push_cast at hs
  nlinarith only [hs,hf]

end TwoClusters

 
theorem supported_triangle_ordered {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ) (hex : FiniteExchangeable μ)
    {A : OverlapBlock 3} (hA : A∈(blockLaw μ 3).support)
    (hab : (A 0 1:ℝ)≤(A 0 2:ℝ)) (hbc : (A 0 2:ℝ)≤(A 1 2:ℝ)) : A 0 1=A 0 2 := by
  have hg := blockSupport_Gram hG _ hA
  have h10 := hg.1 1 0
  have h20 := hg.1 2 0
  have h21 := hg.1 2 1
  let S : TwoClusters μ 1 1 (A 0 1:ℝ) (A 0 2:ℝ) (A 1 2:ℝ) := {
    r := 2
    r_pos := by norm_num
    block := A
    supported := hA
    root := 0
    left := fun _ => 1
    right := fun _ => 2
    left_inj := fun _ _ _ => Subsingleton.elim _ _
    right_inj := fun _ _ _ => Subsingleton.elim _ _
    left_root := by intro j; decide
    right_root := by intro j; decide
    disjoint := by intro j l; decide
    low := by
      intro j l hjl
      fin_cases j <;> fin_cases l <;> simp_all <;> exact le_trans hab hbc
    root_left := fun _ => rfl
    root_right := fun _ => rfl
    cross := fun _ _ => rfl }
  exact Subtype.ext (S.root_overlap_eq hG hgg hex)

 

theorem supported_triangle_ultrametric {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ : Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ) (hex : FiniteExchangeable μ)
    {A : OverlapBlock 3} (hA : A∈(blockLaw μ 3).support) :
    min (A 0 2:ℝ) (A 1 2:ℝ)≤(A 0 1:ℝ) := by
  by_contra h
  have hh := lt_min_iff.mp (lt_of_not_ge h)
  by_cases hc : (A 0 2:ℝ)≤(A 1 2:ℝ)
  · have he := supported_triangle_ordered hG hgg hex hA hh.1.le hc
    exact (ne_of_lt hh.1) (congrArg Subtype.val he)
  · let p : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    have hp01 : permBlock p A 0 1=A 0 1 := by
      simp [permBlock,p,(blockSupport_Gram hG _ hA).1 1 0]
    have hp02 : permBlock p A 0 2=A 1 2 := by simp [permBlock,p,Equiv.swap_apply_def, show (2:Fin 3)≠0 by decide, show (2:Fin 3)≠1 by decide]
    have hp12 : permBlock p A 1 2=A 0 2 := by simp [permBlock,p,Equiv.swap_apply_def, show (2:Fin 3)≠0 by decide, show (2:Fin 3)≠1 by decide]
    have he := supported_triangle_ordered hG hgg hex (permBlock_support hex p hA)
      (by rw [hp01,hp02]; exact hh.2.le) (by rw [hp02,hp12]; exact le_of_not_ge hc)
    rw [hp01,hp02] at he
    exact (ne_of_lt hh.2) (congrArg Subtype.val he)

end SKCavity

end

end OAI
