import Mathlib
import OAI.Probability.ParisiFinite.ExpectedReindexStates

namespace OAI

/-! Ordered Code. -/

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
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def orderedCode {r : ℕ} (c : OrderedFinpartition r) : Fin r → ℕ := fun i => (c.index i).val

lemma orderedIndex_emb {r : ℕ} (c : OrderedFinpartition r) (i : Fin c.length) (j : Fin (c.partSize i)) :
    c.index (c.emb i j)=i := by
  exact congrArg Sigma.fst (c.equivSigma.symm_apply_apply ⟨i,j⟩)

lemma codeLabels_orderedCode {r : ℕ} (c : OrderedFinpartition r) :
    codeLabels (orderedCode c)=Finset.range c.length := by
  ext x
  simp only [codeLabels_mem,Finset.mem_range]
  constructor
  · rintro ⟨i,rfl⟩
    exact (c.index i).isLt
  · intro hx
    let i : Fin c.length := ⟨x,hx⟩
    refine ⟨c.emb i ⟨0,c.partSize_pos i⟩,?_⟩
    unfold orderedCode
    rw [orderedIndex_emb]

lemma labelCount_orderedCode {r : ℕ} (c : OrderedFinpartition r) (i : Fin c.length) :
    labelCount (orderedCode c) i=c.partSize i := by
  have hc : labelCount (orderedCode c) i=∑ j : Fin r,if (c.index j).val=i.val then 1 else 0 := by
    classical
    simp [labelCount,orderedCode]
    rfl
  rw [hc,← c.sum_sigma_eq_sum]
  simp only [orderedIndex_emb,Fin.val_inj]
  simp

lemma partitionNumerator_ordered {r : ℕ} (a : ℝ) (c : OrderedFinpartition r) :
    partitionNumerator a (orderedCode c)=
      tableFactor a c.length*∏ i,blockFactor a (c.partSize i) := by
  unfold partitionNumerator
  rw [codeLabels_orderedCode,Finset.card_range,← Fin.prod_univ_eq_prod_range]
  simp_rw [labelCount_orderedCode]

lemma tableFactor_explicit (a : ℝ) {k : ℕ} (hk : 0<k) :
    tableFactor a k=a^(k-1)*((k-1).factorial:ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k=0
    · subst k; simp
    have hk' := Nat.pos_of_ne_zero h
    rw [tableFactor_succ a hk',ih hk']
    simp only [Nat.add_sub_cancel]
    have hf : (k.factorial:ℝ)=(k:ℝ)*((k-1).factorial:ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred h).symm
    have hp : a^k=a^(k-1)*a := by rw [← pow_succ,Nat.sub_add_cancel hk']
    rw [hf,hp]
    ring

 

theorem GG_ordered_partition_probability {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) {r : ℕ} (hr : 0<r) (c : OrderedFinpartition r) :
    ((r-1).factorial:ℝ)*(μ:Measure OverlapArray).real (partitionEvent (orderedCode c) q)=
      (overlapDiscount μ q)^(c.length-1)*((c.length-1).factorial:ℝ)*
        ∏ i,blockFactor (overlapDiscount μ q) (c.partSize i) := by
  rw [GG_partition_EPPF hG hgg hu hq hr,partitionNumerator_ordered,
    tableFactor_explicit _ (c.length_pos hr)]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma iteratedDeriv_log_succ {x : ℝ} (hx : x≠0) (n : ℕ) :
    iteratedDeriv (n+1) Real.log x=(-1:ℝ)^n*(n.factorial:ℝ)*x^(-(n:ℤ)-1) := by
  induction n generalizing x with
  | zero => simp [iteratedDeriv_one,Real.deriv_log]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n+1) Real.log =ᶠ[𝓝 x]
        (fun y => (-1:ℝ)^n*(n.factorial:ℝ)*y^(-(n:ℤ)-1)) := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      exact ih hy
    rw [he.deriv_eq]
    have hd := (hasDerivAt_zpow (-(n:ℤ)-1) x (Or.inl hx)).const_mul
      ((-1:ℝ)^n*(n.factorial:ℝ))
    rw [hd.deriv,pow_succ,Nat.factorial_succ]
    push_cast
    have hz : -(n+1:ℤ)-1= -(n:ℤ)-1-1 := by omega
    rw [hz]
    ring

lemma iteratedDeriv_log_one {n : ℕ} (hn : 0<n) :
    iteratedDeriv n Real.log 1= -(-1:ℝ)^n*((n-1).factorial:ℝ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [iteratedDeriv_log_succ (by norm_num),pow_succ]
  simp

lemma signed_log_factor {a : ℝ} (ha : a≠0) {k : ℕ} (hk : 0<k) :
    a⁻¹*((-a)^k*(-(-1:ℝ)^k*((k-1).factorial:ℝ)))= -tableFactor a k := by
  rw [tableFactor_explicit a hk]
  have hp : a^k=a^(k-1)*a := by rw [← pow_succ,Nat.sub_add_cancel hk]
  have hs : (-a)^k*(-(-1:ℝ)^k)= -(a^k) := by
    rw [neg_eq_neg_one_mul a,mul_pow]
    have h : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
    calc
      (-1:ℝ)^k*a^k*(-(-1:ℝ)^k)= -((-1:ℝ)^k*(-1:ℝ)^k)*a^k := by ring
      _ = _ := by rw [h]; ring
  calc
    _ = a⁻¹*((-a)^k*(-(-1:ℝ)^k))*((k-1).factorial:ℝ) := by ring
    _ = _ := by rw [hs,hp]; field_simp

variable {ι : Type*} [Fintype ι]

lemma log_mark_derivative {a : ℝ} (ha : a≠0) (w x : ι → ℝ) (hw : ∑ i,w i=1)
    {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun z => a⁻¹*Real.log (finiteMarkTransform a w x z)) 0=
      -∑ c : OrderedFinpartition n,tableFactor a c.length*
        ∏ j,blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j) := by
  rw [iteratedDeriv_const_mul_field]
  have hz := finiteMarkTransform_zero a w x hw
  have hg : ContDiffAt ℝ n Real.log (finiteMarkTransform a w x 0) := by
    rw [hz]
    exact Real.contDiffAt_log.mpr (by norm_num)
  have h := iteratedDeriv_scomp_eq_sum_orderedFinpartition hg (contDiffAt_mark a w x n) (i:=n) le_rfl
  change iteratedDeriv n (fun z => Real.log (finiteMarkTransform a w x z)) 0=_ at h
  rw [h,Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [iteratedDeriv_mark a w x (c.partSize_pos _),hz,
    iteratedDeriv_log_one (c.length_pos hn),smul_eq_mul]
  have he : (∏ j,-a*blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j))=
      (-a)^c.length*∏ j,blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j) := by
    calc
      _ = ∏ j : Fin c.length,(-a)*(blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j)) := by
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [he]
  have hh := signed_log_factor ha (c.length_pos hn)
  linear_combination (∏ j,blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j))*hh

def orderedMarkedMoment (μ : ProbabilityMeasure OverlapArray) (q : ℝ)
    (moments : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition r,(μ:Measure OverlapArray).real (partitionEvent (orderedCode c) q)*
    ∏ j,moments (c.partSize j)

 

theorem GG_marked_log_derivative {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (ha : overlapDiscount μ q≠0)
    (w x : ι → ℝ) (hw : ∑ i,w i=1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun z => (overlapDiscount μ q)⁻¹*
      Real.log (finiteMarkTransform (overlapDiscount μ q) w x z)) 0=
      -((n-1).factorial:ℝ)*orderedMarkedMoment μ q (finiteMarkMoment w x) n := by
  rw [log_mark_derivative ha w x hw hn]
  unfold orderedMarkedMoment
  simp only [Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have he := GG_partition_EPPF hG hgg hu hq hn (orderedCode c)
  rw [partitionNumerator_ordered] at he
  have hp : (∏ j,blockFactor (overlapDiscount μ q) (c.partSize j)*finiteMarkMoment w x (c.partSize j))=
      (∏ j,blockFactor (overlapDiscount μ q) (c.partSize j))*(∏ j,finiteMarkMoment w x (c.partSize j)) :=
    Finset.prod_mul_distrib
  rw [hp]
  linear_combination (∏ j,finiteMarkMoment w x (c.partSize j))*he

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def branchFactor (a b : ℝ) (k : ℕ) : ℝ :=
  ∏ j∈Finset.range (k-1),(a*((j:ℝ)+1)-b)

@[simp] lemma branchFactor_one (a b : ℝ) : branchFactor a b 1=1 := by simp [branchFactor]
lemma branchFactor_zero (a : ℝ) (k : ℕ) : branchFactor a 0 k=tableFactor a k := by
  simp [branchFactor,tableFactor]
lemma branchFactor_succ (a b : ℝ) {k : ℕ} (hk : 0<k) :
    branchFactor a b (k+1)=branchFactor a b k*(a*k-b) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [branchFactor,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
  rw [Finset.prod_range_succ]
  push_cast
  rfl

lemma signed_power_factor {a : ℝ} (ha : a≠0) (b : ℝ) {k : ℕ} (hk : 0<k) :
    (-a)^k*fallingCoeff (b/a) k= -b*branchFactor a b k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k=0
    · subst k
      simp [fallingCoeff_succ]
      field_simp
    have hk' := Nat.pos_of_ne_zero hk0
    rw [pow_succ,fallingCoeff_succ,branchFactor_succ a b hk']
    have he := ih hk'
    have hab : (-a)*(b/a-k)=a*k-b := by field_simp; ring
    calc
      (-a)^k*(-a)*(fallingCoeff (b/a) k*(b/a-k))=
        ((-a)^k*fallingCoeff (b/a) k)*((-a)*(b/a-k)) := by ring
      _ = _ := by rw [he,hab]; ring

lemma iteratedDeriv_rpow_one (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => y^a) 1=fallingCoeff a n := by
  have h := iteratedDeriv_affine_rpow_zero a (-1) n
  have he : (fun z : ℝ => (1-z*(-1))^a)=(fun z => (fun y : ℝ => y^a) (z+1)) := by
    ext z; congr 1; ring
  rw [he] at h
  have ht := congrFun (iteratedDeriv_comp_add_const (f:=fun y : ℝ => y^a) (n:=n) (s:=1)) 0
  rw [ht] at h
  simpa using h

variable {ι : Type*} [Fintype ι]

 

lemma power_mark_derivative {a : ℝ} (ha : a≠0) (b : ℝ) (w x : ι → ℝ)
    (hw : ∑ i,w i=1) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun z => (finiteMarkTransform a w x z)^(b/a)) 0=
      -b*∑ c : OrderedFinpartition n,branchFactor a b c.length*
        ∏ j,blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j) := by
  have hz := finiteMarkTransform_zero a w x hw
  have hg : ContDiffAt ℝ n (fun y : ℝ => y^(b/a)) (finiteMarkTransform a w x 0) := by
    apply ContDiffAt.rpow_const_of_ne
    · fun_prop
    · rw [hz]; norm_num
  have h := iteratedDeriv_scomp_eq_sum_orderedFinpartition hg (contDiffAt_mark a w x n) (i:=n) le_rfl
  change iteratedDeriv n (fun z => (finiteMarkTransform a w x z)^(b/a)) 0=_ at h
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [iteratedDeriv_mark a w x (c.partSize_pos _),hz,iteratedDeriv_rpow_one,smul_eq_mul]
  have he : (∏ j,-a*blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j))=
      (-a)^c.length*∏ j,blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j) := by
    calc
      _ = ∏ j : Fin c.length,(-a)*(blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j)) := by
        apply Finset.prod_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [he]
  have hh := signed_power_factor ha b (c.length_pos hn)
  linear_combination (∏ j,blockFactor a (c.partSize j)*finiteMarkMoment w x (c.partSize j))*hh

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

theorem GG_join_on_block {μ : ProbabilityMeasure OverlapArray} (hgg : GGIdentities μ)
    {r : ℕ} {S : Set (OverlapBlock r)} (hS : MeasurableSet S)
    (c : Fin r → ℕ) (q : ℝ) (hc : S⊆partitionBlock c q) (i : Fin r) :
    (r:ℝ)*(μ:Measure OverlapArray).real {R | blockOfArray r R∈S ∧ q<(R i r:ℝ)}=
      ((clusterCount c i:ℝ)-overlapDiscount μ q)*
        (μ:Measure OverlapArray).real ((blockOfArray r) ⁻¹' S) := by
  let E := (blockOfArray r) ⁻¹' S
  have h := GG_event_identity hgg r i S {x | q<(x:ℝ)} hS
    (measurableSet_lt measurable_const (by fun_prop))
  change (r:ℝ)*(μ:Measure OverlapArray).real {R | R∈E ∧ q<(R i r:ℝ)}=
    (μ:Measure OverlapArray).real E*(entryLaw μ 0 1).real {x | q<(x:ℝ)}+
      ∑ l∈Finset.univ.erase i,(μ:Measure OverlapArray).real {R | R∈E ∧ q<(R i l:ℝ)} at h
  have hp (l : Fin r) : {R | R∈E ∧ q<(R i l:ℝ)}=if c i=c l then E else ∅ := by
    split_ifs with hh
    · ext R
      exact ⟨fun hR => hR.1,fun hR => ⟨hR,(hc hR i l).mpr hh⟩⟩
    · ext R
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hR => hh ((hc hR.1 i l).mp hR.2)
  simp_rw [hp] at h
  simp only [apply_ite,measureReal_empty] at h
  have hs : (∑ l∈Finset.univ.erase i,if c i=c l then (μ:Measure OverlapArray).real E else 0)=
    ((clusterCount c i:ℝ)-1)*(μ:Measure OverlapArray).real E := by
    have hj : (∑ l : Fin r,if c i=c l then (μ:Measure OverlapArray).real E else 0)=
        (clusterCount c i:ℝ)*(μ:Measure OverlapArray).real E := by
      simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      congr 2
      apply congrArg Finset.card
      ext l
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,eq_comm]
    have hh := Finset.sum_erase_add (s:=Finset.univ)
      (f:=fun l => if c i=c l then (μ:Measure OverlapArray).real E else 0) (Finset.mem_univ i)
    simp only [ite_true] at hh
    rw [hj] at hh
    linarith
  rw [hs,entry_upper_mass] at h
  calc
    _ = (μ:Measure OverlapArray).real E*(1-overlapDiscount μ q)+
        ((clusterCount c i:ℝ)-1)*(μ:Measure OverlapArray).real E := h
    _ = _ := by dsimp only [E]; ring

def ParentReps {r : ℕ} (p c : Fin r → ℕ) (i : Fin r) (T : Finset (Fin r)) : Prop :=
  Set.InjOn c T ∧ (∀ k∈T,p k=p i) ∧ (∀ j,p j=p i ↔ ∃ k∈T,c k=c j)

lemma sum_parent_clusterCount {r : ℕ} {p c : Fin r → ℕ} {i : Fin r}
    {T : Finset (Fin r)} (hT : ParentReps p c i T) :
    (∑ k∈T,clusterCount c k)=clusterCount p i := by
  have hc (d : Fin r → ℕ) (k) : clusterCount d k=∑ j : Fin r,if d j=d k then 1 else 0 := by
    simp [clusterCount]
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p j=p i
  · obtain ⟨k,hk,hkj⟩ := (hT.2.2 j).mp hj
    rw [ite_eq_left hj,Finset.sum_eq_single k]
    · simp [hkj]
    · intro l hl hlk
      have hne : c j≠c l := fun hh => hlk (hT.1 hl hk (hh.symm.trans hkj.symm))
      simp [hne]
    · exact fun hh => (hh hk).elim
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : c j≠c k := fun h => hj ((hT.2.2 j).mpr ⟨k,hk,h.symm⟩)
    simp [hne]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 

theorem GG_nested_innovation {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {r : ℕ} {S : Set (OverlapBlock r)} (hS : MeasurableSet S)
    {p c : Fin r → ℕ} {q t : ℝ} (hqt : q≤t)
    (hp : S⊆partitionBlock p q) (hc : S⊆partitionBlock c t)
    (i : Fin r) {T : Finset (Fin r)} (hT : ParentReps p c i T) :
    (r:ℝ)*(μ:Measure OverlapArray).real
      {R | blockOfArray r R∈S ∧ q<(R i r:ℝ) ∧ ∀ k∈T,(R k r:ℝ)≤t}=
      ((T.card:ℝ)*overlapDiscount μ t-overlapDiscount μ q)*
        (μ:Measure OverlapArray).real ((blockOfArray r) ⁻¹' S) := by
  let U := GramArrays∩UltrametricArrays
  let E := (blockOfArray r) ⁻¹' S
  let P : Set OverlapArray := {R | R∈E ∧ q<(R i r:ℝ)}
  let J (k : Fin r) : Set OverlapArray := {R | R∈E ∧ t<(R k r:ℝ)}
  let A : Set OverlapArray := ⋃ k∈T,J k
  have hUa : ∀ᵐ R ∂(μ:Measure OverlapArray),R∈U :=
    (ae_full_probability μ isClosed_GramArrays.measurableSet hG).and
      (ae_full_probability μ isClosed_UltrametricArrays.measurableSet hu)
  have hUr (V : Set OverlapArray) : (μ:Measure OverlapArray).real (U∩V)=(μ:Measure OverlapArray).real V :=
    congrArg ENNReal.toReal (Measure.measure_inter_eq_of_ae hUa)
  have hE : MeasurableSet E := hS.preimage (continuous_blockOfArray r).measurable
  have hJ (k : Fin r) : MeasurableSet (J k) := by
    change MeasurableSet (E∩{R : OverlapArray | t<(R k r:ℝ)})
    exact hE.inter (measurableSet_lt measurable_const (by fun_prop))
  have hA : MeasurableSet A := MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hJ k
  have hUP : U∩A⊆U∩P := by
    rintro R ⟨hR,hRA⟩
    obtain ⟨k,hRA⟩ := Set.mem_iUnion.mp hRA
    obtain ⟨hk,hRk⟩ := Set.mem_iUnion.mp hRA
    refine ⟨hR,hRk.1,?_⟩
    have hik : q<(R i k:ℝ) := (hp hRk.1 i k).mpr (hT.2.1 k hk).symm
    have hkr : q<(R k r:ℝ) := hqt.trans_lt hRk.2
    have hh := hR.2 i r k
    rw [hR.1.1 r k] at hh
    exact (lt_min hik hkr).trans_le hh
  have hdis : Set.PairwiseDisjoint (T:Set (Fin r)) (fun k => U∩J k) := by
    intro k hk l hl hkl
    apply Set.disjoint_left.mpr
    intro R hRk hRl
    have hne : c k≠c l := fun h => hkl (hT.1 hk hl h)
    exact hne ((hc hRk.2.1 k l).mp ((lt_min hRk.2.2 hRl.2.2).trans_le (hRk.1.2 k l r)))
  have hsum : (μ:Measure OverlapArray).real A=∑ k∈T,(μ:Measure OverlapArray).real (J k) := by
    rw [← hUr A]
    have he : U∩A=⋃ k∈T,U∩J k := by ext R; simp only [A,Set.mem_inter_iff,Set.mem_iUnion]; aesop
    rw [he,measureReal_biUnion_finset hdis (fun k _ =>
      (isClosed_GramArrays.measurableSet.inter isClosed_UltrametricArrays.measurableSet).inter (hJ k))]
    exact Finset.sum_congr rfl fun k _ => hUr (J k)
  have he : {R | blockOfArray r R∈S ∧ q<(R i r:ℝ) ∧ ∀ k∈T,(R k r:ℝ)≤t}=P\A := by
    ext R
    simp only [P,A,J,E,Set.mem_ofPred_eq,Set.mem_sdiff,Set.mem_iUnion,Set.mem_preimage]
    constructor
    · rintro ⟨hE,hP,hnew⟩
      exact ⟨⟨hE,hP⟩,fun ⟨k,hk,_,hkr⟩ => (not_lt_of_ge (hnew k hk)) hkr⟩
    · rintro ⟨⟨hE,hP⟩,hnot⟩
      exact ⟨hE,hP,fun k hk => le_of_not_gt (fun h => hnot ⟨k,hk,hE,h⟩)⟩
  have hdiff : (μ:Measure OverlapArray).real (P\A)=
      (μ:Measure OverlapArray).real P-(μ:Measure OverlapArray).real A := by
    rw [← hUr (P\A)]
    have hh : U∩(P\A)=(U∩P)\(U∩A) := by ext R; simp only [Set.mem_inter_iff,Set.mem_sdiff]; aesop
    rw [hh,measureReal_sdiff hUP ((isClosed_GramArrays.measurableSet.inter
      isClosed_UltrametricArrays.measurableSet).inter hA),hUr P,hUr A]
  rw [he,hdiff,hsum]
  have hjoin := GG_join_on_block hgg hS p q hp i
  have hjoins := Finset.sum_congr (s₁:=T) (s₂:=T) rfl
    (fun k _ => GG_join_on_block hgg hS c t hc k)
  rw [← Finset.mul_sum] at hjoins
  simp_rw [sub_mul] at hjoins
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,Finset.sum_const,nsmul_eq_mul] at hjoins
  have hcount : (∑ k∈T,(clusterCount c k:ℝ))=(clusterCount p i:ℝ) := by
    exact_mod_cast sum_parent_clusterCount hT
  rw [hcount] at hjoins
  change (r:ℝ)*(μ:Measure OverlapArray).real P=_ at hjoin
  change (r:ℝ)*(∑ k∈T,(μ:Measure OverlapArray).real (J k))=_ at hjoins
  change (r:ℝ)*((μ:Measure OverlapArray).real P-∑ k∈T,(μ:Measure OverlapArray).real (J k))=_
  linear_combination hjoin-hjoins

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma log_power_affine_derivative {a : ℝ} (ha : a≠0) {n : ℕ} (hn : 0<n) :
    iteratedDeriv n (fun z : ℝ => a⁻¹*Real.log ((1-z)^a)) 0= -((n-1).factorial:ℝ) := by
  have he : (fun z : ℝ => a⁻¹*Real.log ((1-z)^a))=ᶠ[𝓝 0] (fun z => Real.log (1-z)) := by
    filter_upwards [(isOpen_Iio.mem_nhds (show (0:ℝ)<1 by norm_num))] with z hz
    rw [Real.log_rpow (sub_pos.mpr hz)]
    field_simp
  rw [he.iteratedDeriv_eq n]
  have ht := congrFun (iteratedDeriv_comp_const_sub n Real.log 1) 0
  rw [ht]
  simp only [sub_zero,smul_eq_mul,iteratedDeriv_log_one hn]
  have hs : (-1:ℝ)^n*(-1:ℝ)^n=1 := by rw [← mul_pow]; norm_num
  calc
    (-1:ℝ)^n*(-(-1:ℝ)^n*((n-1).factorial:ℝ))=
      -((-1:ℝ)^n*(-1:ℝ)^n)*((n-1).factorial:ℝ) := by ring
    _ = _ := by rw [hs]; ring

 

lemma ordered_partition_mass {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (ha : overlapDiscount μ q≠0) {n : ℕ} (hn : 0<n) :
    (∑ c : OrderedFinpartition n,(μ:Measure OverlapArray).real (partitionEvent (orderedCode c) q))=1 := by
  have h := GG_marked_log_derivative hG hgg hu hq ha (fun _ : Fin 1 => 1) (fun _ => 1)
    (by simp) hn
  have ht : finiteMarkTransform (overlapDiscount μ q) (fun _ : Fin 1 => 1) (fun _ => 1)=
      (fun z : ℝ => (1-z)^(overlapDiscount μ q)) := by
    funext z
    simp [finiteMarkTransform]
  rw [ht,log_power_affine_derivative ha hn] at h
  simp only [orderedMarkedMoment,finiteMarkMoment,one_pow,Fin.sum_univ_one,
    Finset.prod_const_one,mul_one] at h
  have hf : ((n-1).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact (mul_left_cancel₀ (neg_ne_zero.mpr hf) (by simpa using h.symm))

lemma ordered_partSize_sum {n : ℕ} (c : OrderedFinpartition n) : ∑ j,c.partSize j=n := by
  have h := c.sum_sigma_eq_sum (fun _ : Fin n => (1:ℕ))
  simpa using h

variable {ι : Type*} [Fintype ι]
lemma finiteMarkMoment_nonneg (w x : ι → ℝ) (hw : ∀ i,0≤w i) (hx : ∀ i,0≤x i) (n : ℕ) :
    0≤finiteMarkMoment w x n := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (pow_nonneg (hx i) n)

lemma finiteMarkMoment_le {w x : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {v : ℝ} (hx : ∀ i,0≤x i ∧ x i≤v) (n : ℕ) : finiteMarkMoment w x n≤v^n := by
  calc
    _ ≤ ∑ i,w i*v^n := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hx i).1 (hx i).2 n) (hw i)
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

lemma orderedMarkedMoment_nonneg (μ : ProbabilityMeasure OverlapArray) (q : ℝ)
    {moments : ℕ → ℝ} (hm : ∀ n,0 ≤ moments n) (n : ℕ) :
    0≤orderedMarkedMoment μ q moments n := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg measureReal_nonneg (Finset.prod_nonneg fun _ _ => hm _)

lemma orderedMarkedMoment_le {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (ha : overlapDiscount μ q≠0) {n : ℕ} (hn : 0<n)
    {v : ℝ} {moments : ℕ → ℝ} (hm : ∀ k,0 ≤ moments k ∧ moments k≤v^k) :
    orderedMarkedMoment μ q moments n≤v^n := by
  have hp (c : OrderedFinpartition n) : (∏ j,moments (c.partSize j))≤v^n := by
    calc
      _ ≤ ∏ j,v^(c.partSize j) := Finset.prod_le_prod₀ (fun j _ => (hm _).1) (fun j _ => (hm _).2)
      _ = v^(∑ j,c.partSize j) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = _ := by rw [ordered_partSize_sum]
  change (∑ c : OrderedFinpartition n,_ )≤_
  calc
    _ ≤ ∑ c : OrderedFinpartition n,(μ:Measure OverlapArray).real (partitionEvent (orderedCode c) q)*v^n :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hp c) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul,ordered_partition_mass hG hgg hu hq ha hn,one_mul]

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

variable {ι : Type*} [Fintype ι]
def markedLogSeries (μ : ProbabilityMeasure OverlapArray) (q : ℝ) (w x : ι → ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => -orderedMarkedMoment μ q (finiteMarkMoment w x) n/(n:ℝ))

lemma markedLog_hasFPowerSeriesAt {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (ha : overlapDiscount μ q≠0)
    (w x : ι → ℝ) (hw : ∑ i,w i=1) :
    HasFPowerSeriesAt (fun z => (overlapDiscount μ q)⁻¹*
      Real.log (finiteMarkTransform (overlapDiscount μ q) w x z)) (markedLogSeries μ q w x) 0 := by
  have hz := finiteMarkTransform_zero (overlapDiscount μ q) w x hw
  have hf : ContDiffAt ℝ ω (fun z => (overlapDiscount μ q)⁻¹*
      Real.log (finiteMarkTransform (overlapDiscount μ q) w x z)) 0 := by
    apply contDiffAt_const.mul
    apply (Real.contDiffAt_log.mpr _).comp 0 (contDiffAt_mark _ w x ω)
    rw [hz]; norm_num
  have h := hf.analyticAt.hasFPowerSeriesAt
  have he : (fun n => iteratedDeriv n (fun z => (overlapDiscount μ q)⁻¹*
      Real.log (finiteMarkTransform (overlapDiscount μ q) w x z)) 0/(n.factorial:ℝ))=
      (fun n => -orderedMarkedMoment μ q (finiteMarkMoment w x) n/(n:ℝ)) := by
    funext n
    by_cases hn : n=0
    · subst n
      simp [hz]
    · have hn' := Nat.pos_of_ne_zero hn
      rw [GG_marked_log_derivative hG hgg hu hq ha w x hw hn']
      have hf : (n.factorial:ℝ)=(n:ℝ)*((n-1).factorial:ℝ) := by
        exact_mod_cast (Nat.mul_factorial_pred hn).symm
      have hf0 : ((n-1).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
      rw [hf]
      field_simp
  rw [he] at h
  exact h

lemma markedLogSeries_radius {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (ha : overlapDiscount μ q≠0)
    {w x : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hx : ∀ i,0≤x i ∧ x i≤1) :
    (1:ℝ≥0∞)≤(markedLogSeries μ q w x).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound (C:=1) (r:=1)
  intro n
  simp only [markedLogSeries,FormalMultilinearSeries.ofScalars,norm_smul,
    NNReal.coe_one,one_pow,mul_one,Real.norm_eq_abs,abs_div,abs_neg]
  rw [show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · simp [hn]
  have hn' := Nat.pos_of_ne_zero hn
  have hm : ∀ k,0≤finiteMarkMoment w x k ∧ finiteMarkMoment w x k≤(1:ℝ)^k := fun k =>
    ⟨finiteMarkMoment_nonneg w x hw (fun i => (hx i).1) k,finiteMarkMoment_le hw hs hx k⟩
  have hnon := orderedMarkedMoment_nonneg μ q (fun k => (hm k).1) n
  have hle := orderedMarkedMoment_le hG hgg hu hq ha hn' hm
  simp only [one_pow] at hle
  rw [abs_of_nonneg hnon]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn'
  have hnorm : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ‖≤1 := by
    apply le_trans ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
    norm_num
  calc
    _ ≤ (1:ℝ)/(n:ℝ)*1 := mul_le_mul (div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)) hnorm
      (norm_nonneg _) (by positivity)
    _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by positivity)).mpr hn1

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι]

lemma affine_mark_pos {x z : ℝ} (hx : 0≤x ∧ x≤1) (hz : |z|<1) : 0<1-z*x := by
  have h : z*x≤|z| := calc
    z*x ≤ |z| *x := mul_le_mul_of_nonneg_right (le_abs_self _) hx.1
    _ ≤ |z| *1 := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
    _ = _ := mul_one _
  linarith

lemma finiteMarkTransform_pos (a : ℝ) {w x : ι → ℝ}
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hx : ∀ i,0≤x i ∧ x i≤1)
    {z : ℝ} (hz : |z|<1) : 0<finiteMarkTransform a w x z := by
  have hex : ∃ i,0<w i := by
    by_contra! h
    have hnon := Finset.sum_nonpos (s:=Finset.univ) (fun i _ => h i)
    rw [hs] at hnon
    linarith
  obtain ⟨i,hi⟩ := hex
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (hw i) (Real.rpow_nonneg (le_of_lt (affine_mark_pos (hx i) hz)) a)
  · exact ⟨i,Finset.mem_univ _,mul_pos hi (Real.rpow_pos_of_pos (affine_mark_pos (hx i) hz) a)⟩

lemma contDiffAt_mark_of_abs_lt (a : ℝ) {w x : ι → ℝ}
    (hx : ∀ i,0≤x i ∧ x i≤1) {z : ℝ} (hz : |z|<1) (n : ℕ∞ω) :
    ContDiffAt ℝ n (finiteMarkTransform a w x) z := by
  apply ContDiffAt.sum
  intro i _
  apply contDiffAt_const.mul
  apply ContDiffAt.rpow_const_of_ne
  · fun_prop
  · exact ne_of_gt (affine_mark_pos (hx i) hz)

 

theorem GG_marked_log_identity {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {q : ℝ} (hq : q<1) (ha : overlapDiscount μ q≠0)
    {w x : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hx : ∀ i,0≤x i ∧ x i≤1)
    {z : ℝ} (hz : |z|<1) :
    (overlapDiscount μ q)⁻¹*Real.log (finiteMarkTransform (overlapDiscount μ q) w x z)=
      (markedLogSeries μ q w x).sum z := by
  let f : ℝ → ℝ := fun z => (overlapDiscount μ q)⁻¹*
    Real.log (finiteMarkTransform (overlapDiscount μ q) w x z)
  let p := markedLogSeries μ q w x
  have hr : (1:ℝ≥0∞)≤p.radius := markedLogSeries_radius hG hgg hu hq ha hw hs hx
  have hf : AnalyticOnNhd ℝ f (Set.Ioo (-1) 1) := by
    intro t ht
    have ht' : |t|<1 := abs_lt.mpr ht
    apply ContDiffAt.analyticAt
    apply contDiffAt_const.mul
    exact (Real.contDiffAt_log.mpr (ne_of_gt (finiteMarkTransform_pos _ hw hs hx ht'))).comp t
      (contDiffAt_mark_of_abs_lt _ hx ht' ω)
  have hp : AnalyticOnNhd ℝ p.sum (Set.Ioo (-1) 1) := by
    intro t ht
    apply p.analyticOnNhd
    apply lt_of_lt_of_le _ hr
    rw [edist_zero_right,← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr (abs_lt.mpr ht)
  have he : f=ᶠ[𝓝 0] p.sum := by
    filter_upwards [(markedLog_hasFPowerSeriesAt hG hgg hu hq ha w x hs).eventually_hasSum] with t ht
    simpa only [zero_add, f, p, FormalMultilinearSeries.sum] using ht.tsum_eq.symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hp isPreconnected_Ioo (by constructor <;> norm_num)
    he (abs_lt.mp hz)

end SKCavity

end

end OAI
