import Mathlib
import OAI.Probability.JammingConcavity.WeightedMarkedFactorial

namespace OAI

/-! R P C Sample Pattern. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def PatternIndex : (k : ℕ) → ReplicaPattern k → Type
  | 0,n => Fin n
  | k+1,bs => (i : Fin (List.length bs)) × PatternIndex k (List.get bs i)

instance patternIndexFintype : (k : ℕ) → (b : ReplicaPattern k) → Fintype (PatternIndex k b)
  | 0,n => by
      change ℕ at n
      exact inferInstanceAs (Fintype (Fin n))
  | k+1,bs => by
      change List (ReplicaPattern k) at bs
      letI := fun i : Fin (List.length bs) => patternIndexFintype k (List.get bs i)
      exact inferInstanceAs (Fintype ((i : Fin (List.length bs)) × PatternIndex k (List.get bs i)))

def RPCSamplePattern : (k : ℕ) → (b : ReplicaPattern k) → (PatternIndex k b → CascadePath k) → Prop
  | 0,_,_ => True
  | k+1,bs,x => ∃ a : Fin (List.length bs) → CloudLabel, Function.Injective a ∧
      ∀ i : Fin (List.length bs), (∀ j : PatternIndex k (List.get bs i), (x ⟨i,j⟩).1 = a i) ∧
        RPCSamplePattern k (List.get bs i) (fun j => (x ⟨i,j⟩).2)

def sampledPatternProbability (ms : List ℝ) (b : ReplicaPattern ms.length)
    (ω : CascadeTree ms.length) : ℝ≥0∞ :=
  (Measure.pi (fun _ : PatternIndex ms.length b => cascadeLeafLaw ms ω))
    {x | RPCSamplePattern ms.length b x}

def RPCSamplePatternStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
    (∀ᵐ ω ∂cascadeLaw ms, ∀ b : ReplicaPattern ms.length, ValidReplicaPattern ms.length b →
      sampledPatternProbability ms b ω = rpcLabelPatternWeight ms b ω) ∧
    (∀ η : ℝ, 0 ≤ η → (∀ m ∈ ms, η < m) →
      ∀ b : ReplicaPattern ms.length, ValidReplicaPattern ms.length b →
      (∫⁻ ω, ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*sampledPatternProbability ms b ω ∂cascadeLaw ms) /
        ENNReal.ofReal (∫ ω, (cascadeTotal ms ω).toReal^η ∂cascadeLaw ms) =
          ENNReal.ofReal (rpcPatternProduct ms η b))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def singletonReplicaPattern : (k : ℕ) → ReplicaPattern k
  | 0 => (1 : ℕ)
  | k+1 => [singletonReplicaPattern k]

 

inductive RPCInsertion : (ms : List ℝ) → ℝ → ReplicaPattern ms.length →
    ReplicaPattern ms.length → ℝ → Prop
  | leaf (η : ℝ) (n : ℕ) : RPCInsertion [] η n (n+1) ((n:ℝ)-η)
  | newChild (m : ℝ) (ms : List ℝ) (η : ℝ) (bs : List (ReplicaPattern ms.length)) :
      RPCInsertion (m::ms) η bs (bs ++ [singletonReplicaPattern ms.length])
        ((bs.length:ℝ)*m-η)
  | oldChild (m : ℝ) (ms : List ℝ) (η : ℝ)
      (pre post : List (ReplicaPattern ms.length)) (b b' : ReplicaPattern ms.length) (w : ℝ)
      (h : RPCInsertion ms m b b' w) :
      RPCInsertion (m::ms) η (pre ++ b::post) (pre ++ b'::post) w

def RPCPredictiveStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ η : ℝ, 0 ≤ η → η < 1 → (∀ m ∈ ms, η < m) →
  ∀ (b b' : ReplicaPattern ms.length) (w : ℝ),
    ValidReplicaPattern ms.length b → RPCInsertion ms η b b' w →
    ValidReplicaPattern ms.length b' ∧
    replicaPatternSize ms.length b' = replicaPatternSize ms.length b + 1 ∧
    0 < w ∧
    rpcPatternProduct ms η b' = rpcPatternProduct ms η b *
      (w / ((replicaPatternSize ms.length b:ℝ)-η)) ∧
    (∫⁻ ω, ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*sampledPatternProbability ms b' ω ∂cascadeLaw ms) /
      ENNReal.ofReal (∫ ω, (cascadeTotal ms ω).toReal^η ∂cascadeLaw ms) =
      ENNReal.ofReal (rpcPatternProduct ms η b * (w / ((replicaPatternSize ms.length b:ℝ)-η)))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma partitionProduct_add_new (m η : ℝ) (hη : η < 1) (ns : List ℕ)
    (hl : 0 < ns.length) (hs : 0 < ns.sum) :
    partitionProduct m η (ns ++ [1]) = partitionProduct m η ns *
      (((ns.length:ℝ)*m-η)/((ns.sum:ℝ)-η)) := by
  have hden := (partition_denominator_pos hη ns.sum).ne'
  have hn : (ns.sum:ℝ)-η ≠ 0 := by
    have : (1:ℝ) ≤ ns.sum := by exact_mod_cast hs
    linarith
  unfold partitionProduct
  simp only [List.length_append, List.length_singleton, List.sum_append, List.sum_singleton,
    List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
    Finset.Ico_self, Finset.prod_empty, mul_one]
  rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ ns.length),
    Finset.prod_Ico_succ_top (by omega : 1 ≤ ns.sum)]
  field_simp
  simp only [mul_comm m]
  ring

lemma partitionProduct_add_old (m η : ℝ) (hη : η < 1)
    (pre post : List ℕ) (n : ℕ) (hn : 0 < n) :
    partitionProduct m η (pre ++ (n+1)::post) =
      partitionProduct m η (pre ++ n::post) *
        (((n:ℝ)-m)/(((pre ++ n::post).sum:ℝ)-η)) := by
  have hden := (partition_denominator_pos hη (pre ++ n::post).sum).ne'
  have hs : 0 < (pre ++ n::post).sum := by simp only [List.sum_append,List.sum_cons]; omega
  have hsum : (pre ++ (n+1)::post).sum = (pre ++ n::post).sum + 1 := by
    simp only [List.sum_append,List.sum_cons]; omega
  have hlen : (pre ++ (n+1)::post).length = (pre ++ n::post).length := by simp
  have hN : ((pre ++ n::post).sum:ℝ)-η ≠ 0 := by
    have : (1:ℝ) ≤ (pre ++ n::post).sum := by exact_mod_cast hs
    linarith
  unfold partitionProduct
  rw [hsum,hlen,Finset.prod_Ico_succ_top (by omega : 1 ≤ (pre ++ n::post).sum)]
  simp only [List.map_append,List.map_cons,List.prod_append,List.prod_cons]
  rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ n)]
  field_simp
  simp only [mul_comm m]
  ring

lemma singletonReplicaPattern_size (k : ℕ) : replicaPatternSize k (singletonReplicaPattern k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [singletonReplicaPattern,replicaPatternSize] using ih

lemma singletonReplicaPattern_valid (k : ℕ) : ValidReplicaPattern k (singletonReplicaPattern k) := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    change [singletonReplicaPattern k] ≠ [] ∧ ∀ b ∈ [singletonReplicaPattern k], ValidReplicaPattern k b
    refine ⟨by simp, ?_⟩
    intro b hb
    have := List.mem_singleton.mp hb
    subst b
    exact ih

lemma singletonReplicaPattern_product (ms : List ℝ) (η : ℝ) :
    rpcPatternProduct ms η (singletonReplicaPattern ms.length) = 1 := by
  induction ms generalizing η with
  | nil => rfl
  | cons m ms ih =>
    simp [singletonReplicaPattern,rpcPatternProduct,singletonReplicaPattern_size,
      partitionProduct,ih]
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma pi_grouping {I P : Type*} [Fintype I] [Countable P]
    [MeasurableSpace P] [MeasurableSingletonClass P] (J : I → Type*)
    [∀ i, Fintype (J i)] (μ : Measure P) [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : (i : I) × J i => μ)).map
        (fun x i j => x ⟨i,j⟩) =
      Measure.pi (fun i : I => Measure.pi (fun _ : J i => μ)) := by
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun (x : ((i : I) × J i) → P) i j => x ⟨i,j⟩) ⁻¹' {f} =
      {fun p : (i : I) × J i => f p.1 p.2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
    exact ⟨fun h p => h p.1 p.2, fun h i j => h ⟨i,j⟩⟩
  rw [he, Measure.pi_singleton, Measure.pi_singleton]
  simp only [Measure.pi_singleton, Fintype.prod_sigma]

 
lemma pi_fixed_root {I P L A : Type*} [Fintype I] [Countable P] [Countable A]
    [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (e : P ≃ L × A) (μ : Measure P) (ν : Measure A)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0∞) (l : L)
    (hd : ∀ a, μ {e.symm (l,a)} = c * ν {a}) (E : Set (I → A)) :
    Measure.pi (fun _ : I => μ)
      {x | (∀ i, (e (x i)).1 = l) ∧ (fun i => (e (x i)).2) ∈ E} =
      c ^ Fintype.card I * Measure.pi (fun _ : I => ν) E := by
  let T : (I → P) → (I → A) := fun x i => (e (x i)).2
  let R : Set (I → P) := {x | ∀ i, (e (x i)).1 = l}
  have hm : ((Measure.pi (fun _ : I => μ)).restrict R).map T =
      c ^ Fintype.card I • Measure.pi (fun _ : I => ν) := by
    apply Measure.ext_of_singleton
    intro y
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      Measure.restrict_apply (measurable_of_countable _ (measurableSet_singleton _))]
    have he : T ⁻¹' {y} ∩ R = {fun i => e.symm (l,y i)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, R, Set.mem_ofPred_eq, T]
      constructor
      · rintro ⟨hy,hr⟩
        funext i
        apply e.injective
        rw [e.apply_symm_apply]
        exact Prod.ext (hr i) (congrFun hy i)
      · intro hx
        subst x
        simp
    rw [he, Measure.pi_singleton, Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]
    simp_rw [hd]
    rw [Finset.prod_mul_distrib]
    simp
  have hs : MeasurableSet E := Set.to_countable E |>.measurableSet
  have H := congrArg (fun τ : Measure (I → A) => τ E) hm
  rw [Measure.map_apply (measurable_of_countable _) hs,
    Measure.restrict_apply ((measurable_of_countable T) hs),
    Measure.smul_apply, smul_eq_mul] at H
  have he : T ⁻¹' E ∩ R =
      {x | (∀ i, (e (x i)).1 = l) ∧ (fun i => (e (x i)).2) ∈ E} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, T, R]
    exact and_comm
  rwa [he] at H

lemma pi_distinct_roots {I P L A : Type*} [Fintype I] [Countable P] [Countable L]
    [Countable A] [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (J : I → Type*) [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    (e : P ≃ L × A) (μ : Measure P) [IsProbabilityMeasure μ]
    (E : (i : I) → Set (J i → A)) :
    Measure.pi (fun _ : (i : I) × J i => μ)
      {x | ∃ a : I → L, Function.Injective a ∧ ∀ i,
        (∀ j, (e (x ⟨i,j⟩)).1 = a i) ∧ (fun j => (e (x ⟨i,j⟩)).2) ∈ E i} =
      ∑' a : {a : I → L // Function.Injective a}, ∏ i : I,
        Measure.pi (fun _ : J i => μ)
          {x | (∀ j, (e (x j)).1 = a.1 i) ∧ (fun j => (e (x j)).2) ∈ E i} := by
  let C (a : {a : I → L // Function.Injective a}) : Set ((i : I) → J i → P) :=
    univ.pi (fun i => {x | (∀ j, (e (x j)).1 = a.1 i) ∧ (fun j => (e (x j)).2) ∈ E i})
  have hc (a) : MeasurableSet (C a) := Set.to_countable (C a) |>.measurableSet
  have hd : Pairwise (fun a b => Disjoint (C a) (C b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    apply hab
    apply Subtype.ext
    funext i
    let j : J i := Classical.choice (inferInstance : Nonempty (J i))
    exact ((hxa i (mem_univ i)).1 j).symm.trans ((hxb i (mem_univ i)).1 j)
  have hs : MeasurableSet (⋃ a, C a) := MeasurableSet.iUnion hc
  have he : (fun (x : ((i : I) × J i) → P) i j => x ⟨i,j⟩) ⁻¹' (⋃ a, C a) =
      {x | ∃ a : I → L, Function.Injective a ∧ ∀ i,
        (∀ j, (e (x ⟨i,j⟩)).1 = a i) ∧ (fun j => (e (x ⟨i,j⟩)).2) ∈ E i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, C, Set.mem_univ_pi, Set.mem_ofPred_eq]
    exact ⟨fun ⟨a,ha⟩ => ⟨a.1,a.2,ha⟩, fun ⟨a,ha,hx⟩ => ⟨⟨a,ha⟩,hx⟩⟩
  rw [← he, ← Measure.map_apply (measurable_of_countable _) hs, pi_grouping J μ,
    measure_iUnion hd hc]
  apply tsum_congr
  intro a
  exact Measure.pi_pi _ _
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def GoodCloudLabels {A : Type*} (ω : PointCloud A) (xs : List CloudLabel) {n : ℕ}
    (a : Fin n → CloudLabel) : Prop :=
  Function.Injective a ∧ ∀ i, (a i).2 < (ω (a i).1).1 ∧ a i ∉ xs

lemma goodCloudLabels_cons {A : Type*} (ω : PointCloud A) (xs : List CloudLabel)
    {n : ℕ} (i : CloudLabel) (a : Fin n → CloudLabel) :
    GoodCloudLabels ω xs (Fin.cons i a) ↔
      (i.2 < (ω i.1).1 ∧ i ∉ xs) ∧ GoodCloudLabels ω (i::xs) a := by
  simp only [GoodCloudLabels, Fin.cons_injective_iff, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, List.mem_cons, not_or]
  constructor
  · rintro ⟨⟨h0,ha⟩,hi,ht⟩
    refine ⟨hi,ha,fun j => ⟨(ht j).1,?_,(ht j).2⟩⟩
    intro hj
    exact h0 ⟨j,hj⟩
  · rintro ⟨hi,ha,ht⟩
    refine ⟨⟨?_,ha⟩,hi,fun j => ⟨(ht j).1,(ht j).2.2⟩⟩
    rintro ⟨j,hj⟩
    exact (ht j).2.1 hj

lemma labelCloudIntegral_tuple {A : Type*} (ω : PointCloud A)
    (fs : List (CloudLabel → ℝ≥0∞)) (xs : List CloudLabel) :
    labelCloudIntegral fs ω xs = ∑' a : Fin fs.length → CloudLabel,
      if GoodCloudLabels ω xs a then ∏ i : Fin fs.length, (fs.get i) (a i) else 0 := by
  induction fs generalizing xs with
  | nil => simp [labelCloudIntegral, GoodCloudLabels, Function.Injective]
  | cons f fs ih =>
    have ht : (∑' a : Fin (f::fs).length → CloudLabel,
        if GoodCloudLabels ω xs a then ∏ i : Fin (f::fs).length, ((f::fs).get i) (a i) else 0) =
        ∑' i : CloudLabel, ∑' a : Fin fs.length → CloudLabel,
          if (i.2 < (ω i.1).1 ∧ i ∉ xs) ∧ GoodCloudLabels ω (i::xs) a then
            f i * ∏ j : Fin fs.length, (fs.get j) (a j) else 0 := by
      simp only [List.length_cons]
      rw [← (Fin.consEquiv (fun _ : Fin (fs.length+1) => CloudLabel)).tsum_eq,
        ENNReal.tsum_prod']
      apply tsum_congr
      intro i
      apply tsum_congr
      intro a
      change (if GoodCloudLabels ω xs (Fin.cons i a) then
        ∏ j : Fin (fs.length+1), ((f::fs).get j) ((Fin.cons (α := fun _ : Fin (fs.length+1) => CloudLabel) i a) j) else 0) = _
      rw [goodCloudLabels_cons]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.get_eq_getElem,
        Fin.val_zero, Fin.val_succ, List.getElem_cons_succ]
      all_goals rfl
    rw [ht]
    simp only [labelCloudIntegral]
    apply tsum_congr
    intro i
    by_cases hi : i.2 < (ω i.1).1 ∧ i ∉ xs
    · simp only [hi, not_false_eq_true, true_and, ite_true, ih]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      split_ifs <;> simp
    · simp [hi]

lemma labelCloudIntegral_injective {A : Type*} (ω : PointCloud A)
    (fs : List (CloudLabel → ℝ≥0∞)) :
    labelCloudIntegral fs ω [] =
      ∑' a : {a : Fin fs.length → CloudLabel // Function.Injective a},
        ∏ i : Fin fs.length, if (a.1 i).2 < (ω (a.1 i).1).1 then (fs.get i) (a.1 i) else 0 := by
  rw [labelCloudIntegral_tuple]
  have hs := tsum_subtype {a : Fin fs.length → CloudLabel | Function.Injective a}
    (fun a => ∏ i : Fin fs.length, if (a i).2 < (ω (a i).1).1 then fs.get i (a i) else 0)
  refine Eq.trans ?_ hs.symm
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  apply tsum_congr
  intro a
  by_cases ha : Function.Injective a
  · simp only [GoodCloudLabels, List.not_mem_nil, not_false_eq_true, and_true, ha, true_and, ite_true]
    by_cases ht : ∀ i, (a i).2 < (ω (a i).1).1
    · simp only [ite_eq_left ht]
      apply Finset.prod_congr rfl
      intro i hi
      rw [ite_eq_left (ht i)]
    · simp only [ite_eq_right ht]
      obtain ⟨i,hi⟩ := not_forall.mp ht
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  · simp [GoodCloudLabels,ha]

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma patternIndex_card (k : ℕ) (b : ReplicaPattern k) :
    Fintype.card (PatternIndex k b) = replicaPatternSize k b := by
  induction k with
  | zero => exact Fintype.card_fin b
  | succ k ih =>
    change List (ReplicaPattern k) at b
    change Fintype.card ((i : Fin (List.length b)) × PatternIndex k (List.get b i)) = _
    rw [Fintype.card_sigma]
    simp_rw [ih]
    change (∑ i : Fin b.length, replicaPatternSize k (b.get i)) = (b.map (replicaPatternSize k)).sum
    simpa only [List.ofFn_getElem_eq_map, List.get_eq_getElem] using
      (Fin.sum_ofFn (fun i : Fin b.length => replicaPatternSize k (b.get i))).symm

lemma patternIndex_nonempty (k : ℕ) (b : ReplicaPattern k) (hb : ValidReplicaPattern k b) :
    Nonempty (PatternIndex k b) := by
  apply Fintype.card_pos_iff.mp
  rw [patternIndex_card]
  exact replicaPatternSize_pos k b hb

lemma labelCloudIntegral_map {A B : Type*} (ω : PointCloud A)
    (bs : List B) (f : B → CloudLabel → ℝ≥0∞) :
    labelCloudIntegral (bs.map f) ω [] =
      ∑' a : {a : Fin bs.length → CloudLabel // Function.Injective a},
        ∏ i : Fin bs.length, if (a.1 i).2 < (ω (a.1 i).1).1 then f (bs.get i) (a.1 i) else 0 := by
  have h := labelCloudIntegral_injective ω (bs.map f)
  simp only [List.get_eq_getElem, List.getElem_map] at h
  have hc (n : ℕ) (hn : n = bs.length) :
      (∑' a : {a : Fin n → CloudLabel // Function.Injective a},
        ∏ i : Fin n, if (a.1 i).2 < (ω (a.1 i).1).1 then f (bs.get (Fin.cast hn i)) (a.1 i) else 0) =
      ∑' a : {a : Fin bs.length → CloudLabel // Function.Injective a},
        ∏ i : Fin bs.length, if (a.1 i).2 < (ω (a.1 i).1).1 then f (bs.get i) (a.1 i) else 0 := by
    subst n
    rfl
  exact h.trans (hc _ (List.length_map f))

lemma cascadeLeafLaw_child_density (ms : List ℝ) (m : ℝ)
    (ω : CascadeTree (m::ms).length) (i : CloudLabel)
    (hω : 0 < cascadeTotal (m::ms) ω ∧ cascadeTotal (m::ms) ω < ∞)
    (hc : 0 < cascadeTotal ms (cloudLabelPoint ω i).2 ∧
      cascadeTotal ms (cloudLabelPoint ω i).2 < ∞) (ℓ : CascadePath ms.length) :
    cascadeLeafLaw (m::ms) ω {((i,ℓ) : CascadePath (m::ms).length)} =
      (if i.2 < (ω i.1).1 then
        ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
          cascadeTotal ms (cloudLabelPoint ω i).2 / cascadeTotal (m::ms) ω else 0) *
        cascadeLeafLaw ms (cloudLabelPoint ω i).2 {ℓ} := by
  erw [cascadeLeafLaw_singleton_good _ _ hω, cascadeLeafLaw_singleton_good _ _ hc]
  by_cases hi : i.2 < (ω i.1).1
  · simp only [cascadePathWeight, hi, ite_true, div_eq_mul_inv]
    change _ = (ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
      cascadeTotal ms (cloudLabelPoint ω i).2 * (cascadeTotal (m::ms) ω)⁻¹) *
      (cascadePathWeight ms (cloudLabelPoint ω i).2 ℓ * (cascadeTotal ms (cloudLabelPoint ω i).2)⁻¹)
    rw [show (ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
        cascadeTotal ms (cloudLabelPoint ω i).2 * (cascadeTotal (m::ms) ω)⁻¹) *
        (cascadePathWeight ms (cloudLabelPoint ω i).2 ℓ * (cascadeTotal ms (cloudLabelPoint ω i).2)⁻¹) =
        (ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
          cascadePathWeight ms (cloudLabelPoint ω i).2 ℓ * (cascadeTotal (m::ms) ω)⁻¹) *
        (cascadeTotal ms (cloudLabelPoint ω i).2 * (cascadeTotal ms (cloudLabelPoint ω i).2)⁻¹) by ac_rfl,
      ENNReal.mul_inv_cancel hc.1.ne' hc.2.ne, mul_one]
    rfl
  · simp [cascadePathWeight, hi]

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma ofReal_toReal_neg_nat (T : ℝ≥0∞) (hT : 0 < T ∧ T < ∞) (n : ℕ) :
    ENNReal.ofReal (T.toReal ^ (-(n : ℝ))) = T⁻¹ ^ n := by
  rw [← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hT.1.ne' hT.2.ne),
    ENNReal.ofReal_toReal hT.2.ne, ENNReal.rpow_neg, ENNReal.rpow_natCast,
    ENNReal.inv_pow]

lemma sampledPatternProbability_cons (ms : List ℝ) (m : ℝ)
    (bs : ReplicaPattern (m::ms).length) (hb : ValidReplicaPattern (m::ms).length bs)
    (ω : CascadeTree (m::ms).length)
    (hω : 0 < cascadeTotal (m::ms) ω ∧ cascadeTotal (m::ms) ω < ∞)
    (hc : ∀ i : CloudLabel, 0 < cascadeTotal ms (cloudLabelPoint ω i).2 ∧
      cascadeTotal ms (cloudLabelPoint ω i).2 < ∞)
    (hp : ∀ (i : CloudLabel) (b : ReplicaPattern ms.length), ValidReplicaPattern ms.length b →
      sampledPatternProbability ms b (cloudLabelPoint ω i).2 =
        rpcLabelPatternWeight ms b (cloudLabelPoint ω i).2) :
    sampledPatternProbability (m::ms) bs ω = rpcLabelPatternWeight (m::ms) bs ω := by
  change List (ReplicaPattern ms.length) at bs
  change bs ≠ [] ∧ ∀ b ∈ bs, ValidReplicaPattern ms.length b at hb
  let J (i : Fin bs.length) := PatternIndex ms.length (bs.get i)
  let (i : Fin bs.length) : Nonempty (J i) := patternIndex_nonempty _ _ (hb.2 _ (bs.get_mem i))
  let := cascadeLeafLaw_probability (m::ms) ω
  have hgroup := pi_distinct_roots (P := CascadePath (m::ms).length) J
    (show CascadePath (m::ms).length ≃ CloudLabel × CascadePath ms.length from Equiv.refl _)
    (cascadeLeafLaw (m::ms) ω) (fun i => {x | RPCSamplePattern ms.length (bs.get i) x})
  change sampledPatternProbability (m::ms) bs ω = _ at hgroup
  rw [hgroup]
  have hblock (a : CloudLabel) (i : Fin bs.length) :
      Measure.pi (fun _ : J i => cascadeLeafLaw (m::ms) ω)
        {x | (∀ j, (x j).1 = a) ∧ RPCSamplePattern ms.length (bs.get i) (fun j => (x j).2)} =
      (cascadeTotal (m::ms) ω)⁻¹ ^ replicaPatternSize ms.length (bs.get i) *
        (if a.2 < (ω a.1).1 then
          (ENNReal.ofReal ((cloudLabelPoint ω a).1^(-1/m)) * cascadeTotal ms (cloudLabelPoint ω a).2)^
            replicaPatternSize ms.length (bs.get i) * rpcLabelPatternWeight ms (bs.get i) (cloudLabelPoint ω a).2
        else 0) := by
    let := cascadeLeafLaw_probability ms (cloudLabelPoint ω a).2
    have H := pi_fixed_root (I := J i) (P := CascadePath (m::ms).length)
      (show CascadePath (m::ms).length ≃ CloudLabel × CascadePath ms.length from Equiv.refl _)
      (cascadeLeafLaw (m::ms) ω) (cascadeLeafLaw ms (cloudLabelPoint ω a).2)
      (if a.2 < (ω a.1).1 then ENNReal.ofReal ((cloudLabelPoint ω a).1^(-1/m)) *
        cascadeTotal ms (cloudLabelPoint ω a).2 / cascadeTotal (m::ms) ω else 0) a
      (cascadeLeafLaw_child_density ms m ω a hω (hc a))
      {x | RPCSamplePattern ms.length (bs.get i) x}
    change _ = _ * sampledPatternProbability ms (bs.get i) (cloudLabelPoint ω a).2 at H
    erw [H, hp a _ (hb.2 _ (bs.get_mem i))]
    have hcard : Fintype.card (J i) = replicaPatternSize ms.length (bs.get i) := patternIndex_card _ _
    rw [hcard]
    by_cases ha : a.2 < (ω a.1).1
    · simp [ha, div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
    · simp only [ite_eq_right ha, zero_pow (ne_of_gt (replicaPatternSize_pos _ _ (hb.2 _ (bs.get_mem i)))),
        zero_mul, mul_zero]
  refine Eq.trans (tsum_congr (fun a => Finset.prod_congr rfl (fun i _ => hblock (a.1 i) i))) ?_
  simp_rw [Finset.prod_mul_distrib]
  have hsum : (∑ i : Fin bs.length, replicaPatternSize ms.length (bs.get i)) =
      replicaPatternSize (ms.length+1) bs := by
    change _ = (bs.map (replicaPatternSize ms.length)).sum
    simpa only [List.get_eq_getElem, List.ofFn_getElem_eq_map] using
      (Fin.sum_ofFn (fun i : Fin bs.length => replicaPatternSize ms.length (bs.get i))).symm
  rw [Finset.prod_pow_eq_pow_sum, hsum, ENNReal.tsum_mul_left]
  erw [rpcLabelPatternWeight, ofReal_toReal_neg_nat _ hω, labelCloudIntegral_map]

lemma sampledPatternProbability_eq_ae (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    ∀ᵐ ω ∂cascadeLaw ms, ∀ b : ReplicaPattern ms.length, ValidReplicaPattern ms.length b →
      sampledPatternProbability ms b ω = rpcLabelPatternWeight ms b ω := by
  induction ms with
  | nil =>
    exact Eventually.of_forall fun ω b hb => by
      let := cascadeLeafLaw_probability [] ω
      simp [sampledPatternProbability, RPCSamplePattern, rpcLabelPatternWeight]
  | cons m ms ih =>
    have htms := (List.pairwise_cons.mp hms).2
    have ht01 : ∀ m ∈ ms, 0 < m ∧ m < 1 := fun x hx => h01 x (List.mem_cons_of_mem _ hx)
    have hchild := ae_pointCloud_marks (cascadeLaw ms)
      (((cascadeNormalization ms htms ht01).1).and (ih htms ht01))
    filter_upwards [(cascadeNormalization (m::ms) hms h01).1, hchild] with ω hω hc
    intro bs hb
    exact sampledPatternProbability_cons ms m bs hb ω hω
      (fun i => (hc i.1 i.2).1) (fun i => (hc i.1 i.2).2)

theorem rpcSamplePattern : RPCSamplePatternStatement := by
  intro ms hms h01
  have h := sampledPatternProbability_eq_ae ms hms h01
  refine ⟨h, ?_⟩
  intro η hη hηms b hb
  have he : (fun ω => ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*sampledPatternProbability ms b ω) =ᵐ[cascadeLaw ms]
      (fun ω => ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*rpcLabelPatternWeight ms b ω) :=
    h.mono fun ω hω => by dsimp only; rw [hω b hb]
  rw [lintegral_congr_ae he]
  exact (rpcLabelSampling ms hms h01).2 η hη hηms b hb
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma rpcInsertion_properties {ms : List ℝ} {η : ℝ}
    {b b' : ReplicaPattern ms.length} {w : ℝ} (h : RPCInsertion ms η b b' w) :
    ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
    0 ≤ η → η < 1 → (∀ m ∈ ms, η < m) → ValidReplicaPattern ms.length b →
    ValidReplicaPattern ms.length b' ∧
    replicaPatternSize ms.length b' = replicaPatternSize ms.length b + 1 ∧
    0 < w ∧ rpcPatternProduct ms η b' = rpcPatternProduct ms η b *
      (w / ((replicaPatternSize ms.length b:ℝ)-η)) := by
  induction h with
  | leaf η n =>
    intro hms h01 hη hη1 hηms hn
    change 0 < n at hn
    have hpos : 0 < (n:ℝ)-η := by
      have : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine ⟨by exact Nat.succ_pos _, rfl, hpos, ?_⟩
    simp [rpcPatternProduct,replicaPatternSize,div_self hpos.ne']
  | newChild m ms η bs =>
    intro hms h01 hη hη1 hηms hb
    change bs ≠ [] ∧ ∀ b ∈ bs, ValidReplicaPattern ms.length b at hb
    have hm := h01 m (by simp)
    have hηm := hηms m (by simp)
    have hl : 0 < bs.length := List.length_pos_iff.mpr hb.1
    have hs : 0 < (bs.map (replicaPatternSize ms.length)).sum :=
      replicaPatternSize_pos (ms.length+1) bs hb
    have hw : 0 < (bs.length:ℝ)*m-η := by
      have : (1:ℝ) ≤ bs.length := by exact_mod_cast hl
      nlinarith
    refine ⟨?_, ?_, hw, ?_⟩
    · change bs ++ [singletonReplicaPattern ms.length] ≠ [] ∧
        ∀ t ∈ bs ++ [singletonReplicaPattern ms.length], ValidReplicaPattern ms.length t
      refine ⟨by simp, ?_⟩
      intro b hb'
      rcases List.mem_append.mp hb' with hb' | hb'
      · exact hb.2 b hb'
      have he := List.mem_singleton.mp hb'
      subst b
      exact singletonReplicaPattern_valid _
    · change replicaPatternSize (ms.length+1) (bs ++ [singletonReplicaPattern ms.length]) =
        replicaPatternSize (ms.length+1) bs + 1
      simp [replicaPatternSize,List.map_append,singletonReplicaPattern_size]
    · change partitionProduct m η ((bs ++ [singletonReplicaPattern ms.length]).map (replicaPatternSize ms.length)) *
        ((bs ++ [singletonReplicaPattern ms.length]).map (rpcPatternProduct ms m)).prod =
        (partitionProduct m η (bs.map (replicaPatternSize ms.length)) *
        (bs.map (rpcPatternProduct ms m)).prod) *
        (((bs.length:ℝ)*m-η)/(((bs.map (replicaPatternSize ms.length)).sum:ℝ)-η))
      simp only [List.map_append,List.map_singleton,singletonReplicaPattern_size,
        List.prod_append,List.prod_singleton,singletonReplicaPattern_product,mul_one]
      rw [partitionProduct_add_new m η hη1 _ (by simpa using hl) hs]
      simp only [List.length_map]
      ring

  | oldChild m ms η pre post b b' w h ih =>
    intro hms h01 hη hη1 hηms hb
    change pre ++ b::post ≠ [] ∧ ∀ t ∈ pre ++ b::post, ValidReplicaPattern ms.length t at hb
    have hm := h01 m (by simp)
    have htms := (List.pairwise_cons.mp hms).2
    have ht01 : ∀ m ∈ ms, 0 < m ∧ m < 1 := fun x hx => h01 x (by simp [hx])
    have hbt : ValidReplicaPattern ms.length b := hb.2 b (by simp)
    obtain ⟨hb',hs',hw,hprod⟩ := ih htms ht01 hm.1.le hm.2 (List.pairwise_cons.mp hms).1 hbt
    have hcpos : 0 < (replicaPatternSize ms.length b:ℝ)-m := by
      have : (1:ℝ) ≤ replicaPatternSize ms.length b := by
        exact_mod_cast replicaPatternSize_pos ms.length b hbt
      linarith
    have htpos : 0 < (replicaPatternSize (ms.length+1) (pre ++ b::post):ℝ)-η := by
      have : (1:ℝ) ≤ replicaPatternSize (ms.length+1) (pre ++ b::post) := by
        exact_mod_cast replicaPatternSize_pos (ms.length+1) (pre ++ b::post) hb
      linarith
    refine ⟨?_, ?_, hw, ?_⟩
    · change pre ++ b'::post ≠ [] ∧ ∀ t ∈ pre ++ b'::post, ValidReplicaPattern ms.length t
      refine ⟨by simp, ?_⟩
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hb.2 t (List.mem_append_left _ ht)
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact hb'
        · exact hb.2 t (by simp [ht])
    · change replicaPatternSize (ms.length+1) (pre ++ b'::post) =
        replicaPatternSize (ms.length+1) (pre ++ b::post) + 1
      simp only [replicaPatternSize,List.map_append,List.map_cons,List.sum_append,List.sum_cons,hs']
      omega
    · change partitionProduct m η ((pre ++ b'::post).map (replicaPatternSize ms.length)) *
          ((pre ++ b'::post).map (rpcPatternProduct ms m)).prod =
        (partitionProduct m η ((pre ++ b::post).map (replicaPatternSize ms.length)) *
          ((pre ++ b::post).map (rpcPatternProduct ms m)).prod) *
        (w / ((replicaPatternSize (ms.length+1) (pre ++ b::post):ℝ)-η))
      simp only [List.map_append,List.map_cons,List.prod_append,List.prod_cons,hs',hprod]
      rw [partitionProduct_add_old m η hη1 _ _ _ (replicaPatternSize_pos _ _ hbt)]
      have hs : ((pre.map (replicaPatternSize ms.length) ++ replicaPatternSize ms.length b ::
          post.map (replicaPatternSize ms.length)).sum:ℝ)-η =
          (replicaPatternSize (ms.length+1) (pre ++ b::post):ℝ)-η := by
        simp [replicaPatternSize]
      rw [hs]
      field_simp

theorem rpcPredictive : RPCPredictiveStatement := by
  intro ms hms h01 η hη hη1 hηms b b' w hb h
  obtain ⟨hb',hs,hw,hprod⟩ := rpcInsertion_properties h hms h01 hη hη1 hηms hb
  refine ⟨hb',hs,hw,hprod,?_⟩
  rw [(rpcSamplePattern ms hms h01).2 η hη hηms b' hb',hprod]
end MicroscopicJamming

end

end OAI
