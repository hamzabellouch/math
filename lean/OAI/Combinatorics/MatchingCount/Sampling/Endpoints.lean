import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.FinitePMF
import OAI.Combinatorics.MatchingCount.Graphs.CompleteGraph

namespace OAI

namespace MatchingFPRAS.GraphBridge

open Finset MatchingFPRAS.Enlargement MatchingFPRAS.Subdivision MatchingFPRAS.Representation MatchingFPRAS.Switching

variable {n : ℕ}

def endpoints : LogicalEdge (Fin n) ↪ (Fin n × Fin n) := ⟨Subtype.val,Subtype.val_injective⟩

def selectedEdges (s : LogicalEdge (Fin n) → Bool) : Finset (Fin n × Fin n) :=
  (univ.filter fun e => s e=true).map endpoints

lemma mem_selected (s : LogicalEdge (Fin n) → Bool) (e : LogicalEdge (Fin n)) :
    e.val ∈ selectedEdges s ↔ s e=true := by simp [selectedEdges,endpoints]

lemma selected_increasing (s : LogicalEdge (Fin n) → Bool) :
    selectedEdges s ⊆ (completeGraph n).edges := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_map.mp he
  exact mem_filter.mpr ⟨mem_univ _,f.property⟩

def edgeSelection (M : Finset (Fin n × Fin n)) (e : LogicalEdge (Fin n)) : Bool := decide (e.val∈M)

@[simp] lemma edgeSelection_selected (s : LogicalEdge (Fin n) → Bool) :
    edgeSelection (selectedEdges s)=s := by
  funext e
  apply Bool.eq_iff_iff.mpr
  simp [edgeSelection,mem_selected]

lemma selected_edgeSelection (M : Finset (Fin n × Fin n)) (hM : M⊆(completeGraph n).edges) :
    selectedEdges (edgeSelection M)=M := by
  ext e
  constructor
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    simpa [edgeSelection,endpoints] using (mem_filter.mp hf).2
  · intro he
    have hi : e.1 < e.2 := (mem_filter.mp (hM he)).2
    apply mem_map.mpr
    exact ⟨⟨e,hi⟩,mem_filter.mpr ⟨mem_univ _,by simp [edgeSelection,he]⟩,rfl⟩

lemma logical_iff_perfect (s : LogicalEdge (Fin n) → Bool) :
    LogicalHoles source target ∅ ∅ s ↔ Perfect (completeGraph n) (selectedEdges s) := by
  constructor
  · intro hs
    refine ⟨selected_increasing s,?_⟩
    intro v
    obtain ⟨e,he,hu⟩ := hs.2.2 v (by simp)
    refine ⟨e.val,⟨(mem_selected s e).mpr he.1,he.2⟩,?_⟩
    intro f hf
    have hi := (completeGraph n).increasing f (selected_increasing s hf.1)
    have hf' : s ⟨f,hi⟩=true := (mem_selected s ⟨f,hi⟩).mp hf.1
    exact congrArg Subtype.val (hu ⟨f,hi⟩ ⟨hf',hf.2⟩)
  · intro hs
    refine ⟨by simp,by simp,?_⟩
    intro v _
    obtain ⟨e,he,hu⟩ := hs.2 v
    have hi := (completeGraph n).increasing e (hs.1 he.1)
    refine ⟨⟨e,hi⟩,⟨(mem_selected s ⟨e,hi⟩).mp he.1,he.2⟩,?_⟩
    intro f hf
    exact Subtype.ext (hu f.val ⟨(mem_selected s f).mpr hf.1,hf.2⟩)

noncomputable def perfectEquiv :
    {s : LogicalEdge (Fin n) → Bool // LogicalHoles source target ∅ ∅ s} ≃
      {M : Finset (Fin n × Fin n) // Perfect (completeGraph n) M} where
  toFun s := ⟨selectedEdges s.val,(logical_iff_perfect s.val).mp s.property⟩
  invFun M := ⟨edgeSelection M.val,(logical_iff_perfect _).mpr (by
    rw [selected_edgeSelection M.val M.property.1]; exact M.property)⟩
  left_inv s := Subtype.ext (edgeSelection_selected s.val)
  right_inv M := Subtype.ext (selected_edgeSelection M.val M.property.1)

lemma selected_prod {A : Type*} [CommMonoid A] (s : LogicalEdge (Fin n) → Bool)
    (w : Fin n × Fin n → A) :
    (∏ e ∈ selectedEdges s,w e)=∏ e : LogicalEdge (Fin n),if s e then w e.val else 1 := by
  rw [selectedEdges,prod_map]
  exact prod_filter (fun e => s e=true) (fun e => w e.val)

theorem weighted_partition (w : Fin n → Fin n → ℝ) :
    (∑ M ∈ perfectMatchings (completeGraph n),∏ e ∈ M,w e.1 e.2)=partition w ∅ := by
  classical
  rw [←logical_partition_eq w ∅]
  let := Fintype.ofFinite {s : LogicalEdge (Fin n) → Bool // LogicalHoles source target ∅ ∅ s}
  let := Fintype.ofFinite {M : Finset (Fin n × Fin n) // Perfect (completeGraph n) M}
  rw [Finset.sum_subtype (perfectMatchings (completeGraph n)) (mem_perfectMatchings _)]
  unfold logicalHolePartition
  symm
  apply Fintype.sum_equiv perfectEquiv
  intro s
  rw [show (perfectEquiv s).val=selectedEdges s.val from rfl,selected_prod]
  apply prod_congr rfl
  intro e _
  simp [logicalActivity,edgeActivity,source,target,e.property]

noncomputable def rawActivity (G : GraphInput) (x : ℝ) (a b : Fin G.n) : ℝ :=
  if (min a b,max a b)∈G.edges then 1 else x

lemma rawActivity_pos (G : GraphInput) (x : ℝ) (hx : 0 < x) : ∀ a b,0 < rawActivity G x a b := by
  intro a b
  unfold rawActivity
  split_ifs <;> positivity

lemma rawActivity_symm (G : GraphInput) (x : ℝ) (a b : Fin G.n) :
    rawActivity G x a b=rawActivity G x b a := by simp [rawActivity,min_comm,max_comm]

theorem raw_partition (G : GraphInput) (x : ℚ) :
    (rawPartition G x:ℝ)=partition (rawActivity G x) ∅ := by
  unfold rawPartition rawWeight
  push_cast
  rw [←weighted_partition]
  apply sum_congr rfl
  intro M hM
  apply prod_congr rfl
  intro e he
  have hi := (completeGraph G.n).increasing e (((mem_perfectMatchings (completeGraph G.n) M).mp hM).1 he)
  simp only [rawActivity,min_eq_left hi.le,max_eq_right hi.le]
  split_ifs <;> simp

theorem complete_count :
    Z (completeGraph n)=UnitRefresh.pairingCount n := by
  have h := weighted_partition (n:=n) (fun _ _ => 1)
  simp only [prod_const_one,sum_const,nsmul_eq_mul,mul_one] at h
  rw [Initializer.uniform_partition,card_empty,Nat.sub_zero,one_pow,mul_one,Fintype.card_fin] at h
  exact_mod_cast h

end MatchingFPRAS.GraphBridge

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open scoped Classical

noncomputable def cooling (n : ℕ) : ℝ := (1+1/(n:ℝ))⁻¹

lemma cooling_pos (n : ℕ) : 0<cooling n := by unfold cooling; positivity

lemma cooling_le_one (n : ℕ) : cooling n ≤ 1 := by
  unfold cooling
  apply inv_le_one_of_one_le₀
  have h : (0:ℝ) ≤ 1/(n:ℝ) := by positivity
  linarith

noncomputable def raw (G : GraphInput) (j : ℕ) : Fin G.n → Fin G.n → ℝ :=
  GraphBridge.rawActivity G (cooling G.n^j)

lemma raw_pos (G : GraphInput) (j : ℕ) (a b : Fin G.n) : 0<raw G j a b :=
  GraphBridge.rawActivity_pos G _ (pow_pos (cooling_pos G.n) j) a b

lemma raw_le_one (G : GraphInput) (j : ℕ) (a b : Fin G.n) : raw G j a b ≤ 1 := by
  unfold raw GraphBridge.rawActivity
  split_ifs
  · rfl
  · exact pow_le_one₀ (cooling_pos G.n).le (cooling_le_one G.n)

lemma raw_cooling (G : GraphInput) (j : ℕ) (a b : Fin G.n) :
    cooling G.n*raw G j a b ≤ raw G (j+1) a b ∧ raw G (j+1) a b ≤ raw G j a b := by
  unfold raw GraphBridge.rawActivity
  split_ifs
  · simpa using And.intro (cooling_le_one G.n) (le_refl (1:ℝ))
  · rw [pow_succ]
    constructor
    · exact le_of_eq (mul_comm _ _)
    · have h := mul_le_mul_of_nonneg_left (cooling_le_one G.n) (pow_pos (cooling_pos G.n) j).le
      simpa using h

lemma raw_zero (G : GraphInput) : raw G 0=(fun _ _=>1) := by
  funext a b
  simp [raw,GraphBridge.rawActivity]

lemma raw_partition_pos (G : GraphInput) (he : Even G.n) (j : ℕ) : 0<partition (raw G j) ∅ := by
  apply partition_pos_of_even _ (raw_pos G j)
  simpa using he

structure ScaleState (G : GraphInput) (j : ℕ) where
  scale : Fin G.n → ℝ
  positive : ∀ i,0<scale i
  upper : ∀ i,scale i ≤ (2:ℝ)^j

variable {G : GraphInput} {j K S : ℕ}

noncomputable def ScaleState.activity (s : ScaleState G j) : Fin G.n → Fin G.n → ℝ :=
  fun a b => raw G j a b*s.scale a*s.scale b

noncomputable def ScaleState.nextActivity (s : ScaleState G j) : Fin G.n → Fin G.n → ℝ :=
  fun a b => raw G (j+1) a b*s.scale a*s.scale b

lemma ScaleState.activity_pos (s : ScaleState G j) (a b : Fin G.n) : 0 < s.activity a b :=
  mul_pos (mul_pos (raw_pos G j a b) (s.positive a)) (s.positive b)

lemma ScaleState.nextActivity_pos (s : ScaleState G j) (a b : Fin G.n) : 0 < s.nextActivity a b :=
  mul_pos (mul_pos (raw_pos G (j+1) a b) (s.positive a)) (s.positive b)

lemma ScaleState.cooling (s : ScaleState G j) (a b : Fin G.n) :
    cooling G.n*s.activity a b  ≤  s.nextActivity a b ∧ s.nextActivity a b ≤ s.activity a b := by
  have h := raw_cooling G j a b
  constructor
  · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.1 (s.positive a).le) (s.positive b).le
    simpa [ScaleState.activity,ScaleState.nextActivity,mul_assoc] using hh
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.2 (s.positive a).le) (s.positive b).le

lemma ScaleState.activity_bound (s : ScaleState G j) (a b : Fin G.n) : s.activity a b ≤ (4:ℝ)^j := by
  calc
    _  ≤  1*(2:ℝ)^j*2^j := by
      apply mul_le_mul (mul_le_mul (raw_le_one G j a b) (s.upper a) (s.positive a).le (by norm_num))
        (s.upper b) (s.positive b).le (by positivity)
    _ = (4:ℝ)^j := by rw [one_mul,←mul_pow]; norm_num

lemma ScaleState.cap (s : ScaleState G j) (h : j ≤ K) (a b : Fin G.n) (_hab : a≠b) :
    edgeActivity s.activity a b ≤ (4:ℝ)^K := by
  unfold edgeActivity
  split_ifs
  all_goals exact (s.activity_bound _ _).trans (pow_le_pow_right₀ (by norm_num) h)

lemma ScaleState.partition_pos (s : ScaleState G j) (he : Even G.n) : 0<partition s.activity ∅ := by
  apply partition_pos_of_even _ s.activity_pos
  simpa using he

lemma ScaleState.ratio (s : ScaleState G j) :
    partition s.nextActivity ∅/partition s.activity ∅=
      partition (raw G (j+1)) ∅/partition (raw G j) ∅ := by
  unfold ScaleState.activity ScaleState.nextActivity
  rw [partition_vertex_scaling,partition_vertex_scaling]
  have hp : (∏ x ∈ (∅:Finset (Fin G.n))ᶜ,s.scale x)≠0 :=
    ne_of_gt (prod_pos fun x _ => s.positive x)
  exact mul_div_mul_right _ _ hp

noncomputable def initialScaleState (G : GraphInput) (hn : 2 ≤ G.n) : ScaleState G 0 where
  scale _ := (Initializer.initialScale G.n:ℝ)
  positive _ := by exact_mod_cast Initializer.initialScale_pos G.n hn
  upper _ := by
    unfold Initializer.initialScale
    push_cast
    simp only [pow_zero]
    have hs : 1 ≤ Nat.sqrt (G.n-1) := Nat.le_sqrt.mpr (by omega)
    have hs' : (1:ℝ) ≤ Nat.sqrt (G.n-1) := by exact_mod_cast hs
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hs'

def ScaleState.Balanced (hn : 2 ≤ G.n) (s : ScaleState G j) : Prop :=
  (∀ i,(1:ℝ)/4 ≤ rowMax (by simpa using hn) s.activity i) ∧
  (∀ i,rowMax (by simpa using hn) s.activity i ≤ 1)

lemma initial_balanced (G : GraphInput) (hn : 2 ≤ G.n) (he : Even G.n) :
    (initialScaleState G hn).Balanced hn := by
  have h := Initializer.initial_balanced (V:=Fin G.n) (by simpa using hn) (by simpa using he)
  have ha : (initialScaleState G hn).activity=(fun _ _ : Fin G.n => (Initializer.initialScale G.n:ℝ)^2) := by
    funext a b
    simp [ScaleState.activity,raw_zero,initialScaleState,pow_two]
  simpa only [ScaleState.Balanced,ha,Fintype.card_fin] using h.2

variable [Nontrivial (Fin G.n)]

noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def ScaleState.matrix (s : ScaleState G j) (x : Fin S → SourceMarked s.activity K) :
    Fin G.n → Fin G.n → ℝ :=
  estimateMatrix (sourceD (V:=Fin G.n) K) (sampleAverage (observableD s.activity s.nextActivity K) x)
    (fun e => sampleAverage (observableProbe s.activity s.nextActivity K e) x)

lemma ScaleState.matrix_bounds (s : ScaleState G j) (x : Fin S → SourceMarked s.activity K) (a b : Fin G.n) :
    RealStage.alpha ≤ s.matrix x a b ∧ s.matrix x a b ≤ 3 := by
  unfold ScaleState.matrix estimateMatrix RealStage.upperEstimate
  split_ifs
  · exact ⟨le_max_left _ _,max_le (by norm_num [RealStage.alpha]) (min_le_left _ _)⟩
  · norm_num [RealStage.alpha]

noncomputable def ScaleState.updateVector (hn : 2 ≤ G.n) (s : ScaleState G j)
    (x : Fin S → SourceMarked s.activity K) : Fin G.n → ℝ :=
  RealStage.scalingTrace hn (s.matrix x) G.n

lemma ScaleState.updateVector_bounds (hn : 2 ≤ G.n) (s : ScaleState G j)
    (x : Fin S → SourceMarked s.activity K) :
    ∀ i,0 < s.updateVector hn x i ∧ s.updateVector hn x i ≤ 2 := by
  have h := (RealStage.scalingTrace_invariant hn (s.matrix x)
    (estimateMatrix_symm _ _ _) (fun a b _ => s.matrix_bounds x a b) G.n).1
  intro i
  exact ⟨h.pos i,h.upper i⟩

noncomputable def ScaleState.update (hn : 2 ≤ G.n) (s : ScaleState G j)
    (x : Fin S → SourceMarked s.activity K) : ScaleState G (j+1) where
  scale i := s.scale i*s.updateVector hn x i
  positive i := mul_pos (s.positive i) (s.updateVector_bounds hn x i).1
  upper i := by
    rw [pow_succ]
    exact mul_le_mul (s.upper i) (s.updateVector_bounds hn x i).2
      (s.updateVector_bounds hn x i).1.le (by positivity)

lemma ScaleState.update_activity (hn : 2 ≤ G.n) (s : ScaleState G j)
    (x : Fin S → SourceMarked s.activity K) :
    (s.update hn x).activity=(fun a b=>s.nextActivity a b*s.updateVector hn x a*s.updateVector hn x b) := by
  funext a b
  simp only [ScaleState.activity,ScaleState.update,ScaleState.nextActivity]
  ring

noncomputable def ScaleState.ratioEstimate (s : ScaleState G j) (x : Fin S → SourceMarked s.activity K) : ℝ :=
  RealStage.ratioEstimate (sampleAverage (observableA s.activity K) x)
    (sampleAverage (observableD s.activity s.nextActivity K) x)

lemma ScaleState.ratioEstimate_nonneg (s : ScaleState G j) (_hS : 0<S)
    (x : Fin S → SourceMarked s.activity K) : 0 ≤ s.ratioEstimate x := by
  unfold ScaleState.ratioEstimate RealStage.ratioEstimate
  split_ifs with h
  · apply div_nonneg _ h.le
    unfold sampleAverage
    apply div_nonneg _ (Nat.cast_nonneg S)
    apply sum_nonneg
    intro i _
    exact (observableD_range_off s.activity s.nextActivity s.activity_pos
      (fun a b=>(s.nextActivity_pos a b).le) (fun a b _=>(s.cooling a b).2) K (x i)).1
  · norm_num

noncomputable def stageData (G : GraphInput) (hn : 2 ≤ G.n) (he : Even G.n) (K : ℕ) (hK : 0<K)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) (j : ℕ) (hj : j ≤ K) (s : ScaleState G j)
    (hs : s.Balanced hn) : StageData G.n K K where
  hn := hn
  w := s.activity
  next := s.nextActivity
  positive := s.activity_pos
  next_positive := s.nextActivity_pos
  partition_positive := s.partition_pos he
  lower := hs.1
  upper := hs.2
  cool_lower a b _ := (s.cooling a b).1
  cool_upper a b _ := (s.cooling a b).2
  cap := s.cap hj
  stages := hK
  epsilon := ε
  epsilon_positive := hε
  epsilon_lt_one := hε1

theorem successful_update (hn : 2 ≤ G.n) (he : Even G.n) (hK : 0<K)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) (hj : j ≤ K) (s : ScaleState G j)
    (hs : s.Balanced hn) (x : Fin S → SourceMarked s.activity K)
    (hx : StageGood s.activity s.nextActivity K (RealStage.sigma (sourceD (V:=Fin G.n) K) K ε) x) :
    (s.update hn x).Balanced hn ∧
      |s.ratioEstimate x/(partition (raw G (j+1)) ∅/partition (raw G j) ∅)-1| ≤ ε/(100*K) := by
  let c := stageData G hn he K hK ε hε hε1 j hj s hs
  let b : EmpiricalData c := empiricalData c x hx
  have hh := actual_successful_stage c b
  dsimp only at hh
  have heq : estimateMatrix (sourceD (V:=Fin G.n) K) b.dbar b.zbar=s.matrix x := rfl
  rw [heq] at hh
  constructor
  · unfold ScaleState.Balanced
    rw [s.update_activity hn x]
    exact ⟨fun i=>(hh.2.1 i).1,fun i=>(hh.2.1 i).2⟩
  · rw [←s.ratio]
    exact hh.2.2

end MatchingFPRAS.Trial

namespace MatchingFPRAS.Counting

theorem stage_product_error (K : ℕ) (hK : 1 ≤ K) (epsilon : ℝ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (factors : Fin K → ℝ)
    (herr : ∀ j, |factors j-1| ≤ epsilon/(100*K)) :
    1-epsilon/100 ≤ ∏ j, factors j ∧ ∏ j, factors j ≤ 1+epsilon/50 := by
  classical
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0:ℝ) < K := by linarith
  let t : ℝ := epsilon/(100*K)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ epsilon/100 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < (100:ℝ)*K)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hKr he.le]
  have hkt : (K:ℝ)*t=epsilon/100 := by dsimp [t]; field_simp
  have hlo (j : Fin K) : 1-t ≤ factors j := by
    have h := (abs_le.mp (herr j)).1
    change -t ≤ factors j-1 at h
    linarith
  have hup (j : Fin K) : factors j ≤ 1+t := by
    have h := (abs_le.mp (herr j)).2
    change factors j-1 ≤ t at h
    linarith
  have hf0 (j : Fin K) : 0 ≤ factors j := by have := hlo j; linarith
  constructor
  · have hpow : 1-epsilon/100 ≤ (1-t)^K := by
      have h := one_add_mul_le_pow (a := -t) (by linarith : (-2:ℝ) ≤ -t) K
      simpa only [← sub_eq_add_neg, mul_neg, hkt] using h
    apply hpow.trans
    calc
      (1-t)^K = ∏ _j : Fin K, (1-t) := by simp
      _ ≤ ∏ j, factors j := Finset.prod_le_prod₀ (fun _ _ => by linarith) (fun j _ => hlo j)
  · have hprod : (∏ j, factors j) ≤ Real.exp (epsilon/100) := by
      calc
        _ ≤ ∏ _j : Fin K, (1+t) := Finset.prod_le_prod₀ (fun j _ => hf0 j) (fun j _ => hup j)
        _ ≤ Real.exp (∑ _j : Fin K, t) := Real.prod_one_add_le_exp_sum _ (fun _ => ht0)
        _ = Real.exp (epsilon/100) := by simp [hkt]
    apply hprod.trans
    have hh := Real.exp_le_two_add_div_two_sub (x := epsilon/100) (by positivity) (by linarith)
    apply hh.trans
    apply (div_le_iff₀ (by linarith : 0 < 2-epsilon/100)).mpr
    nlinarith [sq_nonneg epsilon]



def productEstimate {K : ℕ} (initial : ℝ) (estimates : Fin K → ℝ) : ℝ :=
  initial * ∏ j, estimates j



lemma positive_telescope (Z : ℕ → ℝ) (hZ : ∀ j, 0 < Z j) (K : ℕ) :
    (∏ j : Fin K, Z (j.val+1)/Z j.val)=Z K/Z 0 := by
  induction K with
  | zero => simp [(hZ 0).ne']
  | succ K ih =>
    rw [Fin.prod_univ_castSucc]
    change (∏ j : Fin K, Z (j.val+1)/Z j.val)*(Z (K+1)/Z K)=_
    rw [ih]
    field_simp [(hZ K).ne', (hZ 0).ne']

end MatchingFPRAS.Counting

end OAI
