import Mathlib
import OAI.Probability.JammingConcavity.RPCSamplePattern
import OAI.Probability.JammingConcavity.RowCommonRankContinuity

namespace OAI

/-! R P C Pattern Extension. -/

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
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

 
def patternConsEquiv (k : ℕ) (b : ReplicaPattern k) (bs : List (ReplicaPattern k)) :
    PatternIndex (k+1) (b::bs) ≃ PatternIndex k b ⊕ PatternIndex (k+1) bs where
  toFun x := Fin.cases (fun j => Sum.inl j) (fun i j => Sum.inr ⟨i,j⟩) x.1 x.2
  invFun x := match x with
    | .inl j => ⟨0,j⟩
    | .inr ⟨i,j⟩ => ⟨i.succ,j⟩
  left_inv := by
    rintro ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i j <;> intro j <;> rfl
  right_inv := by rintro (j|⟨i,j⟩) <;> rfl

 
def optionSumLeft (α β : Type*) : Option (α ⊕ β) ≃ Option α ⊕ β where
  toFun x := match x with
    | none => .inl none
    | some (.inl a) => .inl (some a)
    | some (.inr b) => .inr b
  invFun x := match x with
    | .inl none => none
    | .inl (some a) => some (.inl a)
    | .inr b => some (.inr b)
  left_inv := by rintro (_|(_|_)) <;> rfl
  right_inv := by rintro ((_ | _) | _) <;> rfl

def optionSumRight (α β : Type*) : Option (α ⊕ β) ≃ α ⊕ Option β :=
  (Equiv.optionCongr (Equiv.sumComm α β)).trans
    ((optionSumLeft β α).trans (Equiv.sumComm (Option β) α))

 

def PatternSite : (k : ℕ) → ReplicaPattern k → Type
  | 0,_ => PUnit
  | k+1,bs => List.foldr (fun b rest => PatternSite k b ⊕ rest) PUnit bs

instance patternSiteFintype : (k : ℕ) → (b : ReplicaPattern k) → Fintype (PatternSite k b)
  | 0,_ => inferInstanceAs (Fintype PUnit)
  | k+1,bs => by
    change List (ReplicaPattern k) at bs
    induction bs with
    | nil => exact inferInstanceAs (Fintype PUnit)
    | cons b bs ih =>
      letI := patternSiteFintype k b
      letI : Fintype (PatternSite (k+1) bs) := ih
      exact inferInstanceAs (Fintype (PatternSite k b ⊕ PatternSite (k+1) bs))

structure PatternExtension (k : ℕ) (b : ReplicaPattern k) where
  next : ReplicaPattern k
  index : Option (PatternIndex k b) ≃ PatternIndex k next

lemma patternIndex_singleton_card (k : ℕ) :
    Fintype.card (PatternIndex k (singletonReplicaPattern k))=1 := by
  rw [patternIndex_card,singletonReplicaPattern_size]

 

def patternExtension : (k : ℕ) → (b : ReplicaPattern k) →
    PatternSite k b → PatternExtension k b
  | 0,n,_ => by
    change ℕ at n
    exact ⟨n+1,finSuccEquivLast.symm⟩
  | k+1,bs,s => by
    change List (ReplicaPattern k) at bs
    induction bs with
    | nil =>
      letI := patternIndexFintype (k+1) ([] : List (ReplicaPattern k))
      letI := patternIndexFintype (k+1) [singletonReplicaPattern k]
      let e : Option (PatternIndex (k+1) ([] : List (ReplicaPattern k))) ≃
          PatternIndex (k+1) [singletonReplicaPattern k] := Fintype.equivOfCardEq (by
            erw [Fintype.card_option,patternIndex_card,patternIndex_card]
            simp [replicaPatternSize,singletonReplicaPattern_size])
      exact ⟨[singletonReplicaPattern k],e⟩
    | cons b bs ih =>
      rcases s with s | s
      · let e := patternExtension k b s
        exact ⟨e.next :: bs,
          (Equiv.optionCongr (patternConsEquiv k b bs)).trans
            ((optionSumLeft _ _).trans ((Equiv.sumCongr e.index (Equiv.refl _)).trans
              (patternConsEquiv k e.next bs).symm))⟩
      · let e := ih s
        exact ⟨b :: e.next,
          (Equiv.optionCongr (patternConsEquiv k b bs)).trans
            ((optionSumRight _ _).trans ((Equiv.sumCongr (Equiv.refl _) e.index).trans
              (patternConsEquiv k b e.next).symm))⟩

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma rpcSamplePattern_nil (k : ℕ)
    (x : PatternIndex (k+1) ([] : List (ReplicaPattern k)) → CascadePath (k+1)) :
    RPCSamplePattern (k+1) [] x := by
  refine ⟨Fin.elim0,?_,?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

lemma rpcSamplePattern_cons_iff (k : ℕ) (b : ReplicaPattern k) (bs : List (ReplicaPattern k))
    (hbs : ∀ t ∈ bs, ValidReplicaPattern k t)
    (x : PatternIndex (k+1) (b::bs) → CascadePath (k+1)) :
    RPCSamplePattern (k+1) (b::bs) x ↔
      ∃ a : CloudLabel, (∀ j : PatternIndex k b, (x ⟨0,j⟩).1=a) ∧
        RPCSamplePattern k b (fun j => (x ⟨0,j⟩).2) ∧
        RPCSamplePattern (k+1) bs (fun p => x ⟨p.1.succ,p.2⟩) ∧
        ∀ (i : Fin bs.length) (j : PatternIndex k (bs.get i)), (x ⟨i.succ,j⟩).1 ≠ a := by
  constructor
  · rintro ⟨a,ha,hx⟩
    refine ⟨a 0,(hx 0).1,(hx 0).2,?_,?_⟩
    · refine ⟨fun i => a i.succ,ha.comp (Fin.succ_injective _),?_⟩
      intro i
      exact hx i.succ
    · intro i j h
      have he : a i.succ=a 0 := ((hx i.succ).1 j).symm.trans h
      exact Fin.succ_ne_zero i (ha he)
  · rintro ⟨a,ha,hb,⟨c,hc,ht⟩,hneq⟩
    let d : Fin (bs.length+1) → CloudLabel := Fin.cases a c
    have hne (i : Fin bs.length) : c i ≠ a := by
      obtain ⟨j⟩ := patternIndex_nonempty k (bs.get i) (hbs _ (List.get_mem _ _))
      intro h
      exact hneq i j (((ht i).1 j).trans h)
    have hd : Function.Injective d := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro h
        exact (hne j h.symm).elim
      · intro h
        exact (hne i h).elim
      · intro h
        exact congrArg Fin.succ (hc h)
    refine ⟨d,hd,?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨ha,hb⟩
    · exact ht i

lemma rpcSamplePattern_congr {k : ℕ} {b : ReplicaPattern k}
    {x y : PatternIndex k b → CascadePath k} (h : ∀ i, x i=y i) :
    RPCSamplePattern k b x ↔ RPCSamplePattern k b y := by
  rw [funext h]

lemma rpcSamplePattern_singleton (k : ℕ)
    (x : PatternIndex k (singletonReplicaPattern k) → CascadePath k) :
    RPCSamplePattern k (singletonReplicaPattern k) x := by
  induction k with
  | zero => trivial
  | succ k ih =>
    dsimp only [singletonReplicaPattern] at x ⊢
    let : Unique (PatternIndex k (singletonReplicaPattern k)) :=
      Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp (patternIndex_singleton_card k))
    refine ⟨fun _ => (x ⟨0,(default : PatternIndex k (singletonReplicaPattern k))⟩).1,?_,?_⟩
    · intro i j _
      change Fin 1 at i j
      exact Subsingleton.elim i j
    · intro i
      have hi : i=0 := by
        change Fin 1 at i
        exact Subsingleton.elim i 0
      subst i
      refine ⟨?_,ih _⟩
      intro j
      change PatternIndex k (singletonReplicaPattern k) at j
      rw [Subsingleton.elim j (default : PatternIndex k (singletonReplicaPattern k))]

 
def insertedSample {k : ℕ} {b : ReplicaPattern k} {A : Type*}
    (e : PatternExtension k b) (x : PatternIndex k b → A) (y : A) :
    PatternIndex k e.next → A := fun j => (e.index.symm j).elim y x

@[simp] lemma insertedSample_old {k : ℕ} {b : ReplicaPattern k} {A : Type*}
    (e : PatternExtension k b) (x : PatternIndex k b → A) (y : A) (j : PatternIndex k b) :
    insertedSample e x y (e.index (some j))=x j := by simp [insertedSample]

@[simp] lemma insertedSample_new {k : ℕ} {b : ReplicaPattern k} {A : Type*}
    (e : PatternExtension k b) (x : PatternIndex k b → A) (y : A) :
    insertedSample e x y (e.index none)=y := by simp [insertedSample]

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

 

def patternCanonicalPath : (k : ℕ) → (b : ReplicaPattern k) → PatternIndex k b → CascadePath k
  | 0,_,_ => PUnit.unit
  | k+1,bs,i => ((i.1.val,0),patternCanonicalPath k (bs.get i.1) i.2)

def patternSignature (k : ℕ) (b : ReplicaPattern k) (i j : PatternIndex k b) : ℕ :=
  cascadeSharedEdges k (patternCanonicalPath k b i) (patternCanonicalPath k b j)

lemma patternCanonicalPath_sample (k : ℕ) (b : ReplicaPattern k) :
    RPCSamplePattern k b (patternCanonicalPath k b) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨fun i => (i.val,0),?_,?_⟩
    · intro i j h
      exact Fin.ext (congrArg Prod.fst h)
    · intro i
      exact ⟨fun _ => rfl,ih _⟩

lemma cascadeSharedEdges_le (k : ℕ) (x y : CascadePath k) : cascadeSharedEdges k x y ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [cascadeSharedEdges]
    split_ifs
    · simpa only [Nat.add_comm] using Nat.add_le_add_left (ih _ _) 1
    · exact Nat.zero_le _

lemma cascadeSharedEdges_self (k : ℕ) (x : CascadePath k) : cascadeSharedEdges k x x=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [cascadeSharedEdges,ih,Nat.add_comm]

lemma cascadeSharedEdges_pos_iff {k : ℕ} (x y : CascadePath (k+1)) :
    0 < cascadeSharedEdges (k+1) x y ↔ x.1=y.1 := by
  simp only [cascadeSharedEdges]
  split_ifs with h <;> simp [h]

lemma patternSignature_root_iff {k : ℕ} {bs : List (ReplicaPattern k)}
    (i j : PatternIndex (k+1) bs) : 0 < patternSignature (k+1) bs i j ↔ i.1=j.1 := by
  erw [patternSignature,cascadeSharedEdges_pos_iff]
  change (i.1.val,0)=(j.1.val,0) ↔ i.1=j.1
  simp only [Prod.mk.injEq,and_true,Fin.val_inj]

lemma rpcSamplePattern_signature (k : ℕ) (b : ReplicaPattern k)
    (x : PatternIndex k b → CascadePath k) (hx : RPCSamplePattern k b x) :
    ∀ i j, cascadeSharedEdges k (x i) (x j)=patternSignature k b i j := by
  induction k with
  | zero => intro i j; rfl
  | succ k ih =>
    obtain ⟨a,ha,hx⟩ := hx
    rintro ⟨i,s⟩ ⟨j,t⟩
    by_cases hij : i=j
    · subst j
      change (if (x ⟨i,s⟩).1=(x ⟨i,t⟩).1 then 1+cascadeSharedEdges k (x ⟨i,s⟩).2 (x ⟨i,t⟩).2 else 0)=_
      erw [ite_eq_left (((hx i).1 s).trans ((hx i).1 t).symm)]
      have hc := ih _ _ (hx i).2 s t
      change 1+_=(if (i.val,0)=(i.val,0) then 1+_ else 0)
      erw [ite_eq_left rfl,hc]
      rfl
    · have hxy : (x ⟨i,s⟩).1 ≠ (x ⟨j,t⟩).1 := by
        erw [(hx i).1 s,(hx j).1 t]
        exact fun h => hij (ha h)
      have hc : (i.val,0) ≠ (j.val,0) := by
        intro h
        exact hij (Fin.ext (congrArg Prod.fst h))
      change (if _ then _ else 0)=(if _ then _ else 0)
      erw [ite_eq_right hxy,ite_eq_right hc]

lemma rpcSamplePattern_of_signature (k : ℕ) (b : ReplicaPattern k)
    (hb : ValidReplicaPattern k b) (x : PatternIndex k b → CascadePath k)
    (hx : ∀ i j, cascadeSharedEdges k (x i) (x j)=patternSignature k b i j) :
    RPCSamplePattern k b x := by
  induction k with
  | zero => trivial
  | succ k ih =>
    change List (ReplicaPattern k) at b
    have hn (i : Fin b.length) : Nonempty (PatternIndex k (b.get i)) :=
      patternIndex_nonempty k (b.get i) (hb.2 _ (List.get_mem _ _))
    let f (i : Fin b.length) : PatternIndex k (b.get i) := Classical.choice (hn i)
    let a (i : Fin b.length) : CloudLabel := (x ⟨i,f i⟩).1
    have hsame (i : Fin b.length) (s t : PatternIndex k (b.get i)) :
        (x ⟨i,s⟩).1=(x ⟨i,t⟩).1 := by
      apply (cascadeSharedEdges_pos_iff _ _).mp
      erw [hx]
      exact (patternSignature_root_iff _ _).mpr rfl
    refine ⟨a,?_,?_⟩
    · intro i j h
      have hp : 0 < cascadeSharedEdges (k+1) (x ⟨i,f i⟩) (x ⟨j,f j⟩) :=
        (cascadeSharedEdges_pos_iff _ _).mpr h
      erw [hx] at hp
      exact (patternSignature_root_iff _ _).mp hp
    · intro i
      refine ⟨fun s => hsame i s (f i),ih _ (hb.2 _ (List.get_mem _ _)) _ ?_⟩
      intro s t
      have he := hx ⟨i,s⟩ ⟨i,t⟩
      change (if (x ⟨i,s⟩).1=(x ⟨i,t⟩).1 then 1+_ else 0)=
        (if (i.val,0)=(i.val,0) then 1+_ else 0) at he
      erw [ite_eq_left (hsame i s t),ite_eq_left rfl] at he
      exact Nat.add_left_cancel he

lemma rpcSamplePattern_iff_signature (k : ℕ) (b : ReplicaPattern k)
    (hb : ValidReplicaPattern k b) (x : PatternIndex k b → CascadePath k) :
    RPCSamplePattern k b x ↔
      ∀ i j, cascadeSharedEdges k (x i) (x j)=patternSignature k b i j :=
  ⟨rpcSamplePattern_signature k b x,rpcSamplePattern_of_signature k b hb x⟩

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

local instance (n : ℕ) : Encodable (Fin n → Bool) := Fintype.toEncodable _

def rankProfileCode {n : ℕ} (m : ℝ) (f : Fin n → ℝ) : CloudLabel :=
  (Encodable.encode (fun i => if m ≤ f i then true else false),0)

lemma rankProfileCode_eq_iff {n : ℕ} (m : ℝ) (f g : Fin n → ℝ) :
    rankProfileCode m f=rankProfileCode m g ↔ ∀ i, (m ≤ f i ↔ m ≤ g i) := by
  simp only [rankProfileCode,Prod.mk.injEq,and_true,Encodable.encode_inj,funext_iff]
  exact forall_congr' fun i => by by_cases hf : m ≤ f i <;> by_cases hg : m ≤ g i <;> simp [hf,hg]

lemma measurable_rankProfileCode (n : ℕ) (m : ℝ) :
    Measurable (rankProfileCode (n:=n) m) := by
  have hc : Measurable (fun f : Fin n → ℝ => fun i => if m ≤ f i then true else false) := by
    apply Measurable.of_eval
    intro i
    exact Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply i))
      measurable_const measurable_const
  exact (measurable_of_countable (fun b : Fin n → Bool => (Encodable.encode b,0))).comp hc

def rankProfilePath {n : ℕ} : (ms : List ℝ) → (Fin n → ℝ) → CascadePath ms.length
  | [],_ => ()
  | m::ms,f => (rankProfileCode m f,rankProfilePath ms f)

lemma measurable_rankProfilePath (n : ℕ) (ms : List ℝ) :
    Measurable (rankProfilePath (n:=n) ms) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    exact (measurable_of_countable (fun p : CloudLabel × CascadePath ms.length =>
      (show CascadePath (m::ms).length from p))).comp ((measurable_rankProfileCode n m).prodMk ih)

lemma rankProfileCode_rows {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i j : Fin n) (m : ℝ) (hm : m ≤ 1) :
    rankProfileCode m (R i)=rankProfileCode m (R j) ↔ m ≤ R i j := by
  rw [rankProfileCode_eq_iff]
  constructor
  · intro h
    exact (h j).mpr (by rw [hR.1 j]; exact hm)
  · intro hij l
    constructor
    · intro hil
      exact (le_min (by rw [hR.2.1 j i]; exact hij) hil).trans (hR.2.2.2 j i l)
    · intro hjl
      exact (le_min hij hjl).trans (hR.2.2.2 i j l)

lemma rankProfileCode_link {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i j : Fin n) (v m : ℝ) (hm : m ≤ 1) :
    rankProfileCode m (rankLink R j v)=rankProfileCode m (R i) ↔ m ≤ rankLink R j v i := by
  rw [rankProfileCode_eq_iff]
  constructor
  · intro h
    exact (h i).mpr (by rw [hR.1 i]; exact hm)
  · intro hi l
    constructor
    · intro hl
      exact (le_min hi hl).trans (rankLink_pair_le hR i l j v)
    · intro hil
      exact (le_min (by rw [hR.2.1 l i]; exact hil) hi).trans (rankLink_parent_le hR l i j v)

lemma rankProfilePath_sharedEdges {n : ℕ} (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (f g : Fin n → ℝ) (z : ℝ)
    (he : ∀ m ∈ ms, rankProfileCode m f=rankProfileCode m g ↔ m ≤ z) :
    cascadeSharedEdges ms.length (rankProfilePath ms f) (rankProfilePath ms g)=rpcStepLevel ms z := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    have ht := ih (List.pairwise_cons.mp hms).2 (fun t ht => he t (List.mem_cons_of_mem _ ht))
    change (if rankProfileCode m f=rankProfileCode m g then 1+_ else 0)=_
    by_cases hm : m ≤ z
    · erw [ite_eq_left ((he m (by simp)).mpr hm),ht]
      simp [rpcStepLevel,hm,Nat.add_comm]
    · rw [ite_eq_right (fun h => hm ((he m (by simp)).mp h))]
      have hf : ∀ t ∈ ms, ¬ t ≤ z := fun t ht htz =>
        hm (((List.pairwise_cons.mp hms).1 t ht).le.trans htz)
      have hnil : ms.filter (fun t => decide (t ≤ z))=[] :=
        List.filter_eq_nil_iff.mpr (by simpa using hf)
      simp [rpcStepLevel,hm,hnil]

lemma rankProfilePath_rows {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (hmax : ∀ m ∈ ms, m ≤ 1) (i j : Fin n) :
    cascadeSharedEdges ms.length (rankProfilePath ms (R i)) (rankProfilePath ms (R j))=
      rpcStepLevel ms (R i j) :=
  rankProfilePath_sharedEdges ms hms _ _ _ (fun m hm => rankProfileCode_rows hR i j m (hmax m hm))

lemma rankProfilePath_link {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (hmax : ∀ m ∈ ms, m ≤ 1) (i j : Fin n) (v : ℝ) :
    cascadeSharedEdges ms.length (rankProfilePath ms (rankLink R j v)) (rankProfilePath ms (R i))=
      rpcStepLevel ms (rankLink R j v i) :=
  rankProfilePath_sharedEdges ms hms _ _ _ (fun m hm => rankProfileCode_link hR i j v m (hmax m hm))

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma insertedSample_left_head {k : ℕ} (b : ReplicaPattern k) (bs : List (ReplicaPattern k))
    (s : PatternSite k b) {A : Type*} (x : PatternIndex (k+1) (b::bs) → A) (y : A)
    (j : PatternIndex k (patternExtension k b s).next) :
    insertedSample (patternExtension (k+1) (b::bs) (.inl s)) x y ⟨⟨0,by change 0 < bs.length+1; omega⟩,j⟩ =
      insertedSample (patternExtension k b s) (fun j => x ⟨0,j⟩) y j := by
  change ((Equiv.optionCongr (patternConsEquiv k b bs)).symm
    ((optionSumLeft _ _).symm (.inl ((patternExtension k b s).index.symm j)))).elim y x = _
  cases h : (patternExtension k b s).index.symm j <;>
    simp only [insertedSample,h] <;> rfl

lemma insertedSample_left_tail {k : ℕ} (b : ReplicaPattern k) (bs : List (ReplicaPattern k))
    (s : PatternSite k b) {A : Type*} (x : PatternIndex (k+1) (b::bs) → A) (y : A)
    (i : Fin bs.length) (j : PatternIndex k (bs.get i)) :
    insertedSample (patternExtension (k+1) (b::bs) (.inl s)) x y ⟨i.succ,j⟩ = x ⟨i.succ,j⟩ := by
  rfl

lemma insertedSample_right_head {k : ℕ} (b : ReplicaPattern k) (bs : List (ReplicaPattern k))
    (s : PatternSite (k+1) bs) {A : Type*} (x : PatternIndex (k+1) (b::bs) → A) (y : A)
    (j : PatternIndex k b) :
    insertedSample (patternExtension (k+1) (b::bs) (.inr s)) x y ⟨⟨0,by change 0 < ((patternExtension (k+1) bs s).next : List (ReplicaPattern k)).length+1; omega⟩,j⟩ = x ⟨0,j⟩ := by
  rfl

lemma insertedSample_right_tail {k : ℕ} (b : ReplicaPattern k) (bs : List (ReplicaPattern k))
    (s : PatternSite (k+1) bs) {A : Type*} (x : PatternIndex (k+1) (b::bs) → A) (y : A)
    (i : Fin (patternExtension (k+1) bs s).next.length)
    (j : PatternIndex k ((patternExtension (k+1) bs s).next.get i)) :
    insertedSample (patternExtension (k+1) (b::bs) (.inr s)) x y ⟨i.succ,j⟩ =
      insertedSample (patternExtension (k+1) bs s) (fun j => x ⟨j.1.succ,j.2⟩) y ⟨i,j⟩ := by
  change ((Equiv.optionCongr (patternConsEquiv k b bs)).symm
    ((optionSumRight _ _).symm (.inr ((patternExtension (k+1) bs s).index.symm ⟨i,j⟩)))).elim y x = _
  cases h : (patternExtension (k+1) bs s).index.symm ⟨i,j⟩ <;>
    simp only [insertedSample,h] <;> rfl

lemma insertedSample_comp {k : ℕ} {b : ReplicaPattern k} {A B : Type*}
    (e : PatternExtension k b) (x : PatternIndex k b → A) (y : A) (f : A → B) :
    f ∘ insertedSample e x y = insertedSample e (f ∘ x) (f y) := by
  funext j
  simp only [Function.comp_apply, insertedSample]
  cases e.index.symm j <;> rfl

lemma insertedSample_forall {k : ℕ} {b : ReplicaPattern k} {A : Type*}
    (e : PatternExtension k b) (x : PatternIndex k b → A) (y : A) (P : A → Prop) :
    (∀ j, P (insertedSample e x y j)) ↔ P y ∧ ∀ j, P (x j) := by
  constructor
  · intro h
    exact ⟨by simpa using h (e.index none),fun j => by simpa using h (e.index (some j))⟩
  · rintro ⟨hy,hx⟩ j
    obtain ⟨a,rfl⟩ := e.index.surjective j
    cases a with
    | none => simpa using hy
    | some j => simpa using hx j

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def patternSiteFold {A : Type*} (k : ℕ) (f : (b : ReplicaPattern k) → PatternSite k b → A)
    (a : A) : (bs : List (ReplicaPattern k)) → PatternSite (k+1) bs → A
  | [],_ => a
  | b::_,.inl s => f b s
  | _::bs,.inr s => patternSiteFold k f a bs s

def patternSiteWeight : (ms : List ℝ) → ℝ → (b : ReplicaPattern ms.length) →
    PatternSite ms.length b → ℝ
  | [],η,n,_ => by
    change ℕ at n
    exact (n:ℝ)-η
  | m::ms,η,bs,s => patternSiteFold ms.length (fun b t => patternSiteWeight ms m b t)
      ((bs.length:ℝ)*m-η) bs s

lemma patternExtension_cases {A : Type*} (k : ℕ)
    (f : (b : ReplicaPattern k) → PatternSite k b → A) (a : A)
    (bs : List (ReplicaPattern k)) (s : PatternSite (k+1) bs) :
    ((patternExtension (k+1) bs s).next=bs ++ [singletonReplicaPattern k] ∧
      patternSiteFold k f a bs s=a) ∨
    ∃ (pre post : List (ReplicaPattern k)) (b : ReplicaPattern k) (t : PatternSite k b),
      bs=pre ++ b::post ∧
      (patternExtension (k+1) bs s).next=pre ++ (patternExtension k b t).next::post ∧
      patternSiteFold k f a bs s=f b t := by
  induction bs with
  | nil => exact Or.inl ⟨rfl,rfl⟩
  | cons b bs ih =>
    rcases s with s|s
    · exact Or.inr ⟨[],bs,b,s,rfl,rfl,rfl⟩
    · rcases ih s with ⟨hn,hf⟩|⟨pre,post,c,t,hbs,hn,hf⟩
      · exact Or.inl ⟨congrArg (List.cons b) hn,hf⟩
      · exact Or.inr ⟨b::pre,post,c,t,congrArg (List.cons b) hbs,congrArg (List.cons b) hn,hf⟩

lemma patternExtension_insertion (ms : List ℝ) (η : ℝ)
    (b : ReplicaPattern ms.length) (s : PatternSite ms.length b) :
    RPCInsertion ms η b (patternExtension ms.length b s).next (patternSiteWeight ms η b s) := by
  induction ms generalizing η with
  | nil => exact RPCInsertion.leaf η b
  | cons m ms ih =>
    change List (ReplicaPattern ms.length) at b
    obtain ⟨hn,hw⟩|⟨pre,post,c,t,hb,hn,hw⟩ := patternExtension_cases ms.length
      (fun c t => patternSiteWeight ms m c t) ((b.length:ℝ)*m-η) b s
    · change RPCInsertion (m::ms) η b _ (patternSiteFold _ _ _ b s)
      erw [hn,hw]
      exact RPCInsertion.newChild m ms η b
    · change RPCInsertion (m::ms) η b _ (patternSiteFold _ _ _ b s)
      erw [hn,hw,hb]
      exact RPCInsertion.oldChild m ms η pre post c _ _ (ih m c t)

lemma patternExtension_valid (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (b : ReplicaPattern ms.length)
    (hb : ValidReplicaPattern ms.length b) (s : PatternSite ms.length b) :
    ValidReplicaPattern ms.length (patternExtension ms.length b s).next := by
  exact (rpcInsertion_properties (patternExtension_insertion ms 0 b s) hms h01
    le_rfl zero_lt_one (fun m hm => (h01 m hm).1) hb).1

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma patternExtension_valid_generic (k : ℕ) (b : ReplicaPattern k)
    (hb : ValidReplicaPattern k b) (s : PatternSite k b) :
    ValidReplicaPattern k (patternExtension k b s).next := by
  induction k with
  | zero => exact Nat.succ_pos _
  | succ k ih =>
    change List (ReplicaPattern k) at b
    change b ≠ [] ∧ ∀ c ∈ b, ValidReplicaPattern k c at hb
    change (patternExtension (k+1) b s).next ≠ ([] : List (ReplicaPattern k)) ∧
      ∀ c, List.Mem c (patternExtension (k+1) b s).next → ValidReplicaPattern k c
    rcases patternExtension_cases k (fun _ _ => ()) () b s with
      ⟨hn,_⟩|⟨pre,post,c,t,hb',hn,_⟩
    · erw [hn]
      refine ⟨?_,?_⟩
      · change (b ++ [singletonReplicaPattern k] : List (ReplicaPattern k)) ≠ []
        simp
      · intro c hc
        rcases List.mem_append.mp hc with hc|hc
        · exact hb.2 c hc
        · rw [List.mem_singleton] at hc
          subst c
          exact singletonReplicaPattern_valid k
    · erw [hn]
      refine ⟨?_,?_⟩
      · change (pre ++ (patternExtension k c t).next :: post : List (ReplicaPattern k)) ≠ []
        simp
      · intro d hd
        rcases List.mem_append.mp hd with hd|hd
        · exact hb.2 d (by rw [hb']; exact List.mem_append_left _ hd)
        · rcases List.mem_cons.mp hd with rfl|hd
          · exact ih c (hb.2 c (by rw [hb']; simp)) t
          · exact hb.2 d (by rw [hb']; simp [hd])

lemma patternExtension_blocks_valid (k : ℕ) (bs : List (ReplicaPattern k))
    (hbs : ∀ c ∈ bs, ValidReplicaPattern k c) (s : PatternSite (k+1) bs) :
    ∀ c, List.Mem c (patternExtension (k+1) bs s).next → ValidReplicaPattern k c := by
  rcases patternExtension_cases k (fun _ _ => ()) () bs s with
    ⟨hn,_⟩|⟨pre,post,c,t,hb',hn,_⟩
  · erw [hn]
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact hbs c hc
    · rw [List.mem_singleton] at hc
      subst c
      exact singletonReplicaPattern_valid k
  · erw [hn]
    intro d hd
    rcases List.mem_append.mp hd with hd|hd
    · exact hbs d (by rw [hb']; exact List.mem_append_left _ hd)
    · rcases List.mem_cons.mp hd with rfl|hd
      · exact patternExtension_valid_generic k c (hbs c (by rw [hb']; simp)) t
      · exact hbs d (by rw [hb']; simp [hd])

end MicroscopicJamming

end

end OAI
