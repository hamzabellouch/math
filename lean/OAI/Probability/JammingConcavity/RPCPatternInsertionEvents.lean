import Mathlib
import OAI.Probability.JammingConcavity.RPCPatternExtension

namespace OAI

/-! R P C Pattern Insertion Events. -/

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

lemma rpcSamplePattern_insert_left_iff (k : ℕ) (b : ReplicaPattern k)
    (bs : List (ReplicaPattern k)) (hb : ValidReplicaPattern k b)
    (hbs : ∀ c ∈ bs, ValidReplicaPattern k c)
    (x : PatternIndex (k+1) (b::bs) → CascadePath (k+1)) (y : CascadePath (k+1))
    (a : CloudLabel) (ha : ∀ j : PatternIndex k b, (x ⟨0,j⟩).1=a)
    (ht : RPCSamplePattern (k+1) bs (fun j => x ⟨j.1.succ,j.2⟩))
    (hne : ∀ (i : Fin bs.length) (j : PatternIndex k (bs.get i)), (x ⟨i.succ,j⟩).1≠a)
    (s : PatternSite k b) :
    RPCSamplePattern (k+1) (patternExtension (k+1) (b::bs) (.inl s)).next
      (insertedSample (patternExtension (k+1) (b::bs) (.inl s)) x y) ↔
      y.1=a ∧ RPCSamplePattern k (patternExtension k b s).next
        (insertedSample (patternExtension k b s) (fun j => (x ⟨0,j⟩).2) y.2) := by
  have H (j : PatternIndex k (patternExtension k b s).next) :=
    insertedSample_left_head b bs s x y j
  have T (i : Fin bs.length) (j : PatternIndex k (bs.get i)) :=
    insertedSample_left_tail b bs s x y i j
  have D (j : PatternIndex k (patternExtension k b s).next) :=
    congrFun (insertedSample_comp (patternExtension k b s) (fun j => x ⟨0,j⟩) y Prod.snd) j
  obtain ⟨j₀⟩ := patternIndex_nonempty k b hb
  constructor
  · intro h
    obtain ⟨a',ha',hp',_,_⟩ := (rpcSamplePattern_cons_iff k _ bs hbs _).mp h
    have hr := (insertedSample_forall (patternExtension k b s) (fun j => x ⟨0,j⟩) y
      (fun v => v.1=a')).mp (fun j => (congrArg Prod.fst (H j)).symm.trans (ha' j))
    have heq : a'=a := (hr.2 j₀).symm.trans (ha j₀)
    subst a'
    refine ⟨hr.1,?_⟩
    exact (rpcSamplePattern_congr (fun j => (congrArg Prod.snd (H j)).trans (D j))).mp hp'
  · rintro ⟨hy,hp⟩
    apply (rpcSamplePattern_cons_iff k _ bs hbs _).mpr
    refine ⟨a,?_,?_,?_,?_⟩
    · have hr := (insertedSample_forall (patternExtension k b s) (fun j => x ⟨0,j⟩) y
        (fun v => v.1=a)).mpr ⟨hy,ha⟩
      exact fun j => (congrArg Prod.fst (H j)).trans (hr j)
    · exact (rpcSamplePattern_congr (fun j => (congrArg Prod.snd (H j)).trans (D j))).mpr hp
    · exact (rpcSamplePattern_congr (k := k+1) (b := bs) (fun j => T j.1 j.2)).mpr ht
    · intro i j he
      exact hne i j ((congrArg Prod.fst (T i j)).symm.trans he)

lemma rpcSamplePattern_insert_right_iff (k : ℕ) (b : ReplicaPattern k)
    (bs : List (ReplicaPattern k)) (hb : ValidReplicaPattern k b)
    (hbs : ∀ c ∈ bs, ValidReplicaPattern k c)
    (x : PatternIndex (k+1) (b::bs) → CascadePath (k+1)) (y : CascadePath (k+1))
    (a : CloudLabel) (ha : ∀ j : PatternIndex k b, (x ⟨0,j⟩).1=a)
    (hp : RPCSamplePattern k b (fun j => (x ⟨0,j⟩).2))
    (hne : ∀ (i : Fin bs.length) (j : PatternIndex k (bs.get i)), (x ⟨i.succ,j⟩).1≠a)
    (s : PatternSite (k+1) bs) :
    RPCSamplePattern (k+1) (patternExtension (k+1) (b::bs) (.inr s)).next
      (insertedSample (patternExtension (k+1) (b::bs) (.inr s)) x y) ↔
      y.1≠a ∧ RPCSamplePattern (k+1) (patternExtension (k+1) bs s).next
        (insertedSample (patternExtension (k+1) bs s) (fun j => x ⟨j.1.succ,j.2⟩) y) := by
  have H (j : PatternIndex k b) := insertedSample_right_head b bs s x y j
  have T (j : PatternIndex (k+1) (patternExtension (k+1) bs s).next) :=
    insertedSample_right_tail b bs s x y j.1 j.2
  have hv := patternExtension_blocks_valid k bs hbs s
  obtain ⟨j₀⟩ := patternIndex_nonempty k b hb
  constructor
  · intro h
    obtain ⟨a',ha',_,ht',hne'⟩ := (rpcSamplePattern_cons_iff k b _ hv _).mp h
    have heq : a'=a := (ha' j₀).symm.trans ((congrArg Prod.fst (H j₀)).trans (ha j₀))
    subst a'
    have hnew : ∀ j, (insertedSample (patternExtension (k+1) bs s)
        (fun j => x ⟨j.1.succ,j.2⟩) y j).1≠a := by
      intro j he
      exact hne' j.1 j.2 ((congrArg Prod.fst (T j)).trans he)
    refine ⟨((insertedSample_forall (patternExtension (k+1) bs s) (fun j => x ⟨j.1.succ,j.2⟩) y (fun v => v.1≠a)).mp hnew).1,?_⟩
    exact (rpcSamplePattern_congr T).mp ht'
  · rintro ⟨hy,ht⟩
    apply (rpcSamplePattern_cons_iff k b _ hv _).mpr
    refine ⟨a,?_,?_,?_,?_⟩
    · exact fun j => (congrArg Prod.fst (H j)).trans (ha j)
    · exact (rpcSamplePattern_congr (fun j => congrArg Prod.snd (H j))).mpr hp
    · exact (rpcSamplePattern_congr T).mpr ht
    · have hnew := (insertedSample_forall (patternExtension (k+1) bs s)
        (fun j => x ⟨j.1.succ,j.2⟩) y (fun v => v.1≠a)).mpr
          ⟨hy,fun j => hne j.1 j.2⟩
      intro i j he
      exact hnew ⟨i,j⟩ ((congrArg Prod.fst (T ⟨i,j⟩)).symm.trans he)

 

lemma rpcSamplePattern_unique_insertion (k : ℕ) (b : ReplicaPattern k)
    (hb : ValidReplicaPattern k b)
    (x : PatternIndex k b → CascadePath k) (hx : RPCSamplePattern k b x)
    (y : CascadePath k) :
    ∃! s : PatternSite k b, RPCSamplePattern k (patternExtension k b s).next
      (insertedSample (patternExtension k b s) x y) := by
  induction k with
  | zero =>
    refine ⟨PUnit.unit,?_,?_⟩
    · trivial
    · intro s _; exact Subsingleton.elim (α := PUnit) _ _
  | succ k ih =>
    change List (ReplicaPattern k) at b
    have aux (bs : List (ReplicaPattern k)) (hbs : ∀ c ∈ bs, ValidReplicaPattern k c)
        (z : PatternIndex (k+1) bs → CascadePath (k+1)) (hz : RPCSamplePattern (k+1) bs z) :
        ∃! s : PatternSite (k+1) bs, RPCSamplePattern (k+1) (patternExtension (k+1) bs s).next
          (insertedSample (patternExtension (k+1) bs s) z y) := by
      induction bs with
      | nil =>
        refine ⟨PUnit.unit,?_,?_⟩
        · exact rpcSamplePattern_singleton (k+1) _
        · intro s _; exact Subsingleton.elim (α := PUnit) _ _
      | cons c cs iht =>
        have hc := hbs c (by simp)
        have hcs : ∀ d ∈ cs, ValidReplicaPattern k d := fun d hd => hbs d (by simp [hd])
        obtain ⟨a,ha,hp,ht,hne⟩ := (rpcSamplePattern_cons_iff k c cs hcs z).mp hz
        by_cases hya : y.1=a
        · obtain ⟨s,hs,hu⟩ := ih c hc (fun j => (z ⟨0,j⟩).2) hp y.2
          refine ⟨.inl s,(rpcSamplePattern_insert_left_iff k c cs hc hcs z y a ha ht hne s).mpr ⟨hya,hs⟩,?_⟩
          intro t h
          rcases t with t|t
          · exact congrArg Sum.inl (hu t ((rpcSamplePattern_insert_left_iff k c cs hc hcs z y a ha ht hne t).mp h).2)
          · exact (((rpcSamplePattern_insert_right_iff k c cs hc hcs z y a ha hp hne t).mp h).1 hya).elim
        · obtain ⟨s,hs,hu⟩ := iht hcs (fun j => z ⟨j.1.succ,j.2⟩) ht
          refine ⟨.inr s,(rpcSamplePattern_insert_right_iff k c cs hc hcs z y a ha hp hne s).mpr ⟨hya,hs⟩,?_⟩
          intro t h
          rcases t with t|t
          · exact (hya ((rpcSamplePattern_insert_left_iff k c cs hc hcs z y a ha ht hne t).mp h).1).elim
          · exact congrArg Sum.inr (hu t ((rpcSamplePattern_insert_right_iff k c cs hc hcs z y a ha hp hne t).mp h).2)
    exact aux b hb.2 x hx

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def freshPatternSite (k : ℕ) : (bs : List (ReplicaPattern k)) → PatternSite (k+1) bs
  | [] => PUnit.unit
  | _::bs => .inr (freshPatternSite k bs)

def childPatternSite (k : ℕ) : (bs : List (ReplicaPattern k)) →
    (i : Fin bs.length) → PatternSite k (bs.get i) → PatternSite (k+1) bs
  | [],i => Fin.elim0 i
  | _::bs,i => Fin.cases (fun s => .inl s) (fun i s => .inr (childPatternSite k bs i s)) i

lemma patternSite_fresh_or_child (k : ℕ) (bs : List (ReplicaPattern k)) (s : PatternSite (k+1) bs) :
    s=freshPatternSite k bs ∨ ∃ (i : Fin bs.length) (t : PatternSite k (bs.get i)), s=childPatternSite k bs i t := by
  induction bs with
  | nil => exact Or.inl (Subsingleton.elim (α:=PUnit) _ _)
  | cons b bs ih =>
    rcases s with s|s
    · exact Or.inr ⟨0,s,rfl⟩
    · rcases ih s with hs|⟨i,t,hs⟩
      · exact Or.inl (congrArg Sum.inr hs)
      · exact Or.inr ⟨i.succ,t,congrArg Sum.inr hs⟩

lemma patternSiteFold_fresh {k : ℕ} {A : Type*}
    (g : (b : ReplicaPattern k) → PatternSite k b → A) (d : A) (bs : List (ReplicaPattern k)) :
    patternSiteFold k g d bs (freshPatternSite k bs)=d := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact ih

lemma patternSiteFold_child {k : ℕ} {A : Type*}
    (g : (b : ReplicaPattern k) → PatternSite k b → A) (d : A) (bs : List (ReplicaPattern k))
    (i : Fin bs.length) (s : PatternSite k (bs.get i)) :
    patternSiteFold k g d bs (childPatternSite k bs i s)=g (bs.get i) s := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b bs ih =>
    refine Fin.cases ?_ (fun i => ?_) i s
    · intro s; rfl
    · intro s; exact ih i s

lemma rpcSamplePattern_insert_fresh_iff (k : ℕ) (bs : List (ReplicaPattern k))
    (hbs : ∀ b ∈ bs, ValidReplicaPattern k b)
    (x : PatternIndex (k+1) bs → CascadePath (k+1)) (y : CascadePath (k+1))
    (a : Fin bs.length → CloudLabel) (ha : Function.Injective a)
    (hx : ∀ i, (∀ j : PatternIndex k (bs.get i), (x ⟨i,j⟩).1=a i) ∧
       RPCSamplePattern k (bs.get i) (fun j => (x ⟨i,j⟩).2)) :
    RPCSamplePattern (k+1) (patternExtension (k+1) bs (freshPatternSite k bs)).next
      (insertedSample (patternExtension (k+1) bs (freshPatternSite k bs)) x y) ↔
      ∀ i, y.1≠a i := by
  induction bs with
  | nil =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; exact rpcSamplePattern_singleton (k+1) _
  | cons b bs ih =>
    have hb := hbs b (by simp)
    have ht : ∀ c ∈ bs, ValidReplicaPattern k c := fun c hc => hbs c (by simp [hc])
    have hneq : ∀ (i : Fin bs.length) (j : PatternIndex k (bs.get i)), (x ⟨i.succ,j⟩).1≠a 0 := by
      intro i j he
      exact Fin.succ_ne_zero i (ha (((hx i.succ).1 j).symm.trans he))
    have he := rpcSamplePattern_insert_right_iff k b bs hb ht x y (a 0) (hx 0).1 (hx 0).2
      hneq (freshPatternSite k bs)
    refine he.trans ?_
    have hi := ih ht (fun j => x ⟨j.1.succ,j.2⟩) (fun i => a i.succ)
      (ha.comp (Fin.succ_injective _)) (fun i => hx i.succ)
    rw [hi]
    constructor
    · rintro ⟨h0,ht⟩ i
      exact Fin.cases h0 ht i
    · intro h
      exact ⟨h 0,fun i => h i.succ⟩

lemma rpcSamplePattern_insert_child_iff (k : ℕ) (bs : List (ReplicaPattern k))
    (hbs : ∀ b ∈ bs, ValidReplicaPattern k b)
    (x : PatternIndex (k+1) bs → CascadePath (k+1)) (y : CascadePath (k+1))
    (a : Fin bs.length → CloudLabel) (ha : Function.Injective a)
    (hx : ∀ i, (∀ j : PatternIndex k (bs.get i), (x ⟨i,j⟩).1=a i) ∧
       RPCSamplePattern k (bs.get i) (fun j => (x ⟨i,j⟩).2))
    (i : Fin bs.length) (s : PatternSite k (bs.get i)) :
    RPCSamplePattern (k+1) (patternExtension (k+1) bs (childPatternSite k bs i s)).next
      (insertedSample (patternExtension (k+1) bs (childPatternSite k bs i s)) x y) ↔
      y.1=a i ∧ RPCSamplePattern k (patternExtension k (bs.get i) s).next
        (insertedSample (patternExtension k (bs.get i) s) (fun j => (x ⟨i,j⟩).2) y.2) := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b bs ih =>
    have hb := hbs b (by simp)
    have ht : ∀ c ∈ bs, ValidReplicaPattern k c := fun c hc => hbs c (by simp [hc])
    have hneq : ∀ (i : Fin bs.length) (j : PatternIndex k (bs.get i)), (x ⟨i.succ,j⟩).1≠a 0 := by
      intro i j he
      exact Fin.succ_ne_zero i (ha (((hx i.succ).1 j).symm.trans he))
    refine Fin.cases ?_ (fun i => ?_) i s
    · intro s
      apply rpcSamplePattern_insert_left_iff k b bs hb ht x y (a 0) (hx 0).1
      · exact ⟨fun i => a i.succ,ha.comp (Fin.succ_injective _),fun i => hx i.succ⟩
      · exact hneq
    · intro s
      have he := rpcSamplePattern_insert_right_iff k b bs hb ht x y (a 0) (hx 0).1 (hx 0).2
        hneq (childPatternSite k bs i s)
      refine he.trans ?_
      have hi := ih ht (fun j => x ⟨j.1.succ,j.2⟩) (fun i => a i.succ)
        (ha.comp (Fin.succ_injective _)) (fun i => hx i.succ) i s
      rw [hi]
      constructor
      · exact fun h => h.2
      · rintro ⟨hy,hp⟩
        refine ⟨?_,hy,hp⟩
        intro h
        exact Fin.succ_ne_zero i (ha (hy.symm.trans h))

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma rankCluster_card_of_embedding {n k : ℕ} (R : Fin n → Fin n → ℝ)
    (p : Fin n) (η : ℝ) (b : ReplicaPattern k)
    (e : PatternIndex k b → Fin n) (he : Function.Injective e)
    (hc : ∀ q, η ≤ R p q ↔ ∃ j, e j=q) :
    (rankCluster R p η).card=replicaPatternSize k b := by
  have hs : rankCluster R p η=Finset.univ.image e := by
    ext q
    simpa only [rankCluster,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_image,exists_true_left] using hc q
  rw [hs,Finset.card_image_of_injective _ he,Finset.card_univ,patternIndex_card]

 
lemma rankPattern_children {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (ms : List ℝ) (m η : ℝ) (hm : m ≤ 1) (hηm : η ≤ m)
    (p : Fin n) (bs : List (ReplicaPattern ms.length))
    (hb : ValidReplicaPattern (ms.length+1) bs)
    (e : PatternIndex (ms.length+1) bs → Fin n) (he : Function.Injective e)
    (hc : ∀ q, η ≤ R p q ↔ ∃ j, e j=q)
    (hx : RPCSamplePattern (ms.length+1) bs (fun j => rankProfilePath (m::ms) (R (e j)))) :
    ∃ (a : Fin bs.length → CloudLabel) (c : Fin bs.length → Fin n),
      Function.Injective a ∧
      (∀ i, (∀ j : PatternIndex ms.length (bs.get i), rankProfileCode m (R (e ⟨i,j⟩))=a i) ∧
        RPCSamplePattern ms.length (bs.get i) (fun j => rankProfilePath ms (R (e ⟨i,j⟩)))) ∧
      (∀ i, rankProfileCode m (R (c i))=a i) ∧
      (∀ i, η ≤ R p (c i)) ∧
      (∀ i j, i ≠ j → R (c i) (c j) < m) ∧
      (∀ i q, m ≤ R (c i) q ↔ ∃ j : PatternIndex ms.length (bs.get i), e ⟨i,j⟩=q) ∧
      (rankCluster R p η).card=∑ i, (rankCluster R (c i) m).card := by
  obtain ⟨a,ha,hx⟩ := hx
  let r (i : Fin bs.length) : PatternIndex ms.length (bs.get i) :=
    Classical.choice (patternIndex_nonempty _ _ (hb.2 _ (List.get_mem _ _)))
  let c (i : Fin bs.length) : Fin n := e ⟨i,r i⟩
  have hcr (i : Fin bs.length) : rankProfileCode m (R (c i))=a i := (hx i).1 (r i)
  have hcp (i : Fin bs.length) : η ≤ R p (c i) := (hc _).mpr ⟨⟨i,r i⟩,rfl⟩
  have hchild (i : Fin bs.length) (q : Fin n) :
      m ≤ R (c i) q ↔ ∃ j : PatternIndex ms.length (bs.get i), e ⟨i,j⟩=q := by
    constructor
    · intro hi
      have hq : η ≤ R p q := (le_min (hcp i) (hηm.trans hi)).trans (hR.2.2.2 p (c i) q)
      obtain ⟨⟨l,j⟩,rfl⟩ := (hc q).mp hq
      have hl : i=l := ha (hcr i |>.symm.trans
        (((rankProfileCode_rows hR (c i) (e ⟨l,j⟩) m hm).mpr hi).trans ((hx l).1 j)))
      subst l
      exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩
      exact (rankProfileCode_rows hR (c i) (e ⟨i,j⟩) m hm).mp
        ((hcr i).trans ((hx i).1 j).symm)
  refine ⟨a,c,ha,hx,hcr,hcp,?_,hchild,?_⟩
  · intro i j hij
    apply lt_of_not_ge
    intro h
    exact hij (ha ((hcr i).symm.trans
      (((rankProfileCode_rows hR (c i) (c j) m hm).mpr h).trans (hcr j))))
  · rw [rankCluster_card_of_embedding (k:=ms.length+1) R p η bs e he hc]
    have hs (i : Fin bs.length) : (rankCluster R (c i) m).card=
        replicaPatternSize ms.length (bs.get i) :=
      rankCluster_card_of_embedding R (c i) m (bs.get i) (fun j => e ⟨i,j⟩)
        (fun j l h => eq_of_heq (Sigma.mk.inj_iff.mp (he h)).2) (hchild i)
    simp_rw [hs]
    change (bs.map (replicaPatternSize ms.length)).sum = ∑ i, replicaPatternSize ms.length (bs.get i)
    simpa only [List.ofFn_getElem_eq_map,List.get_eq_getElem] using
      (Fin.sum_ofFn (fun i : Fin bs.length => replicaPatternSize ms.length (bs.get i)))

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

def rankPatternInsertEvent {n : ℕ} (R : Fin (n+1) → Fin (n+1) → ℝ)
    (ms : List ℝ) (η : ℝ) (p : Fin (n+1)) (b : ReplicaPattern ms.length)
    (e : PatternIndex ms.length b → Fin (n+1)) (s : PatternSite ms.length b) :
    Set (Fin (n+1) × ℝ) := {z | η ≤ rankLink R z.1 z.2 p ∧
      RPCSamplePattern ms.length (patternExtension ms.length b s).next
        (insertedSample (patternExtension ms.length b s)
          (fun j => rankProfilePath ms (R (e j))) (rankProfilePath ms (rankLink R z.1 z.2)))}

lemma rankPatternInsertEvent_real {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hηms : ∀ m ∈ ms, η < m) (p : Fin (n+1)) (b : ReplicaPattern ms.length)
    (hb : ValidReplicaPattern ms.length b) (e : PatternIndex ms.length b → Fin (n+1))
    (he : Function.Injective e) (hc : ∀ q, η ≤ R p q ↔ ∃ j, e j=q)
    (hx : RPCSamplePattern ms.length b (fun j => rankProfilePath ms (R (e j))))
    (s : PatternSite ms.length b) :
    (rankInnovationLaw n).real (rankPatternInsertEvent R ms η p b e s) =
      patternSiteWeight ms η b s/((n:ℝ)+1) := by
  induction ms generalizing η p with
  | nil =>
    have hs : rankPatternInsertEvent R [] η p b e s=rankJoinEvent R p η := by
      ext z
      change (_ ∧ True) ↔ _
      simp [rankJoinEvent]
    rw [hs,rankJoinEvent_real_nonneg hR p hη hη1,
      rankCluster_card_of_embedding R p η b e he hc]
    rfl
  | cons m ms ih =>
    have hm := h01 m (by simp)
    have htms := (List.pairwise_cons.mp hms).2
    have ht01 : ∀ t ∈ ms, 0 < t ∧ t < 1 := fun t ht => h01 t (by simp [ht])
    have hηm : η < m := hηms m (by simp)
    change List (ReplicaPattern ms.length) at b
    obtain ⟨a,c,ha,hx,hcr,hcp,hsep,hchild,hcard⟩ :=
      rankPattern_children hR ms m η hm.2.le hηm.le p b hb e he hc hx
    have heq (z : Fin (n+1) × ℝ) (i : Fin b.length) :
        rankProfileCode m (rankLink R z.1 z.2)=a i ↔ m ≤ rankLink R z.1 z.2 (c i) := by
      rw [← hcr i]
      exact rankProfileCode_link hR (c i) z.1 z.2 m hm.2.le
    rcases patternSite_fresh_or_child ms.length b s with rfl|⟨i,t,rfl⟩
    · have hs : rankPatternInsertEvent R (m::ms) η p b e (freshPatternSite ms.length b)=
          rankJoinEvent R p η \ ⋃ i, rankJoinEvent R (c i) m := by
        ext z
        change (_ ∧ _) ↔ _
        have hf := rpcSamplePattern_insert_fresh_iff ms.length b hb.2
          (fun j => rankProfilePath (m::ms) (R (e j)))
          (rankProfilePath (m::ms) (rankLink R z.1 z.2)) a ha hx
        erw [hf]
        simp only [Set.mem_sdiff,rankJoinEvent,mem_ofPred_eq,mem_iUnion,not_exists]
        exact and_congr_right fun _ => forall_congr' fun i => not_congr (heq z i)
      rw [hs,rankFreshBranch_real hR p c hη hηm.le hm.1 hm.2.le hcp hsep hcard]
      change _=patternSiteFold ms.length _ _ b (freshPatternSite ms.length b)/_
      rw [patternSiteFold_fresh]
    · have hs : rankPatternInsertEvent R (m::ms) η p b e (childPatternSite ms.length b i t)=
          rankPatternInsertEvent R ms m (c i) (b.get i) (fun j => e ⟨i,j⟩) t := by
        ext z
        change (_ ∧ _) ↔ (_ ∧ _)
        have hf := rpcSamplePattern_insert_child_iff ms.length b hb.2
          (fun j => rankProfilePath (m::ms) (R (e j)))
          (rankProfilePath (m::ms) (rankLink R z.1 z.2)) a ha hx i t
        erw [hf]
        change (_ ∧ (rankProfileCode m (rankLink R z.1 z.2)=a i ∧ _)) ↔ (_ ∧ _)
        rw [heq z i]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨rankJoinEvent_subset hR p (c i) hηm.le (hcp i) h.1,h⟩
      rw [hs]
      change _=patternSiteFold ms.length _ _ b (childPatternSite ms.length b i t)/_
      rw [patternSiteFold_child]
      exact ih htms ht01 m hm.1.le hm.2.le (List.pairwise_cons.mp hms).1 (c i)
        (b.get i) (hb.2 _ (List.get_mem _ _)) (fun j => e ⟨i,j⟩)
        (fun j l h => eq_of_heq (Sigma.mk.inj_iff.mp (he h)).2) (hchild i) (hx i).2 t

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

 
structure PatternLabelling (k n : ℕ) where
  pattern : ReplicaPattern k
  index : Fin (n+1) ≃ PatternIndex k pattern

def PatternLabelling.singleton (k : ℕ) : PatternLabelling k 0 :=
  ⟨singletonReplicaPattern k,Fintype.equivOfCardEq (by rw [Fintype.card_fin,patternIndex_singleton_card])⟩

def PatternLabelling.extend {k n : ℕ} (h : PatternLabelling k n) (s : PatternSite k h.pattern) :
    PatternLabelling k (n+1) :=
  ⟨(patternExtension k h.pattern s).next,finSuccEquivLast.trans
    ((Equiv.optionCongr h.index).trans (patternExtension k h.pattern s).index)⟩

inductive ReachablePatternLabelling (k : ℕ) : {n : ℕ} → PatternLabelling k n → Prop
  | singleton : ReachablePatternLabelling k (PatternLabelling.singleton k)
  | extend {n : ℕ} {h : PatternLabelling k n} (hh : ReachablePatternLabelling k h)
      (s : PatternSite k h.pattern) : ReachablePatternLabelling k (h.extend s)

lemma ReachablePatternLabelling.valid {k n : ℕ} {h : PatternLabelling k n}
    (hh : ReachablePatternLabelling k h) : ValidReplicaPattern k h.pattern := by
  induction hh with
  | singleton => exact singletonReplicaPattern_valid k
  | extend hh s ih => exact patternExtension_valid_generic k _ ih s

lemma PatternLabelling.size {k n : ℕ} (h : PatternLabelling k n) :
    replicaPatternSize k h.pattern=n+1 := by
  rw [← patternIndex_card,← Fintype.card_congr h.index,Fintype.card_fin]

lemma PatternLabelling.extend_old {k n : ℕ} (h : PatternLabelling k n)
    (s : PatternSite k h.pattern) (i : Fin (n+1)) :
    (h.extend s).index i.castSucc = (patternExtension k h.pattern s).index (some (h.index i)) := by
  exact congrArg (fun o => (patternExtension k h.pattern s).index ((Equiv.optionCongr h.index) o))
    (finSuccEquivLast_castSucc i)

lemma PatternLabelling.extend_new {k n : ℕ} (h : PatternLabelling k n)
    (s : PatternSite k h.pattern) :
    (h.extend s).index (Fin.last (n+1))=(patternExtension k h.pattern s).index none := by
  exact congrArg (fun o => (patternExtension k h.pattern s).index ((Equiv.optionCongr h.index) o))
    (finSuccEquivLast_last (n := n+1))

lemma PatternLabelling.extend_sample {k n : ℕ} (h : PatternLabelling k n)
    (s : PatternSite k h.pattern) {A : Type*} (x : Fin (n+2) → A) :
    insertedSample (patternExtension k h.pattern s)
      (fun j => x (h.index.symm j).castSucc) (x (Fin.last (n+1))) =
      fun j => x ((h.extend s).index.symm j) := by
  funext j
  obtain ⟨i,rfl⟩ := (h.extend s).index.surjective j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Equiv.symm_apply_apply,h.extend_new,insertedSample_new]
  · rw [Equiv.symm_apply_apply,h.extend_old,insertedSample_old,Equiv.symm_apply_apply]

 

lemma reachablePatternLabelling_covers (k n : ℕ) (x : Fin (n+1) → CascadePath k) :
    ∃ h : PatternLabelling k n, ReachablePatternLabelling k h ∧
      RPCSamplePattern k h.pattern (fun j => x (h.index.symm j)) := by
  induction n with
  | zero => exact ⟨PatternLabelling.singleton k,.singleton,rpcSamplePattern_singleton k _⟩
  | succ n ih =>
    obtain ⟨h,hh,hx⟩ := ih (fun i => x i.castSucc)
    obtain ⟨s,hs,_⟩ := rpcSamplePattern_unique_insertion k h.pattern hh.valid _ hx (x (Fin.last (n+1)))
    refine ⟨h.extend s,.extend hh s,?_⟩
    rwa [h.extend_sample s x] at hs

def PatternLabelling.signature {k n : ℕ} (h : PatternLabelling k n) : Fin (n+1) → Fin (n+1) → ℕ :=
  fun i j => patternSignature k h.pattern (h.index i) (h.index j)

lemma PatternLabelling.sample_iff_signature {k n : ℕ} (h : PatternLabelling k n)
    (hh : ValidReplicaPattern k h.pattern) (x : Fin (n+1) → CascadePath k) :
    RPCSamplePattern k h.pattern (fun j => x (h.index.symm j)) ↔
      ∀ i j, cascadeSharedEdges k (x i) (x j)=h.signature i j := by
  rw [rpcSamplePattern_iff_signature k h.pattern hh]
  constructor
  · intro hx i j
    simpa only [Equiv.symm_apply_apply,PatternLabelling.signature] using hx (h.index i) (h.index j)
  · intro hx i j
    simpa only [PatternLabelling.signature,Equiv.apply_symm_apply] using hx (h.index.symm i) (h.index.symm j)

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma rpcSamplePattern_delete (k : ℕ) (b : ReplicaPattern k) (hb : ValidReplicaPattern k b)
    (s : PatternSite k b) (x : PatternIndex k b → CascadePath k) (y : CascadePath k)
    (h : RPCSamplePattern k (patternExtension k b s).next
      (insertedSample (patternExtension k b s) x y)) : RPCSamplePattern k b x := by
  induction k with
  | zero => trivial
  | succ k ih =>
    change List (ReplicaPattern k) at b
    have aux : ∀ (bs : List (ReplicaPattern k)), (∀ b ∈ bs, ValidReplicaPattern k b) →
        ∀ (s : PatternSite (k+1) bs) (x : PatternIndex (k+1) bs → CascadePath (k+1))
        (y : CascadePath (k+1)),
        RPCSamplePattern (k+1) (patternExtension (k+1) bs s).next
          (insertedSample (patternExtension (k+1) bs s) x y) → RPCSamplePattern (k+1) bs x := by
      intro bs
      induction bs with
      | nil => intro _ _ x _ _; exact rpcSamplePattern_nil k x
      | cons b bs it =>
        intro hb s x y h
        have hbt : ∀ c ∈ bs, ValidReplicaPattern k c := fun c hc => hb c (by simp [hc])
        rcases s with s|s
        · have H (j : PatternIndex k (patternExtension k b s).next) :=
            insertedSample_left_head b bs s x y j
          have T (i : Fin bs.length) (j : PatternIndex k (bs.get i)) :=
            insertedSample_left_tail b bs s x y i j
          have D (j : PatternIndex k (patternExtension k b s).next) :=
            congrFun (insertedSample_comp (patternExtension k b s) (fun j => x ⟨0,j⟩) y Prod.snd) j
          obtain ⟨a,hr,hp,ht,hn⟩ := (rpcSamplePattern_cons_iff k _ bs hbt _).mp h
          have hrold := ((insertedSample_forall (patternExtension k b s) (fun j => x ⟨0,j⟩) y
            (fun v => v.1=a)).mp (fun j => (congrArg Prod.fst (H j)).symm.trans (hr j))).2
          have hpnew := (rpcSamplePattern_congr (fun j => (congrArg Prod.snd (H j)).trans (D j))).mp hp
          refine (rpcSamplePattern_cons_iff k b bs hbt x).mpr ⟨a,hrold,?_,?_,?_⟩
          · exact ih b (hb b (by simp)) s (fun j => (x ⟨0,j⟩).2) y.2 hpnew
          · exact (rpcSamplePattern_congr (k:=k+1) (b:=bs) (fun j => T j.1 j.2)).mp ht
          · intro i j he
            exact hn i j ((congrArg Prod.fst (T i j)).trans he)
        · have H (j : PatternIndex k b) := insertedSample_right_head b bs s x y j
          have T (j : PatternIndex (k+1) (patternExtension (k+1) bs s).next) :=
            insertedSample_right_tail b bs s x y j.1 j.2
          have hv := patternExtension_blocks_valid k bs hbt s
          obtain ⟨a,hr,hp,ht,hn⟩ := (rpcSamplePattern_cons_iff k b _ hv _).mp h
          have htnew := (rpcSamplePattern_congr T).mp ht
          have hall : ∀ j, (insertedSample (patternExtension (k+1) bs s)
              (fun j => x ⟨j.1.succ,j.2⟩) y j).1≠a := by
            intro j he
            exact hn j.1 j.2 ((congrArg Prod.fst (T j)).trans he)
          have hneq := ((insertedSample_forall (patternExtension (k+1) bs s)
            (fun j => x ⟨j.1.succ,j.2⟩) y (fun v => v.1≠a)).mp hall).2
          refine (rpcSamplePattern_cons_iff k b bs hbt x).mpr ⟨a,?_,?_,?_,?_⟩
          · exact fun j => (congrArg Prod.fst (H j)).symm.trans (hr j)
          · exact (rpcSamplePattern_congr (fun j => congrArg Prod.snd (H j))).mp hp
          · exact it hbt s _ y htnew
          · exact fun i j => hneq ⟨i,j⟩
    exact aux b hb.2 s x y h

lemma PatternLabelling.delete_sample {k n : ℕ} (h : PatternLabelling k n)
    (hh : ValidReplicaPattern k h.pattern) (s : PatternSite k h.pattern)
    (x : Fin (n+2) → CascadePath k)
    (hx : RPCSamplePattern k (h.extend s).pattern (fun j => x ((h.extend s).index.symm j))) :
    RPCSamplePattern k h.pattern (fun j => x (h.index.symm j).castSucc) := by
  rw [← h.extend_sample s x] at hx
  exact rpcSamplePattern_delete k h.pattern hh s _ _ hx

end MicroscopicJamming

 
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace MicroscopicJamming

def rankMesh (n : ℕ) : List ℝ := (List.range n).map (fun (i : ℕ) => ((i:ℝ)+1)/((n:ℝ)+1))

def rankMeshValue (n : ℕ) (u : ℝ) : ℝ := (rpcStepLevel (rankMesh n) u : ℝ)/((n:ℝ)+1)

lemma rankMesh_increasing (n : ℕ) : (rankMesh n).Pairwise (· < ·) := by
  unfold rankMesh
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {i j} hij =>
    (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
      (by exact_mod_cast Nat.add_lt_add_right hij 1)

lemma rankMesh_valid (n : ℕ) (m : ℝ) (hm : m ∈ rankMesh n) : 0 < m ∧ m < 1 := by
  unfold rankMesh at hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
  have hin : i<n := List.mem_range.mp hi
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    exact_mod_cast Nat.add_lt_add_right hin 1

lemma range_filter_lt_length (n k : ℕ) :
    ((List.range n).filter (fun i => i<k)).length=min n k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filter_append,List.length_append,ih]
    by_cases hn : n<k
    · simp [hn, Nat.min_eq_left (Nat.le_of_lt hn)]
    · have hk : k≤n := by omega
      simp [hn, Nat.min_eq_right hk,Nat.min_eq_right (hk.trans (Nat.le_succ n))]

lemma rankMesh_count (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    rpcStepLevel (rankMesh n) u = min n ⌊((n:ℝ)+1)*u⌋₊ := by
  have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hnon : 0 ≤ ((n:ℝ)+1)*u := mul_nonneg hn.le hu
  unfold rpcStepLevel rankMesh
  rw [List.filter_map,List.length_map]
  have he (i : ℕ) : decide ((((i:ℝ)+1)/((n:ℝ)+1)) ≤ u) =
      decide (i<⌊((n:ℝ)+1)*u⌋₊) := by
    congr 1
    apply propext
    rw [div_le_iff₀ hn,mul_comm u,← Nat.cast_add_one,← Nat.le_floor_iff hnon]
    omega
  simp only [Function.comp_def,he]
  exact range_filter_lt_length _ _

lemma rankMeshValue_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    u-1/((n:ℝ)+1) ≤ rankMeshValue n u ∧ rankMeshValue n u ≤ u := by
  have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hnon : 0 ≤ ((n:ℝ)+1)*u := mul_nonneg hn.le hu.1
  unfold rankMeshValue
  rw [rankMesh_count n hu.1, Nat.cast_min]
  constructor
  · rw [le_div_iff₀ hn,le_min_iff]
    constructor
    · have ha := mul_le_mul_of_nonneg_left hu.2 hn.le
      have hd : (1/((n:ℝ)+1))*((n:ℝ)+1)=1 := by field_simp
      nlinarith
    · have ha := Nat.lt_floor_add_one (((n:ℝ)+1)*u)
      have hd : (1/((n:ℝ)+1))*((n:ℝ)+1)=1 := by field_simp
      nlinarith
  · rw [div_le_iff₀ hn]
    exact (min_le_right _ _).trans ((Nat.floor_le hnon).trans_eq (mul_comm _ _))

lemma rankMeshValue_tendsto {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun n => rankMeshValue n u) atTop (𝓝 u) := by
  have hlo : Tendsto (fun n : ℕ => u-1/((n:ℝ)+1)) atTop (𝓝 u) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => (rankMeshValue_bounds n hu).1) (fun n => (rankMeshValue_bounds n hu).2)

end MicroscopicJamming

end

end OAI
