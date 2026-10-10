import OAI.Probability.FKMaps.ConditionedTrees
import OAI.Probability.FKMaps.NodeMetric

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.TreeCoding

lemma recordTypeAt_congr_prefix {x y : ℕ → ℕ} {N t : ℕ}
    (h : ∀ k  <  N,x k=y k) (ht0 : 0 < t) (htN : t ≤ N) :
    recordTypeAt x t=recordTypeAt y t := by
  have hS := integerSum_congr_prefix h
  unfold recordTypeAt
  rw [h (t-1) (by omega),hS t htN,prefixMaximum_congr (fun k hk => hS k (by omega))]

lemma record_boundary (x y : ℕ → ℕ) {n m : ℕ} (hnm : n ≤ m)
    (hxy : ∀ k  <  n,x k=y k)
    (hmax : ∀ k  ≤  n,integerSum x k ≤ integerSum x n)
    (hmid : ∀ k,n < k → k ≤ m → integerSum y k < integerSum x n)
    (hfin : integerSum x n ≤ integerSum y (m+1)) :
    weakRecords (integerSum y) (m+1)=insert (m+1) (weakRecords (integerSum x) n) ∧
    recordTypeAt y (m+1)=(y m,(integerSum y (m+1)-integerSum x n).toNat) := by
  have hS (k) (hk : k ≤ n) : integerSum x k=integerSum y k := integerSum_congr_prefix hxy k hk
  have hmaxy (k) (hk : k ≤ m) : integerSum y k ≤ integerSum x n := by
    by_cases hkn : k ≤ n
    · rw [← hS k hkn];exact hmax k hkn
    · exact (hmid k (by omega) hk).le
  have hp : prefixMaximum (integerSum y) m=integerSum x n := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun k hk => hmaxy k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    · rw [hS n le_rfl]
      exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))
  refine ⟨?_,by simp only [recordTypeAt,Nat.add_sub_cancel,hp]⟩
  rw [weakRecords_congr_prefix hS]
  ext k
  simp only [mem_weakRecords,Finset.mem_insert]
  constructor
  · rintro ⟨hk0,hkm,hrec⟩
    by_cases hkn : k ≤ n
    · exact Or.inr ⟨hk0,hkn,hrec⟩
    · left
      by_contra he
      have hh := hrec n (by omega)
      rw [← hS n le_rfl] at hh
      have := hmid k (by omega) (by omega)
      omega
  · rintro (rfl | ⟨hk0,hkn,hrec⟩)
    · refine ⟨by omega,le_rfl,?_⟩
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · rfl
      · exact (hmaxy j (by omega)).trans hfin
    · exact ⟨hk0,hkn.trans (by omega),hrec⟩

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open TreeCoding

def labelProfileSum (b : (ℕ×ℕ) → CoreLabel → ℝ) (l : List CoreLabel) : ℝ :=
  ∑ r ∈ weakRecords (integerSum (listStream (l.map CoreLabel.arity).reverse)) l.length,
    b (recordTypeAt (listStream (l.map CoreLabel.arity).reverse) r) (l.reverse[r-1]?.getD none)

lemma labelProfileSum_empty (b : (ℕ×ℕ) → CoreLabel → ℝ) : labelProfileSum b []=0 := by
  simp [labelProfileSum,weakRecords]

lemma labelProfileSum_attach (b : (ℕ×ℕ) → CoreLabel → ℝ) (a f : List CoreLabel) (c : CoreLabel)
    {i : ℕ} (ha : ∀ j  ≤  a.length,0 ≤ prefixSum (PlaneTree.incrementWord (a.map CoreLabel.arity)) j)
    (hf : PlaneTree.SuffixNegative (f.map CoreLabel.arity))
    (hfs : (PlaneTree.incrementWord (f.map CoreLabel.arity)).sum= -(i:ℤ))
    (hik : i < c.arity) :
    labelProfileSum b (c::(f++a))=labelProfileSum b a+b (c.arity,c.arity-1-i) c := by
  let aa := a.map CoreLabel.arity
  let ff := f.map CoreLabel.arity
  let x := listStream aa.reverse
  let y := listStream ((aa.reverse++ff.reverse)++[c.arity])
  let n := a.length
  let m := a.length+f.length
  have hp : ∀ j  <  n,x j=y j := by
    intro j hj
    dsimp [x,y,n,aa] at *
    rw [List.append_assoc]
    exact (listStream_append_prefix _ _ j (by simpa using hj)).symm
  have hS : integerSum x n=(PlaneTree.incrementWord aa).sum := by
    dsimp [x,n,aa]
    convert integerSum_listStream_length (a.map CoreLabel.arity).reverse using 1  <;>
      simp [PlaneTree.incrementWord]
  have hm : ∀ j  ≤  m,integerSum y j=integerSum (listStream (aa.reverse++ff.reverse)) j := by
    intro j hj
    apply integerSum_congr_prefix (N := m) _ j hj
    intro r hr
    exact listStream_append_prefix _ _ r (by simpa [m,aa,ff] using hr)
  have hmid : ∀ j,n < j → j ≤ m → integerSum y j < integerSum x n := by
    intro j hj hjm
    rw [hm j hjm]
    have hsub : j-n ≤ ff.reverse.length := by dsimp [ff,m,n] at *;simp at *;omega
    have he : j=aa.reverse.length+(j-n) := by dsimp [aa,n] at *;simp only [List.length_reverse,List.length_map];omega
    rw [he,integerSum_list_append _ _ hsub]
    rw [show (PlaneTree.incrementWord aa.reverse).sum=(PlaneTree.incrementWord aa).sum by simp [PlaneTree.incrementWord],hS]
    exact add_lt_of_neg_right _ (reverse_word_strict_negative ff hf (by omega) (by simpa using hsub))
  have hfinal : integerSum y (m+1)=integerSum x n+((c.arity:ℤ)-1-i) := by
    dsimp [y,m]
    have he : a.length+f.length+1=(((aa.reverse++ff.reverse)++[c.arity])).length := by simp [aa,ff,Nat.add_assoc]
    rw [he,integerSum_listStream_length,PlaneTree.incrementWord_append,PlaneTree.incrementWord_append]
    simp only [List.sum_append,PlaneTree.incrementWord,List.map_reverse,List.sum_reverse,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [hS]
    unfold PlaneTree.incrementWord
    unfold PlaneTree.incrementWord at hfs
    dsimp only [ff]
    rw [hfs]
    omega
  have hy : y m=c.arity := by
    dsimp [y,m]
    rw [listStream_get (by simp [aa,ff]),List.getElem_append_right (by simp [aa,ff])]
    simp [aa,ff]
  have hmax : ∀ j  ≤  n,integerSum x j ≤ integerSum x n := by
    simpa only [x,n,aa,List.length_map] using list_reverse_prefix_max aa (by simpa [aa] using ha)
  obtain ⟨hr,ht⟩ := record_boundary x y (by dsimp [n,m];omega) hp hmax hmid (by rw [hfinal];omega)
  rw [hy,hfinal,show (integerSum x n+((c.arity:ℤ)-1-i)-integerSum x n).toNat=c.arity-1-i by omega] at ht
  have hword : ((c::(f++a)).map CoreLabel.arity).reverse=(aa.reverse++ff.reverse)++[c.arity] := by
    simp [aa,ff,List.reverse_append]
  unfold labelProfileSum
  rw [hword,show (c::(f++a)).length=m+1 by simp [m,Nat.add_comm]]
  change (∑ r ∈ weakRecords (integerSum y) (m+1),
    b (recordTypeAt y r) ((c::(f++a)).reverse[r-1]?.getD none))=_
  rw [hr,Finset.sum_insert (by intro h;have := (mem_weakRecords _ _ _).mp h;omega)]
  rw [ht]
  have hlast : ((c::(f++a)).reverse[m]?.getD none)=c := by
    simp only [List.reverse_cons,List.reverse_append]
    rw [List.getElem?_append_right (by simp [m])]
    simp [m]
  simp only [Nat.add_sub_cancel,hlast]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hb := (mem_weakRecords _ _ _).mp hr
  rw [← recordTypeAt_congr_prefix hp (by omega) hb.2.1]
  congr 1
  simp only [List.reverse_cons,List.reverse_append,List.append_assoc]
  rw [List.getElem?_append_left (by dsimp [n] at hb;simp;omega)]

lemma toCode_labelProfile (T : CoreTree) (b : (ℕ×ℕ) → CoreLabel → ℝ) {v : ℕ}
    (hv : v ≤ T.labels.length) :
    markedSpineSum b T.toCode hv (fun i => T.labels[i.val])=labelProfileSum b (T.labels.take v) := by
  let l := T.labels.map CoreLabel.arity
  let x := reverseFirst v (arrayStream (codeEmbedding T.labels.length T.toCode))
  let y := listStream (l.take v).reverse
  have hxy : ∀ k  <  v,x k=y k := by
    have hh : ∀ k  <  T.labels.length,arrayStream (codeEmbedding T.labels.length T.toCode) k=listStream l k := by
      intro k hk
      rw [listStream_get (by simpa [l] using hk)]
      simp only [arrayStream,dite_eq_left hk,l,List.getElem_map]
      rfl
    intro k hk
    exact (reverseFirst_prefix_congr hv hh k hk).trans (reverseFirst_list_prefix l (by simpa [l] using hv) k hk)
  unfold markedSpineSum labelProfileSum
  have hlen : (T.labels.take v).length=v := by simp [Nat.min_eq_left hv]
  rw [hlen,List.map_take]
  change _=(∑ r ∈ weakRecords (integerSum y) v,_)
  rw [← weakRecords_congr_prefix (integerSum_congr_prefix hxy)]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro r _
  have hb := (mem_weakRecords _ _ _).mp r.property
  change b (recordTypeAt x r.val) _=b (recordTypeAt y r.val) _
  rw [recordTypeAt_congr_prefix hxy (by omega) hb.2.1]
  congr 1
  rw [List.getElem?_eq_getElem (by simp [hlen];omega),List.getElem_reverse]
  simp only [hlen]
  rw [List.getElem_take]
  congr 1
  simp only [spineRecordVertex]
  omega

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open TreeCoding
attribute [local instance] Classical.propDecidable

def before (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) : List CoreTree :=
  (List.ofFn ts).take i.val

def after (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) : List CoreTree :=
  (List.ofFn ts).drop (i.val+1)

lemma children_split (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    List.ofFn ts=before c ts i++ts i::after c ts i := by
  have h := List.take_append_drop i.val (List.ofFn ts)
  rw [List.drop_eq_getElem_cons (by simp)] at h
  simpa only [before,after,List.getElem_ofFn] using h.symm

lemma before_length (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (before c ts i).length=i.val := by simp [before]

lemma after_length (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (after c ts i).length=c.val.length-1-i.val := by simp [after];omega

lemma labels_split (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (branch c ts).labels=some c::((before c ts i).flatMap labels++(ts i).labels++(after c ts i).flatMap labels) := by
  rw [labels_branch,children_split c ts i,List.flatMap_append,List.flatMap_cons,List.append_assoc]

lemma labels_nonempty (t : CoreTree) : t.labels≠[] := by
  cases t <;> simp [labels]

def nodeIndex : (t : CoreTree) → t.Node → ℕ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩ => 1+((before c ts i).flatMap labels).length+nodeIndex (ts i) v

lemma nodeIndex_bound (t : CoreTree) (v : t.Node) : t.nodeIndex v<t.labels.length := by
  induction t with
  | leaf => simp [nodeIndex,labels]
  | branch c ts ih =>
    cases v with
    | inl u => exact List.length_pos_iff.mpr (labels_nonempty _)
    | inr v =>
      obtain ⟨i,v⟩ := v
      rw [labels_split c ts i]
      simp only [nodeIndex,List.length_cons,List.length_append]
      have := ih i v
      omega

lemma labels_take_child (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length)
    {v : ℕ} (hv : v≤(ts i).labels.length) :
    (branch c ts).labels.take (1+((before c ts i).flatMap labels).length+v)=
      some c::((before c ts i).flatMap labels++(ts i).labels.take v) := by
  rw [labels_split c ts i]
  rw [show 1+((before c ts i).flatMap labels).length+v=
    (((before c ts i).flatMap labels).length+v)+1 by omega,List.take_succ_cons]
  rw [List.append_assoc,List.take_append]
  congr 1
  rw [List.take_of_length_le (by omega),Nat.add_sub_cancel_left,List.take_append_of_le_length hv]

lemma forest_labels_degrees (fs : List CoreTree) :
    (fs.flatMap labels).map CoreLabel.arity=PlaneTree.forestDegrees (fs.map shape) := by
  simp only [PlaneTree.forestDegrees,List.flatMap_map,List.map_flatMap]
  congr 1
  funext t
  exact t.shape_degrees.symm

lemma forest_labels_properties (fs : List CoreTree) :
    (PlaneTree.incrementWord ((fs.flatMap labels).map CoreLabel.arity)).sum= -(fs.length:ℤ) ∧
    PlaneTree.SuffixNegative ((fs.flatMap labels).map CoreLabel.arity) := by
  rw [forest_labels_degrees]
  simpa only [List.length_map] using PlaneTree.forest_properties (fs.map shape)

lemma labels_take_nonneg (t : CoreTree) {v : ℕ} (hv : v<t.labels.length) :
    ∀ j≤(t.labels.take v).length,
      0≤prefixSum (PlaneTree.incrementWord ((t.labels.take v).map CoreLabel.arity)) j := by
  intro j hj
  have hjv : j≤v := hj.trans (List.length_take_le _ _)
  have h := t.degrees_excursion.2 j (by simpa [PlaneTree.incrementWord,degrees] using hjv.trans_lt hv)
  simpa only [PlaneTree.incrementWord,degrees,List.map_take,prefixSum,List.take_take,Nat.min_eq_left hjv] using h

def nodeSpine (b : (ℕ×ℕ) → CoreLabel → ℝ) : (t : CoreTree) → t.Node → ℝ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩ => b (c.val.length,c.val.length-1-i.val) (some c)+nodeSpine b (ts i) v

lemma nodeSpine_profile (b : (ℕ×ℕ) → CoreLabel → ℝ) (t : CoreTree) (v : t.Node) :
    labelProfileSum b (t.labels.take (t.nodeIndex v))=t.nodeSpine b v := by
  induction t with
  | leaf => exact labelProfileSum_empty b
  | branch c ts ih =>
    cases v with
    | inl u => exact labelProfileSum_empty b
    | inr v =>
      obtain ⟨i,v⟩ := v
      change labelProfileSum b ((branch c ts).labels.take (1+((before c ts i).flatMap labels).length+(ts i).nodeIndex v))=_
      rw [labels_take_child c ts i (nodeIndex_bound _ _).le]
      have hp := forest_labels_properties (before c ts i)
      rw [before_length] at hp
      rw [labelProfileSum_attach b ((ts i).labels.take ((ts i).nodeIndex v)) ((before c ts i).flatMap labels) (some c) (labels_take_nonneg _ (nodeIndex_bound _ _)) hp.2 hp.1 i.isLt,ih i v]
      exact add_comm _ _

lemma nodeSpine_marked (b : (ℕ×ℕ) → CoreLabel → ℝ) (t : CoreTree) (v : t.Node) :
    t.nodeSpine b v=markedSpineSum b t.toCode (t.nodeIndex_bound v).le (fun i => t.labels[i.val]) := by
  rw [toCode_labelProfile,nodeSpine_profile]

lemma coreIncrement_slot (c : Core) (i : Fin c.val.length) :
    coreIncrement (c.val.length,c.val.length-1-i.val) (some c)=(c.increment i:ℝ) := by
  dsimp only [coreIncrement]
  rw [dite_eq_left (by constructor;rfl;omega)]
  congr 2
  apply Fin.ext
  dsimp
  omega

lemma nodeSpine_metric (t : CoreTree) (v : t.Node) :
    t.nodeSpine coreIncrement v=(t.routeLength v:ℝ) := by
  induction t with
  | leaf => simp [nodeSpine,routeLength]
  | branch c ts ih =>
    cases v with
    | inl u => simp [nodeSpine,routeLength]
    | inr v =>
      obtain ⟨i,v⟩ := v
      simp only [nodeSpine,coreIncrement_slot,routeLength,Nat.cast_add,ih]

/-- The actual original-map pole distance is the same marked ancestor sum
appearing in the conditioned-code uniform LLN, not a separately sampled tree. -/
theorem routeLength_marked (t : CoreTree) (v : t.Node) :
    (t.routeLength v:ℝ)=markedSpineSum coreIncrement t.toCode (t.nodeIndex_bound v).le
      (fun i => t.labels[i.val]) := by
  rw [← nodeSpine_metric,nodeSpine_marked]

def depth : (t : CoreTree) → t.Node → ℕ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch _ ts,.inr ⟨i,v⟩ => 1+depth (ts i) v

lemma nodeSpine_one (t : CoreTree) (v : t.Node) : t.nodeSpine (fun _ _ => 1) v=(t.depth v:ℝ) := by
  induction t with
  | leaf => simp [nodeSpine,depth]
  | branch c ts ih =>
    cases v with
    | inl u => simp [nodeSpine,depth]
    | inr v =>
      obtain ⟨i,v⟩ := v
      simp only [nodeSpine,depth,Nat.cast_add,Nat.cast_one,ih]

lemma depth_height (t : CoreTree) (v : t.Node) :
    t.depth v=height t.toCode.val (t.nodeIndex v) := by
  have h := nodeSpine_marked (fun _ _ => 1) t v
  rw [nodeSpine_one,markedSpineSum_deterministic,codeSpineSum_one t.toCode (nodeIndex_bound _ _).le] at h
  exact_mod_cast h

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
attribute [local instance] Classical.propDecidable

lemma offset_separation (c : Core) (ts : Fin c.val.length → CoreTree) (i j : Fin c.val.length)
    (hij : i<j) :
    ((before c ts i).flatMap labels).length+(ts i).labels.length≤((before c ts j).flatMap labels).length := by
  have h := (List.take_prefix_take_left (l := List.ofFn ts) (show i.val+1≤j.val by exact hij)).flatMap labels
  have he : (List.ofFn ts).take (i.val+1)=before c ts i++[ts i] := by
    rw [List.take_succ_eq_append_getElem (by simp)]
    simp only [before,List.getElem_ofFn]
  rw [he,List.flatMap_append,List.flatMap_singleton] at h
  simpa only [List.length_append,before] using h.length_le

lemma children_index_strict (c : Core) (ts : Fin c.val.length → CoreTree) (i j : Fin c.val.length)
    (hij : i<j) (v : (ts i).Node) (w : (ts j).Node) :
    (branch c ts).nodeIndex (.inr ⟨i,v⟩)<(branch c ts).nodeIndex (.inr ⟨j,w⟩) := by
  have hs := offset_separation c ts i j hij
  have hv := nodeIndex_bound (ts i) v
  simp only [nodeIndex]
  omega

lemma children_order (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (v : (ts i).Node) (w : (ts j).Node)
    (h : (branch c ts).nodeIndex (.inr ⟨i,v⟩)≤(branch c ts).nodeIndex (.inr ⟨j,w⟩)) : i≤j := by
  by_contra hn
  have hh := children_index_strict c ts j i (lt_of_not_ge hn) w v
  omega

lemma nodeIndex_root (t : CoreTree) : t.nodeIndex t.root=0 := by cases t <;> rfl
lemma routeLength_root (t : CoreTree) : t.routeLength t.root=0 := by cases t <;> rfl

lemma same_child_between (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length)
    (v w : (ts i).Node) (u : (branch c ts).Node)
    (h₁ : (branch c ts).nodeIndex (.inr ⟨i,v⟩)≤(branch c ts).nodeIndex u)
    (h₂ : (branch c ts).nodeIndex u≤(branch c ts).nodeIndex (.inr ⟨i,w⟩)) :
    ∃ z : (ts i).Node,u=.inr ⟨i,z⟩ ∧ (ts i).nodeIndex v≤(ts i).nodeIndex z ∧
      (ts i).nodeIndex z≤(ts i).nodeIndex w := by
  cases u with
  | inl a => simp only [nodeIndex] at h₁;omega
  | inr u =>
    obtain ⟨j,z⟩ := u
    have hi := children_order c ts i j v z h₁
    have hj := children_order c ts j i z w h₂
    obtain rfl := le_antisymm hi hj
    exact ⟨z,rfl,by simpa only [nodeIndex,Nat.add_le_add_iff_left] using h₁,
      by simpa only [nodeIndex,Nat.add_le_add_iff_left] using h₂⟩

/-- Every intervening preorder vertex remains below the last common ancestor. -/
lemma commonRoute_le_intervening (t : CoreTree) (v w u : t.Node)
    (h₁ : t.nodeIndex v≤t.nodeIndex u) (h₂ : t.nodeIndex u≤t.nodeIndex w) :
    t.commonRoute v w≤t.routeLength u := by
  induction t with
  | leaf => simp [commonRoute,routeLength]
  | branch c ts ih =>
    cases v with
    | inl a => exact Nat.zero_le _
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl a => exact Nat.zero_le _
      | inr w =>
        obtain ⟨j,w⟩ := w
        by_cases hij : i=j
        · subst j
          obtain ⟨z,rfl,hz₁,hz₂⟩ := same_child_between c ts i v w u h₁ h₂
          simpa only [commonRoute,dite_true,routeLength,Nat.add_le_add_iff_left] using ih i v w z hz₁ hz₂
        · simp only [commonRoute,dite_eq_right hij]
          exact Nat.zero_le _

/-- One intervening vertex is either the ancestor itself or the first node
of its selected right-hand child, costing at most one maximum core degree. -/
lemma exists_intervening_low (t : CoreTree) (v w : t.Node) (h : t.nodeIndex v≤t.nodeIndex w) :
    ∃ u : t.Node,t.nodeIndex v≤t.nodeIndex u ∧ t.nodeIndex u≤t.nodeIndex w ∧
      t.routeLength u≤t.commonRoute v w+t.maxDegree := by
  induction t with
  | leaf => exact ⟨v,le_rfl,h,by simp [routeLength,commonRoute]⟩
  | branch c ts ih =>
    cases v with
    | inl a => exact ⟨.inl a,le_rfl,h,by simp [routeLength,commonRoute]⟩
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl a =>
        simp only [nodeIndex] at h
        omega
      | inr w =>
        obtain ⟨j,w⟩ := w
        by_cases hij : i=j
        · subst j
          have hvw : (ts i).nodeIndex v≤(ts i).nodeIndex w := by simpa only [nodeIndex,Nat.add_le_add_iff_left] using h
          obtain ⟨u,hu₁,hu₂,hu⟩ := ih i v w hvw
          refine ⟨.inr ⟨i,u⟩,by simpa only [nodeIndex,Nat.add_le_add_iff_left] using hu₁,
            by simpa only [nodeIndex,Nat.add_le_add_iff_left] using hu₂,?_⟩
          have hm := maxDegree_child c ts i
          simp only [routeLength,commonRoute,dite_true]
          omega
        · have hij' : i<j := lt_of_le_of_ne (children_order c ts i j v w h) hij
          refine ⟨.inr ⟨j,(ts j).root⟩,(children_index_strict c ts i j hij' v (ts j).root).le,?_,?_⟩
          · simp only [nodeIndex,nodeIndex_root]
            omega
          · simp only [routeLength,routeLength_root,Nat.add_zero,commonRoute,dite_eq_right hij,Nat.zero_add]
            exact (c.increment_le j).trans (maxDegree_core c ts)

lemma flatMap_find_index {A B : Type*} (f : A → List B) (fs : List A) {r : ℕ}
    (hr : r<(fs.flatMap f).length) :
    ∃ i : Fin fs.length,∃ j,j<(f fs[i.val]).length ∧ r=((fs.take i.val).flatMap f).length+j := by
  induction fs generalizing r with
  | nil => simp at hr
  | cons a fs ih =>
    by_cases ha : r<(f a).length
    · exact ⟨⟨0,by simp⟩,r,ha,by simp⟩
    · obtain ⟨i,j,hj,he⟩ := ih (r := r-(f a).length) (by simp only [List.flatMap_cons,List.length_append] at hr;omega)
      refine ⟨i.succ,j,hj,?_⟩
      simp only [Fin.val_succ,List.take_succ_cons,List.flatMap_cons,List.length_append]
      omega

/-- The literal recursive node index covers every and only preorder cell. -/
lemma nodeIndex_surjective (t : CoreTree) {r : ℕ} (hr : r<t.labels.length) :
    ∃ v : t.Node,t.nodeIndex v=r := by
  induction t generalizing r with
  | leaf => exact ⟨leaf.root,by simp only [labels,List.length_singleton] at hr;simpa [nodeIndex_root] using (show 0=r by omega)⟩
  | branch c ts ih =>
    by_cases hr0 : r=0
    · exact ⟨.inl PUnit.unit,hr0.symm⟩
    · have hf : r-1<((List.ofFn ts).flatMap labels).length := by rw [labels_branch] at hr;simp only [List.length_cons] at hr;omega
      obtain ⟨i,j,hj,he⟩ := flatMap_find_index labels (List.ofFn ts) hf
      let k : Fin c.val.length := ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩
      have hk : (List.ofFn ts)[i.val]=ts k := by simp [k]
      rw [hk] at hj
      obtain ⟨v,hv⟩ := ih k hj
      refine ⟨.inr ⟨k,v⟩,?_⟩
      dsimp only [nodeIndex,before,k]
      rw [hv]
      omega

/-- A walk minimum can be used without assuming a probabilistic law at a
random ancestor. This is the deterministic all-poles comparison after the
uniform same-code ancestral estimate. -/
theorem pole_walk_comparison (t : CoreTree) (v w m : t.Node) (a b : t.Dart)
    (ha : t.pole v=some a) (hb : t.pole w=some b)
    (hm₁ : t.nodeIndex v≤t.nodeIndex m) (hm₂ : t.nodeIndex m≤t.nodeIndex w)
    (W : t.Node → ℝ) {α ε : ℝ} (hα : 0≤α)
    (herr : ∀ u,|(t.routeLength u:ℝ)-α*W u|≤ε)
    (hmin : ∀ u,t.nodeIndex v≤t.nodeIndex u → t.nodeIndex u≤t.nodeIndex w → W m≤W u) :
    |t.realDistance a b-α*(W v+W w-2*W m)|≤4*(t.maxDegree:ℝ)+4*ε := by
  have hp := abs_le.mp (t.pole_comparison v w a b ha hb)
  have hlow : (t.commonRoute v w:ℝ)≤t.routeLength m := Nat.cast_le.mpr (commonRoute_le_intervening t v w m hm₁ hm₂)
  obtain ⟨u,hu₁,hu₂,hu⟩ := exists_intervening_low t v w (hm₁.trans hm₂)
  have hhi : (t.routeLength u:ℝ)≤(t.commonRoute v w:ℝ)+t.maxDegree := by exact_mod_cast hu
  have hv := abs_le.mp (herr v)
  have hw := abs_le.mp (herr w)
  have hM := abs_le.mp (herr m)
  have hU := abs_le.mp (herr u)
  have hmul := mul_le_mul_of_nonneg_left (hmin u hu₁ hu₂) hα
  apply abs_le.mpr
  constructor <;> linarith

end FKCRT.Inventory.CoreTree
end

end OAI
