import OAI.Probability.FKMaps.CoreMetric

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Actual ordered-tree nodes, with a distinct trivial leaf at every empty
corner word. Coincident map poles are not identified as tree nodes. -/
def Node : CoreTree → Type
  | .leaf => PUnit
  | .branch c ts => PUnit ⊕ (Σ i : Fin c.val.length,Node (ts i))

instance (t : CoreTree) : Fintype t.Node := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype PUnit)
  | branch c ts ih =>
    letI := ih
    exact inferInstanceAs (Fintype (PUnit ⊕ (Σ i, (ts i).Node)))

instance (t : CoreTree) : DecidableEq t.Node := Classical.decEq _

def root : (t : CoreTree) → t.Node
  | .leaf => PUnit.unit
  | .branch _ _ => .inl PUnit.unit

def rootDart : (t : CoreTree) → Option t.Dart
  | .leaf => none
  | .branch c ts => some (coreDart ts c.entry)

def pole : (t : CoreTree) → t.Node → Option t.Dart
  | .leaf,_ => none
  | .branch c ts,.inl _ => some (coreDart ts c.entry)
  | .branch c ts,.inr ⟨i,v⟩ =>
    some (((pole (ts i) v).map (childDart ts i)).getD (coreDart ts (nextSlot c i)))

lemma pole_some (c : Core) (ts : Fin c.val.length → CoreTree) (v : (branch c ts).Node) :
    ∃ d,(branch c ts).pole v=some d := by
  cases v <;> exact ⟨_,rfl⟩

def routeLength : (t : CoreTree) → t.Node → ℕ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩ => c.increment i+routeLength (ts i) v

lemma darts_head (c : Core) (ts : Fin c.val.length → CoreTree) :
    ∃ L,(branch c ts).darts=coreDart ts c.entry::L := by
  have h := List.drop_eq_getElem_cons (l := List.finRange c.val.length) (i := 0)
    (by simpa using coreWord_pos c.val c.property)
  have he : (List.finRange c.val.length)[0]'(by simpa using coreWord_pos c.val c.property)=c.entry := by
    apply Fin.ext
    simp [Core.entry]
  rw [List.drop_zero,he] at h
  rw [darts,h,List.flatMap_cons]
  exact ⟨_,rfl⟩

lemma pole_none_of_leaf (t : CoreTree) (h : t=leaf) (v : t.Node) : t.pole v=none := by
  subst t
  rfl

lemma route_zero_of_leaf (t : CoreTree) (h : t=leaf) (v : t.Node) : t.routeLength v=0 := by
  subst t
  rfl

lemma pole_some_of_ne_leaf (t : CoreTree) (h : t≠leaf) (v : t.Node) : ∃ d,t.pole v=some d := by
  cases t with
  | leaf => exact False.elim (h rfl)
  | branch c ts => exact pole_some c ts v

/-- The route length sums the genuine isolated-core graph distances along
the strict ancestor chain. It equals the original full-map graph distance
from the root pole, rather than a postulated replacement metric. -/
theorem distance_root_pole (t : CoreTree) (v : t.Node) (a b : t.Dart)
    (ha : t.rootDart=some a) (hb : t.pole v=some b) :
    t.matching.distance a b=(t.routeLength v : ℕ∞) := by
  induction t with
  | leaf => cases a
  | branch c ts ih =>
    have ha' : coreDart ts c.entry=a := Option.some.inj ha
    subst a
    cases v with
    | inl u =>
      have hb' : coreDart ts c.entry=b := Option.some.inj hb
      subst b
      exact SimpleGraph.edist_self
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases ht : ts i with
      | leaf =>
        have hn := pole_none_of_leaf (ts i) ht v
        have hr := route_zero_of_leaf (ts i) ht v
        have hb' : coreDart ts (nextSlot c i)=b := by simpa only [pole,hn,Option.map_none,Option.getD_none,Option.some.injEq] using hb
        subst b
        rw [core_distance,Core.distance_eq_nat]
        change (c.increment i:ℕ∞)=((c.increment i+(ts i).routeLength v:ℕ):ℕ∞)
        rw [hr,Nat.add_zero]
      | branch d us =>
        have hs := pole_some_of_ne_leaf (ts i) (by rw [ht];exact CoreTree.noConfusion) v
        obtain ⟨b',hb'⟩ := hs
        have hsroot : ∃ a' L,(ts i).rootDart=some a' ∧ (ts i).darts=a'::L := by
          rw [ht]
          obtain ⟨L,hL⟩ := darts_head d us
          exact ⟨_,L,rfl,hL⟩
        obtain ⟨a',L,ha',hL⟩ := hsroot
        have hbb : childDart ts i b'=b := by
          simpa only [pole,hb',Option.map_some,Option.getD_some,Option.some.injEq] using hb
        subst b
        rw [child_distance_sum c ts i c.entry a' b' L hL,ih i v a' b' ha' hb',Core.distance_eq_nat]
        change (c.increment i:ℕ∞)+((ts i).routeLength v:ℕ∞)=
          ((c.increment i+(ts i).routeLength v:ℕ):ℕ∞)
        exact_mod_cast (rfl : c.increment i+(ts i).routeLength v=c.increment i+(ts i).routeLength v)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma child_interval (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (a : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) :
    ∃ u z R,(branch c ts).darts=u++((childDart ts i a::L.map (childDart ts i))++z) ∧
      z++u=coreDart ts (nextSlot c i)::R := by
  let v := (ts i).darts.map (childDart ts i)
  have hm : (coreDart ts i,v)∈dartCorners c ts := List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
  obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hm
  have hv : v=childDart ts i a::L.map (childDart ts i) := by simp only [v,hhead,List.map_cons]
  obtain ⟨R,hR⟩ := corner_complement_head A B (coreDart ts i) v
    (by rw [← hAB,← darts_branch];exact (branch c ts).darts_nodup)
  rw [← hAB,core_next] at hR
  refine ⟨dartInsert A++[coreDart ts i],dartInsert B,R,?_,hR⟩
  rw [darts_branch,hAB]
  simp only [dartInsert,List.flatMap_append,List.flatMap_cons,List.cons_append,hv,List.append_assoc,
    List.nil_append]

/-- Isometry of every nonempty inserted child, in its original all-edge
metric. No root-distance-only surrogate is used. -/
theorem child_internal_distance (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (a x y : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) :
    (branch c ts).matching.distance (childDart ts i x) (childDart ts i y)=
      (ts i).matching.distance x y := by
  obtain ⟨u,z,R,hw,hR⟩ := child_interval c ts i a L hhead
  let M : StackMatching (branch c ts).dartLabel (u++((childDart ts i a::L.map (childDart ts i))++z)) :=
    hw ▸ (branch c ts).matching
  have hn := hw ▸ (branch c ts).darts_nodup
  have hv : (ts i).darts.map (childDart ts i)=childDart ts i a::L.map (childDart ts i) := by
    rw [hhead,List.map_cons]
  have he : stackTypedRun ((childDart ts i a::L.map (childDart ts i)).map (branch c ts).dartLabel) []=some [] := by
    rw [← hv,List.map_map]
    change stackTypedRun ((ts i).darts.map (ts i).dartLabel) []=some []
    rw [darts_word];exact (ts i).word_empty
  let Q₀ := (ts i).matching.map (childDart ts i) (branch c ts).dartLabel (fun _ _ => rfl)
  let Q : StackMatching (branch c ts).dartLabel
      (childDart ts i a::L.map (childDart ts i)) := hv ▸ Q₀
  have hm (d : (ts i).Dart) : childDart ts i d∈childDart ts i a::L.map (childDart ts i) := by
    rw [← hv];exact List.mem_map.mpr ⟨d,(ts i).darts_mem d,rfl⟩
  have hg := M.keep_interval_distance u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR (childDart ts i x) (childDart ts i y) (hm x) (hm y)
  have hu := (M.keepInterval hn he).unique_distance Q hn.of_append_right.of_append_left
    (childDart ts i x) (childDart ts i y)
  rw [((branch c ts).matching.distance_cast hw _ _)] at hg
  rw [hu,Q₀.distance_cast hv _ _] at hg
  exact hg.trans ((ts i).matching.map_distance_of_full (ts i).darts_nodup (ts i).darts_mem
      (childDart ts i) (childDart_injective ts i) (branch c ts).dartLabel (fun _ _ => rfl) x y)

lemma child_gate_distance (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (a x : (ts i).Dart) (L : List (ts i).Dart)
    (hhead : (ts i).darts=a::L) (y : (branch c ts).Dart)
    (hy : ∀ d : (ts i).Dart,childDart ts i d≠y) :
    (branch c ts).matching.distance (childDart ts i x) y=
      (ts i).matching.distance x a+
        (branch c ts).matching.distance (coreDart ts (nextSlot c i)) y := by
  obtain ⟨u,z,R,hw,hR⟩ := child_interval c ts i a L hhead
  let M : StackMatching (branch c ts).dartLabel (u++((childDart ts i a::L.map (childDart ts i))++z)) :=
    hw ▸ (branch c ts).matching
  have hn := hw ▸ (branch c ts).darts_nodup
  have hv : (ts i).darts.map (childDart ts i)=childDart ts i a::L.map (childDart ts i) := by
    rw [hhead,List.map_cons]
  have he : stackTypedRun ((childDart ts i a::L.map (childDart ts i)).map (branch c ts).dartLabel) []=some [] := by
    rw [← hv,List.map_map]
    change stackTypedRun ((ts i).darts.map (ts i).dartLabel) []=some []
    rw [darts_word];exact (ts i).word_empty
  have hx : childDart ts i x∈childDart ts i a::L.map (childDart ts i) := by
    rw [← hv];exact List.mem_map.mpr ⟨x,(ts i).darts_mem x,rfl⟩
  have hyn : y∉childDart ts i a::L.map (childDart ts i) := by
    rw [← hv];rintro h
    obtain ⟨d,_,hd⟩ := List.mem_map.mp h
    exact hy d hd
  have hg := M.empty_interval_gate u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR (childDart ts i x) y hx hyn
  have hp := M.empty_interval_pole u (L.map (childDart ts i)) z (childDart ts i a)
    (coreDart ts (nextSlot c i)) R hn he hR
  change M.distance (childDart ts i x) y=M.distance (childDart ts i x) (childDart ts i a)+
    M.distance (childDart ts i a) y at hg
  have hp' : M.distance (childDart ts i a) y=M.distance (coreDart ts (nextSlot c i)) y := by
    dsimp only [StackMatching.distance]
    rw [hp]
  rw [hp'] at hg
  have hh (r s : (branch c ts).Dart) : M.distance r s=(branch c ts).matching.distance r s :=
    (branch c ts).matching.distance_cast hw r s
  rw [hh,hh,hh,child_internal_distance c ts i a x a L hhead] at hg
  exact hg

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def childPole (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) (v : (ts i).Node) :
    (branch c ts).Dart :=
  (((ts i).pole v).map (childDart ts i)).getD (coreDart ts (nextSlot c i))

lemma root_and_head (t : CoreTree) (h : t≠leaf) :
    ∃ a L,t.rootDart=some a ∧ t.darts=a::L := by
  cases t with
  | leaf => exact False.elim (h rfl)
  | branch c ts =>
    obtain ⟨L,hL⟩ := darts_head c ts
    exact ⟨_,L,rfl,hL⟩

lemma core_to_childPole (c : Core) (ts : Fin c.val.length → CoreTree)
    (i r : Fin c.val.length) (v : (ts i).Node) :
    (branch c ts).matching.distance (coreDart ts r) (childPole c ts i v)=
      c.matching.distance r (nextSlot c i)+((ts i).routeLength v:ℕ∞) := by
  by_cases ht : ts i=leaf
  · have hp := pole_none_of_leaf (ts i) ht v
    have hr := route_zero_of_leaf (ts i) ht v
    simp only [childPole,hp,Option.map_none,Option.getD_none,hr,Nat.cast_zero,add_zero]
    exact core_distance c ts r (nextSlot c i)
  · obtain ⟨b,hb⟩ := pole_some_of_ne_leaf (ts i) ht v
    obtain ⟨a,L,ha,hL⟩ := root_and_head (ts i) ht
    simp only [childPole,hb,Option.map_some,Option.getD_some]
    rw [child_distance_sum c ts i r a b L hL,distance_root_pole (ts i) v a b ha hb]

lemma childPole_not_child (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (hij : i≠j) (v : (ts j).Node) (d : (ts i).Dart) :
    childDart ts i d≠childPole c ts j v := by
  unfold childPole
  cases hp : (ts j).pole v with
  | none => simp only [Option.map_none,Option.getD_none];intro h;cases h
  | some b =>
    simp only [Option.map_some,Option.getD_some]
    intro h
    exact hij (congrArg Sigma.fst (Sum.inr.inj h))

/-- The exact three-piece route between distinct child components. -/
theorem between_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (hij : i≠j) (v : (ts i).Node) (w : (ts j).Node) :
    (branch c ts).matching.distance (childPole c ts i v) (childPole c ts j w)=
      ((ts i).routeLength v:ℕ∞)+c.matching.distance (nextSlot c i) (nextSlot c j)+
        ((ts j).routeLength w:ℕ∞) := by
  by_cases ht : ts i=leaf
  · have hp := pole_none_of_leaf (ts i) ht v
    have hr := route_zero_of_leaf (ts i) ht v
    simp only [childPole,hp,Option.map_none,Option.getD_none,hr,Nat.cast_zero,zero_add]
    exact core_to_childPole c ts j (nextSlot c i) w
  · obtain ⟨b,hb⟩ := pole_some_of_ne_leaf (ts i) ht v
    obtain ⟨a,L,ha,hL⟩ := root_and_head (ts i) ht
    have he : childPole c ts i v=childDart ts i b := by simp only [childPole,hb,Option.map_some,Option.getD_some]
    rw [he,child_gate_distance c ts i a b L hL _ (childPole_not_child c ts i j hij w)]
    rw [(ts i).matching.distance_comm b a,distance_root_pole (ts i) v a b ha hb,
      core_to_childPole c ts j (nextSlot c i) w,add_assoc]

lemma within_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (v w : (ts i).Node) (a b : (ts i).Dart)
    (ha : (ts i).pole v=some a) (hb : (ts i).pole w=some b) :
    (branch c ts).matching.distance (childPole c ts i v) (childPole c ts i w)=
      (ts i).matching.distance a b := by
  have hn : ts i≠leaf := by intro h;rw [pole_none_of_leaf (ts i) h v] at ha;cases ha
  obtain ⟨r,L,_,hL⟩ := root_and_head (ts i) hn
  simp only [childPole,ha,hb,Option.map_some,Option.getD_some]
  exact child_internal_distance c ts i r a b L hL

/-- Real graph distance, on the same literal original map. -/
def realDistance (t : CoreTree) (a b : t.Dart) : ℝ :=
  let s := t.darts.formPerm*turns t.matching.first
  (dartGraph t.matching.mate s).dist (vertex s a) (vertex s b)

lemma distance_eq_nat (t : CoreTree) (a b : t.Dart) :
    t.matching.distance a b=
      ((dartGraph t.matching.mate (t.darts.formPerm*turns t.matching.first)).dist
        (vertex _ a) (vertex _ b):ℕ∞) := by
  have hn : t.darts≠[] := List.ne_nil_of_mem (t.darts_mem a)
  have hc := t.matching.connected t.darts_nodup t.darts_mem hn
  exact (SimpleGraph.Reachable.coe_dist_eq_edist (hc.preconnected _ _)).symm

lemma realDistance_nonneg (t : CoreTree) (a b : t.Dart) : 0≤t.realDistance a b := Nat.cast_nonneg _

lemma realDistance_comm (t : CoreTree) (a b : t.Dart) : t.realDistance a b=t.realDistance b a := by
  dsimp [realDistance]
  rw [SimpleGraph.dist_comm]

lemma realDistance_self (t : CoreTree) (a : t.Dart) : t.realDistance a a=0 := by
  simp [realDistance]

lemma real_root_distance (t : CoreTree) (v : t.Node) (a b : t.Dart)
    (ha : t.rootDart=some a) (hb : t.pole v=some b) :
    t.realDistance a b=t.routeLength v := by
  have h := distance_root_pole t v a b ha hb
  rw [distance_eq_nat] at h
  dsimp only [realDistance]
  exact_mod_cast h

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

namespace Core

def realDistance (c : Core) (i j : Fin c.val.length) : ℝ :=
  c.graph.dist (vertex c.rotation i) (vertex c.rotation j)

lemma realDistance_nonneg (c : Core) (i j : Fin c.val.length) : 0≤c.realDistance i j := Nat.cast_nonneg _

lemma corner_distance_le (c : Core) (i j : Fin c.val.length) :
    c.realDistance (CoreTree.nextSlot c i) (CoreTree.nextSlot c j)≤(c.increment i:ℝ)+c.increment j := by
  have h := c.graph_connected.dist_triangle (u := vertex c.rotation (CoreTree.nextSlot c i))
    (v := vertex c.rotation c.entry) (w := vertex c.rotation (CoreTree.nextSlot c j))
  rw [SimpleGraph.dist_comm (u := vertex c.rotation (CoreTree.nextSlot c i)) (v := vertex c.rotation c.entry)] at h
  dsimp only [realDistance,increment,CoreTree.nextSlot]
  exact_mod_cast h

end Core
namespace CoreTree

def commonRoute : (t : CoreTree) → t.Node → t.Node → ℕ
  | .leaf,_,_ => 0
  | .branch _ _,.inl _,_ => 0
  | .branch _ _,.inr _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩,.inr ⟨j,w⟩ =>
    if h : i=j then c.increment i+commonRoute (ts i) v (h.symm ▸ w) else 0

def maxDegree : CoreTree → ℕ
  | .leaf => 0
  | .branch c ts => max c.val.length (Finset.univ.sup (fun i => maxDegree (ts i)))

lemma maxDegree_core (c : Core) (ts : Fin c.val.length → CoreTree) :
    c.val.length≤(branch c ts).maxDegree := le_max_left _ _

lemma maxDegree_child (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (ts i).maxDegree≤(branch c ts).maxDegree :=
  (Finset.le_sup (f := fun i => (ts i).maxDegree) (Finset.mem_univ i)).trans (le_max_right _ _)

lemma real_between_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (hij : i≠j) (v : (ts i).Node) (w : (ts j).Node) :
    (branch c ts).realDistance (childPole c ts i v) (childPole c ts j w)=
      ((ts i).routeLength v:ℝ)+c.realDistance (nextSlot c i) (nextSlot c j)+
        ((ts j).routeLength w:ℝ) := by
  have h := between_childPoles c ts i j hij v w
  rw [distance_eq_nat,Core.distance_eq_nat] at h
  dsimp only [realDistance,Core.realDistance]
  exact_mod_cast h

lemma real_within_childPoles (c : Core) (ts : Fin c.val.length → CoreTree)
    (i : Fin c.val.length) (v w : (ts i).Node) (a b : (ts i).Dart)
    (ha : (ts i).pole v=some a) (hb : (ts i).pole w=some b) :
    (branch c ts).realDistance (childPole c ts i v) (childPole c ts i w)=
      (ts i).realDistance a b := by
  have h := within_childPoles c ts i v w a b ha hb
  rw [distance_eq_nat,distance_eq_nat] at h
  dsimp only [realDistance]
  exact_mod_cast h

lemma commonRoute_leaf (t : CoreTree) (h : t=leaf) (v w : t.Node) : t.commonRoute v w=0 := by
  subst t;rfl

/-- Exact source two-pole comparison: the only error lies inside the last
common ancestor's actual isolated core. All distances use all original edges. -/
theorem pole_comparison (t : CoreTree) (v w : t.Node) (a b : t.Dart)
    (ha : t.pole v=some a) (hb : t.pole w=some b) :
    |t.realDistance a b-((t.routeLength v:ℝ)+t.routeLength w-2*t.commonRoute v w)|≤2*t.maxDegree := by
  induction t with
  | leaf => cases a
  | branch c ts ih =>
    cases v with
    | inl u =>
      have hroot : coreDart ts c.entry=a := Option.some.inj ha
      subst a
      rw [real_root_distance (branch c ts) w _ b rfl hb]
      simp only [routeLength,commonRoute,Nat.cast_zero,zero_add,mul_zero,sub_zero,sub_self,abs_zero]
      positivity
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl u =>
        have hroot : coreDart ts c.entry=b := Option.some.inj hb
        subst b
        rw [realDistance_comm,real_root_distance (branch c ts) (.inr ⟨i,v⟩) _ a rfl ha]
        simp only [routeLength,commonRoute,Nat.cast_zero,add_zero,mul_zero,sub_zero,sub_self,abs_zero]
        positivity
      | inr w =>
        obtain ⟨j,w⟩ := w
        have ha' : childPole c ts i v=a := Option.some.inj ha
        have hb' : childPole c ts j w=b := Option.some.inj hb
        subst a;subst b
        by_cases hij : i=j
        · subst j
          by_cases ht : ts i=leaf
          · have hpv := pole_none_of_leaf (ts i) ht v
            have hpw := pole_none_of_leaf (ts i) ht w
            have hrv := route_zero_of_leaf (ts i) ht v
            have hrw := route_zero_of_leaf (ts i) ht w
            have hcr := commonRoute_leaf (ts i) ht v w
            simp only [childPole,hpv,hpw,Option.map_none,Option.getD_none,realDistance_self,
              routeLength,commonRoute,dite_true,hrv,hrw,hcr,Nat.add_zero]
            norm_num [two_mul]
          · obtain ⟨a,ha⟩ := pole_some_of_ne_leaf (ts i) ht v
            obtain ⟨b,hb⟩ := pole_some_of_ne_leaf (ts i) ht w
            rw [real_within_childPoles c ts i v w a b ha hb]
            have hh := ih i v w a b ha hb
            have hm : ((ts i).maxDegree:ℝ)≤(branch c ts).maxDegree := Nat.cast_le.mpr (maxDegree_child c ts i)
            simp only [routeLength,commonRoute,dite_true,Nat.cast_add]
            convert hh.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2)) using 1
            first | rfl | ring_nf
        · rw [real_between_childPoles c ts i j hij v w]
          have hnonneg := c.realDistance_nonneg (nextSlot c i) (nextSlot c j)
          have hupper := c.corner_distance_le i j
          have hbi : (c.increment i:ℝ)≤c.val.length := Nat.cast_le.mpr (c.increment_le i)
          have hbj : (c.increment j:ℝ)≤c.val.length := Nat.cast_le.mpr (c.increment_le j)
          have hm : (c.val.length:ℝ)≤(branch c ts).maxDegree := Nat.cast_le.mpr (maxDegree_core c ts)
          simp only [routeLength,commonRoute,dite_eq_right hij,Nat.cast_add,Nat.cast_zero,mul_zero,sub_zero]
          apply abs_le.mpr
          constructor <;> linarith

end CoreTree
end FKCRT.Inventory
end

end OAI
