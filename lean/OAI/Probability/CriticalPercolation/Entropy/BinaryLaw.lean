import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SequentialExposure
import OAI.Probability.CriticalPercolation.Entropy.BinaryInterpolation
import OAI.Probability.CriticalPercolation.Exploration.ReachableIncidenceImp

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

universe uE

def History (E : Type uE) : ℕ → Type uE
  | 0 => PUnit
  | n+1 => History E n × Bool × Option E

instance historyFintype {E : Type*} [Fintype E] : (n : ℕ) → Fintype (History E n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := historyFintype (E := E) n
    exact inferInstanceAs (Fintype (History E n × Bool × Option E))

def interval {E : Type*} (d : ℕ) : (n : ℕ) → History E n → ℕ × ℕ
  | 0, _ => (0,d)
  | n+1, h => bisect (interval d n h.1).1 (interval d n h.1).2 h.2.1

lemma interval_bounds {E : Type*} {d : ℕ} (hd : 0<d) (n : ℕ) (h : History E n) :
    (interval d n h).1 < (interval d n h).2 ∧ (interval d n h).2 ≤ d := by
  induction n with
  | zero => exact ⟨hd,le_rfl⟩
  | succ n ih =>
    have hi := ih h.1
    have hb := bisect_bounds hi.1 h.2.1
    exact ⟨hb.2.1,hb.2.2.trans hi.2⟩

def nextIndex {E : Type*} (d : ℕ) (n : ℕ) (h : History E n) : ℕ :=
  if (interval d n h).2 ≤ (interval d n h).1+1 then (interval d n h).1
    else midpoint (interval d n h).1 (interval d n h).2

lemma nextIndex_bounds {E : Type*} {d : ℕ} (hd : 0<d) (n : ℕ) (h : History E n) :
    (interval d n h).1 ≤ nextIndex d n h ∧ nextIndex d n h < (interval d n h).2 := by
  have hi := (interval_bounds hd n h).1
  unfold nextIndex
  split_ifs with ht
  · exact ⟨le_rfl,hi⟩
  · have hm := midpoint_strict (by omega : (interval d n h).1+1 < (interval d n h).2)
    exact ⟨hm.1.le,hm.2⟩

def anchors {V E : Type*} (d : ℕ) (x : ℕ → V) : (n : ℕ) → History E n → List (V × Bool)
  | 0, _ => [(x 0,true),(x d,false)]
  | n+1, h => anchors d x n h.1 ++ [(x (nextIndex d n h.1),h.2.1)]

def anchorSet {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) : Set V :=
  {v | ∃ b, (v,b) ∈ anchors d x n h}

lemma anchors_length {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (anchors d x n h).length = n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [anchors,List.length_append,List.length_singleton,ih]

lemma anchorSet_step {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1)) :
    anchorSet d x (n+1) h = insert (x (nextIndex d n h.1)) (anchorSet d x n h.1) := by
  ext v
  constructor
  · rintro ⟨b,hb⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact Or.inr ⟨b,hb⟩
    · exact Or.inl (congrArg Prod.fst (List.mem_singleton.mp hb))
  · rintro (rfl | ⟨b,hb⟩)
    · exact ⟨h.2.1,List.mem_append_right _ (List.mem_singleton_self _)⟩
    · exact ⟨b,List.mem_append_left _ hb⟩

lemma endpoint_mem {V E : Type*} {d : ℕ} (_hd : 0<d) (x : ℕ → V) (n : ℕ) (h : History E n) :
    x (interval d n h).1 ∈ anchorSet d x n h ∧
      x (interval d n h).2 ∈ anchorSet d x n h := by
  induction n with
  | zero => constructor <;> simp [interval,anchorSet,anchors]
  | succ n ih =>
    have hi := ih h.1
    rw [anchorSet_step]
    change x (bisect _ _ _).1 ∈ _ ∧ x (bisect _ _ _).2 ∈ _
    unfold bisect
    split_ifs with ht hb
    · exact ⟨Or.inr hi.1,Or.inr hi.2⟩
    · have ha : nextIndex d n h.1 = midpoint (interval d n h.1).1 (interval d n h.1).2 := by
        rw [nextIndex,ite_eq_right ht]
      exact ⟨Or.inl (congrArg x ha.symm),Or.inr hi.2⟩
    · have ha : nextIndex d n h.1 = midpoint (interval d n h.1).1 (interval d n h.1).2 := by
        rw [nextIndex,ite_eq_right ht]
      exact ⟨Or.inr hi.1,Or.inl (congrArg x ha.symm)⟩

noncomputable def firstIndex (P : ℕ → Prop) : ℕ :=
  if h : ∃ j, P j then Nat.find h else 0

lemma firstIndex_spec {P : ℕ → Prop} (h : ∃ j, P j) : P (firstIndex P) := by
  rw [firstIndex,dite_eq_left h]
  exact Nat.find_spec h

lemma firstIndex_le {P : ℕ → Prop} {j : ℕ} (hj : P j) : firstIndex P ≤ j := by
  rw [firstIndex,dite_eq_left ⟨j,hj⟩]
  exact Nat.find_min' _ hj

variable {V E : Type*} (G : BondGraph V E)

def parentPredicate (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) (j : ℕ) : Prop :=
  ∃ z, L[j]? = some z ∧ match m with
    | none => (G.openGraph ω).Reachable a z.1
    | some e => ∃ v ∈ G.ends e, (G.openGraph ω).Reachable z.1 v

noncomputable def parent (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : ℕ :=
  firstIndex (parentPredicate G L a ω m)

noncomputable def side (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E) : Bool :=
  ((L[parent G L a ω m]?).getD (a,true)).2

lemma parentPredicate_congr (L : List (V × Bool)) (S : Set V) (a : V)
    (hL : ∀ z ∈ L, z.1 ∈ S) (ha : a ∈ S) (ω η : Set E)
    (h : G.clusterObject ω S = G.clusterObject η S) (m : Option E) (j : ℕ) :
    parentPredicate G L a ω m j ↔ parentPredicate G L a η m j := by
  have hr (v : V) (hv : v ∈ S) (u : V) :
      (G.openGraph ω).Reachable v u ↔ (G.openGraph η).Reachable v u := by
    apply G.reachable_incidence_congr
    rintro e ⟨r,her,hvr⟩
    have hib : (G.clusterObject ω S).2 e ↔ (G.clusterObject η S).2 e := by rw [h]
    have hei : e ∈ G.incidentEdges (G.clusterObject ω S).1 := ⟨r,⟨v,hv,hvr⟩,her⟩
    have hei' : e ∈ G.incidentEdges (G.clusterObject η S).1 := h ▸ hei
    change (ω e ∧ e ∈ G.incidentEdges (G.clusterObject ω S).1) ↔
      (η e ∧ e ∈ G.incidentEdges (G.clusterObject η S).1) at hib
    simpa only [hei,hei',and_true] using hib
  unfold parentPredicate
  apply exists_congr
  intro z
  by_cases hz : L[j]? = some z
  · have hzmem : z ∈ L := List.mem_of_getElem? hz
    simp only [hz,true_and]
    cases m with
    | none => exact hr a ha z.1
    | some e => exact exists_congr (fun v => and_congr_right (fun _ => hr z.1 (hL z hzmem) v))
  · simp only [hz,false_and]

lemma side_record (L : List (V × Bool)) (S : Set V) (a : V)
    (hL : ∀ z ∈ L, z.1 ∈ S) (ha : a ∈ S) (ω η : Set E)
    (h : G.clusterObject ω S = G.clusterObject η S) (m : Option E) :
    side G L a ω m = side G L a η m := by
  have he : parentPredicate G L a ω m = parentPredicate G L a η m :=
    funext (fun j => propext (parentPredicate_congr G L S a hL ha ω η h m j))
  simp only [side,parent,he]

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

noncomputable def density : (n : ℕ) → History E n → (E → Prop) → ℝ
  | 0, _, ω => r₀ ω
  | n+1, h, ω =>
    if side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 then
      density n h.1 ω * G.contactKernel order (anchorSet d x n h.1)
        (x (nextIndex d n h.1)) p w (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2
      else 0

lemma density_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hr₀ : ∀ ω, 0 ≤ r₀ ω) (n : ℕ) (h : History E n)
    (ω : E → Prop) : 0 ≤ density G order d x p w r₀ n h ω := by
  induction n with
  | zero => exact hr₀ ω
  | succ n ih =>
    rw [density]
    split_ifs
    · exact mul_nonneg (ih h.1) (G.contactKernel_nonneg order _ _ hp w h0 h1 _ ω _)
    · exact le_rfl

lemma density_record
    (hr₀ : ∀ ω η, G.clusterObject ω ({x 0,x d} : Set V) =
      G.clusterObject η {x 0,x d} → r₀ ω = r₀ η)
    (n : ℕ) (h : History E n) (ω η : E → Prop)
    (he : G.clusterObject ω (anchorSet d x n h) = G.clusterObject η (anchorSet d x n h)) :
    density G order d x p w r₀ n h ω = density G order d x p w r₀ n h η := by
  induction n with
  | zero =>
    apply hr₀
    convert he using 2 <;> ext v <;> simp [anchorSet,anchors,or_comm]
  | succ n ih =>
    have hST : anchorSet d x n h.1 ⊆ anchorSet d x (n+1) h := by
      rw [anchorSet_step]
      exact Set.subset_insert _ _
    have ha : x (nextIndex d n h.1) ∈ anchorSet d x (n+1) h := by
      rw [anchorSet_step]
      exact Set.mem_insert _ _
    have hs := side_record G (anchors d x n h.1) _ _
      (fun z hz => hST ⟨z.2,hz⟩) ha ω η he h.2.2
    rw [density,density,hs]
    split_ifs
    · rw [ih h.1 (G.clusterObject_refines hST ω η he)]
      rw [G.contactKernel_record order _ _ _ _ hST ha p w ω η he]
    · rfl

theorem density_normalized (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hr₀ : ∀ ω η, G.clusterObject ω ({x 0,x d} : Set V) =
      G.clusterObject η {x 0,x d} → r₀ ω = r₀ η)
    (hZ : expect w r₀ = 1)
    (hh : ∀ n (h : History E n), 0 < prob w (fun σ => ∃ b ∈ anchorSet d x n h,
      (G.openGraph σ).Reachable (x (nextIndex d n h)) b)) (n : ℕ) :
    ∑ h : History E n, expect w (density G order d x p w r₀ n h) = 1 := by
  induction n with
  | zero =>
    change (∑ _h : PUnit, expect w r₀) = 1
    simpa only [Fintype.sum_unique] using hZ
  | succ n ih =>
    have hs := G.adaptive_marked_step order ho (anchorSet d x n) (anchorSet d x n)
      (fun _ => Set.Subset.rfl) (fun h => x (nextIndex d n h)) hp w h0 h1 (hh n)
      (density G order d x p w r₀ n)
      (fun h ω η he => density_record G order d x p w r₀ hr₀ n h ω η he)
      (fun h ω m => side G (anchors d x n h) (x (nextIndex d n h)) ω m)
    change (∑ h : History E n × Bool × Option E, _) = 1
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ h : History E n, expect w (fun ω => ∑ m : Option E, ∑ b : Bool,
          if side G (anchors d x n h) (x (nextIndex d n h)) ω m = b then
            density G order d x p w r₀ n h ω * G.contactKernel order (anchorSet d x n h)
              (x (nextIndex d n h)) p w (G.clusterObject ω (anchorSet d x n h)) ω m else 0) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Fintype.sum_prod_type]
        simp_rw [←expect_sum]
        congr 1
        funext ω
        exact Finset.sum_comm
      _ = ∑ h : History E n, expect w (density G order d x p w r₀ n h) := hs
      _ = 1 := ih

end Density

lemma base_left_mem {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    x 0 ∈ anchorSet d x n h := by
  induction n with
  | zero => exact ⟨true,by simp [anchors]⟩
  | succ n ih => rw [anchorSet_step]; exact Or.inr (ih h.1)

lemma root_bound [Fintype E] {d : ℕ} (hd : 0<d) (x : ℕ → V)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    {c : ℝ} (hc1 : c≤1)
    (hc : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (n : ℕ) (h : History E n) :
    c ≤ prob w (fun ω => ∃ b ∈ anchorSet d x n h,
      (G.openGraph ω).Reachable (x (nextIndex d n h)) b) := by
  let j := nextIndex d n h
  have hj : j<d := (nextIndex_bounds hd n h).2.trans_le (interval_bounds hd n h).2
  by_cases hj0 : j=0
  · have he : prob w (fun ω => ∃ b ∈ anchorSet d x n h,
        (G.openGraph ω).Reachable (x j) b) = 1 := by
      calc
        _ = prob w (fun _ => True) := prob_congr w (fun ω => ⟨fun _ => True.intro,
          fun _ => ⟨x 0,base_left_mem d x n h,hj0 ▸ SimpleGraph.Reachable.refl _⟩⟩)
        _ = 1 := prob_true w hw
    exact hc1.trans_eq he.symm
  · exact (hc j (by omega) hj).trans (prob_mono w hn (fun ω hr =>
      ⟨x 0,base_left_mem d x n h,hr.symm⟩))

lemma reachable_record {S : Set V} {a b : V} (ha : a ∈ S) {ω η : Set E}
    (h : G.clusterObject ω S = G.clusterObject η S) :
    (G.openGraph ω).Reachable a b ↔ (G.openGraph η).Reachable a b := by
  calc
    _ ↔ (G.openGraph (G.clusterObject ω S).2).Reachable a b :=
      (G.reachable_clusterObject ha).symm
    _ ↔ (G.openGraph (G.clusterObject η S).2).Reachable a b := by rw [h]
    _ ↔ _ := G.reachable_clusterObject ha

lemma cluster_record {S : Set V} {a : V} (ha : a ∈ S) {ω η : Set E}
    (h : G.clusterObject ω S = G.clusterObject η S) : G.cluster ω a = G.cluster η a := by
  ext b
  exact reachable_record G ha h

section Seed
variable [Fintype V] [Fintype E]

def endpointEvent (u v : V) (s : ℕ) (ω : Set E) : Prop :=
  ¬ (G.openGraph ω).Reachable u v ∧
    s ≤ (G.cluster ω u).toFinset.card ∧ s ≤ (G.cluster ω v).toFinset.card

noncomputable def seed (w : E → Prop → ℝ) (u v : V) (s : ℕ) (ω : E → Prop) : ℝ :=
  (prob w (endpointEvent G u v s))⁻¹ * if endpointEvent G u v s ω then 1 else 0

omit [Fintype E] in
lemma endpointEvent_record (u v : V) (s : ℕ) (ω η : Set E)
    (h : G.clusterObject ω {u,v} = G.clusterObject η {u,v}) :
    endpointEvent G u v s ω ↔ endpointEvent G u v s η := by
  unfold endpointEvent
  rw [reachable_record G (Set.mem_insert u {v}) h,
    cluster_record G (Set.mem_insert u {v}) h,
    cluster_record G (Set.mem_insert_of_mem u (Set.mem_singleton v)) h]

lemma seed_record (w : E → Prop → ℝ) (u v : V) (s : ℕ) (ω η : E → Prop)
    (h : G.clusterObject ω {u,v} = G.clusterObject η {u,v}) :
    seed G w u v s ω = seed G w u v s η := by
  simp only [seed,endpointEvent_record G u v s ω η h]

lemma seed_normalized (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) : expect w (seed G w u v s) = 1 := by
  unfold seed
  rw [expect_const_mul]
  change (prob w (endpointEvent G u v s))⁻¹ * prob w (endpointEvent G u v s) = 1
  exact inv_mul_cancel₀ hδ.ne'

lemma seed_nonneg (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) (ω : E → Prop) : 0 ≤ seed G w u v s ω := by
  unfold seed
  apply mul_nonneg (inv_nonneg.mpr hδ.le)
  split_ifs <;> norm_num

end Seed

section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem endpoint_density_normalized (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) {d : ℕ} (hd : 2≤d) (x : ℕ → V)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) (n : ℕ) :
    ∑ h : History E n, expect w
      (density G order d x p w (seed G w (x 0) (x d) s) n h) = 1 := by
  have hw := homogeneous_normalized w p h0 h1
  have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  apply density_normalized G order d x p w _ ho hp h0 h1
    (seed_record G w (x 0) (x d) s) (seed_normalized G w (x 0) (x d) s hδ)
  intro k h
  apply hc.trans_le
  exact root_bound G (by omega : 0<d) x w hw hn
    ((hconn 0 1 (by omega) (by omega) (by omega)).trans (prob_le_one w hw hn _))
    (fun j hj hjd => hconn 0 j hj hjd.le (by simpa using hjd)) k h

lemma kernel_parent_exists (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0) :
    ∃ j, parentPredicate G (anchors d x n h) a ω m j := by
  by_cases ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1
  · have hm : m=none := by
      by_contra hm
      simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
      exact hk rfl
    subst m
    obtain ⟨v,⟨b,hb⟩,hr⟩ := ha
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    exact ⟨j,(v,b),hj,hr.symm⟩
  · cases m with
    | none => simp only [contactKernel,ite_eq_right ha] at hk; exact (hk rfl).elim
    | some e =>
      have he : e ∈ G.cutEdges (G.clusterObject ω (anchorSet d x n h)).1 := by
        by_contra he
        simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
        exact hk rfl
      obtain ⟨u,v,heq,-,z,⟨b,hb⟩,hr⟩ := he
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
      refine ⟨j,(z,b),hj,v,?_,hr⟩
      simp [heq]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma parent_lt_of_exists (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (h : ∃ j, parentPredicate G L a ω m j) : parent G L a ω m < L.length := by
  obtain ⟨z,hz,-⟩ := firstIndex_spec h
  exact (List.getElem?_eq_some_iff.mp hz).1

lemma density_step_support (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)
    (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    density G order d x p w r₀ n h.1 ω ≠ 0 ∧
    G.contactKernel order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
      (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2 ≠ 0 ∧
    side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 := by
  rw [density] at hr
  split_ifs at hr with hs
  · exact ⟨(mul_ne_zero_iff.mp hr).1,(mul_ne_zero_iff.mp hr).2,hs⟩
  · exact (hr rfl).elim

end ExactLaw

end CriticalPercolation.BinaryLaw
end
end

end OAI
