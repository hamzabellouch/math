import OAI.Combinatorics.ListHadwiger.EggCover

namespace OAI

namespace ReedSeymour
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

section Weights
variable [Fintype V]

noncomputable def mass (w : V → ℝ) (S : Set V) : ℝ := by
  classical
  exact ∑ v, if v ∈ S then w v else 0

lemma mass_empty (w : V → ℝ) : mass w ∅ = 0 := by simp [mass]
lemma mass_univ (w : V → ℝ) : mass w Set.univ = ∑ v, w v := by simp [mass]

lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (S : Set V) : 0 ≤ mass w S := by
  classical
  exact Finset.sum_nonneg (fun v _ => by split_ifs; exact hw v; exact le_refl 0)

lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {S T : Set V} (hst : S ⊆ T) :
    mass w S ≤ mass w T := by
  classical
  apply Finset.sum_le_sum
  intro v _
  by_cases hs : v ∈ S
  · simp [hs,hst hs]
  · simp only [hs,ite_false]
    split_ifs <;> simp [hw]

lemma mass_union {w : V → ℝ} {S T : Set V} (h : Disjoint S T) :
    mass w (S ∪ T) = mass w S + mass w T := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hh : ¬(v ∈ S ∧ v ∈ T) := fun hv => Set.disjoint_left.mp h hv.1 hv.2
  by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all

lemma mass_two_colors (w : V → ℝ) (S : Set V) (c : V → Fin 2) :
    mass w S = mass w {v | v ∈ S ∧ c v = 0} + mass w {v | v ∈ S ∧ c v = 1} := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hc : c v = 0 ∨ c v = 1 := by omega
  rcases hc with hc | hc <;> by_cases hv : v ∈ S <;> simp [hc,hv]

lemma heavy_color (w : V → ℝ) (S : Set V) (c : V → Fin 2) :
    ∃ q : Fin 2, mass w S ≤ 2 * mass w {v | v ∈ S ∧ c v = q} := by
  have hh := mass_two_colors w S c
  by_cases he : mass w {v | v ∈ S ∧ c v = 0} ≤ mass w {v | v ∈ S ∧ c v = 1}
  · exact ⟨1,by linarith⟩
  · exact ⟨0,by linarith⟩

lemma independent_color_class {V : Type u} {G : SimpleGraph V} [Fintype V] {S : Set V} {c : V → Fin 2}
    (hc : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y) (q : Fin 2) :
    Independent G {v | v ∈ S ∧ c v = q} := by
  rintro x ⟨hx,hcx⟩ y ⟨hy,hcy⟩ hxy
  exact hc x hx y hy hxy (hcx.trans hcy.symm)

def Outside (B : V → Set V) : Set V := {x | ∀ i, x ∉ B i}

structure EggCover (G : SimpleGraph V) (w : V → ℝ) (k : ℕ) where
  bag : V → Set V
  yolk : V → Set V
  color : V → Fin k
  root : ∀ i, (bag i).Nonempty → i ∈ bag i
  connected : ∀ i, (bag i).Nonempty → (G.induce (bag i)).Connected
  disjoint : ∀ i j, i ≠ j → Disjoint (bag i) (bag j)
  yolk_subset : ∀ i, yolk i ⊆ bag i
  stable : ∀ i, Independent G (yolk i)
  half : ∀ i, mass w (bag i) ≤ 2 * mass w (yolk i)
  proper : ∀ i j, i ≠ j → Touch G (bag i) (bag j) → color i ≠ color j
  frontier : ∀ X : Set V, X ⊆ Outside bag → (G.induce X).Connected →
    ∀ i j, i ≠ j → Touch G X (bag i) → Touch G X (bag j) → Touch G (bag i) (bag j)

noncomputable def EggCover.empty (G : SimpleGraph V) (w : V → ℝ) {k : ℕ} (hk : 0 < k) :
    EggCover G w k where
  bag := fun _ => ∅
  yolk := fun _ => ∅
  color := fun _ => ⟨0,hk⟩
  root := by simp
  connected := by simp
  disjoint := by simp
  yolk_subset := by simp
  stable := fun _ => independent_empty
  half := by simp [mass_empty]
  proper := by simp [Touch]
  frontier := by simp [Touch]

lemma EggCover.outside_disjoint {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    {S : Set V} (hS : S ⊆ Outside P.bag) (i : V) : Disjoint S (P.bag i) := by
  exact Set.disjoint_left.mpr (fun x hx hi => hS hx i hi)

structure Region {w : V → ℝ} {k : ℕ} (P : EggCover G w k) (X : Set V) : Prop where
  subset : X ⊆ Outside P.bag
  connected : (G.induce X).Connected
  closed : ∀ x ∈ X, ∀ y ∈ Outside P.bag, G.Adj x y → y ∈ X

lemma EggCover.component_region {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    {a : V} (ha : a ∈ Outside P.bag) : Region P (component G (Outside P.bag) a) := by
  refine ⟨component_subset _ _, component_connected ha, ?_⟩
  intro x hx y hy hxy
  exact hx.trans (ReachOn.adj hx.right hy hxy)

lemma ReachOn.stays {V : Type u} {G : SimpleGraph V} [Fintype V] {R X : Set V} {a b : V} (h : ReachOn G R a b) (ha : a ∈ X)
    (hstep : ∀ x ∈ X, ∀ y ∈ R, G.Adj x y → y ∈ X) : b ∈ X := by
  obtain ⟨p,hp⟩ := h
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih =>
    apply ih
    · exact hstep a ha c (hp c (by simp)) hac
    · exact fun x hx => hp x (by simp [hx])

lemma Region.contains_connected {w : V → ℝ} {k : ℕ} {P : EggCover G w k}
    {X D : Set V} (hX : Region P X) (hD : D ⊆ Outside P.bag)
    (hc : (G.induce D).Connected) (hinter : (D ∩ X).Nonempty) : D ⊆ X := by
  obtain ⟨a,haD,haX⟩ := hinter
  intro b hb
  exact ((connected_reachOn hc haD hb).mono hD).stays haX hX.closed

lemma Region.contains_of_touch {w : V → ℝ} {k : ℕ} {P : EggCover G w k}
    {X D Q : Set V} (hX : Region P X) (hD : D ⊆ Outside P.bag)
    (hc : (G.induce D).Connected) (hQ : Q ⊆ X) (ht : Touch G D Q) : D ⊆ X := by
  obtain ⟨a,ha,b,hb,hab⟩ := ht
  exact hX.contains_connected hD hc ⟨a,ha,hX.closed b (hQ hb) a (hD ha) hab.symm⟩

lemma outside_update_subset {V : Type u} [Fintype V] [DecidableEq V] {B : V → Set V} {i : V} {S : Set V}
    (hi : B i ⊆ S) : Outside (Function.update B i S) ⊆ Outside B := by
  intro x hx j
  by_cases hj : j = i
  · subst j
    intro hm
    have hh := hx i
    simp only [Function.update_self] at hh
    exact hh (hi hm)
  · have hh := hx j
    simpa only [Function.update_of_ne hj] using hh

noncomputable def EggCover.replace [DecidableEq V] {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (i : V) (B Y : Set V) (c : Fin k) (hinc : P.bag i ⊆ B)
    (hroot : B.Nonempty → i ∈ B) (hconn : (G.induce B).Connected)
    (hdisj : ∀ j, j ≠ i → Disjoint B (P.bag j))
    (hY : Y ⊆ B) (hstable : Independent G Y) (hhalf : mass w B ≤ 2 * mass w Y)
    (hproper : ∀ j, i ≠ j → Touch G B (P.bag j) → c ≠ P.color j)
    (hfront : ∀ D : Set V, D ⊆ Outside (Function.update P.bag i B) →
      (G.induce D).Connected → ∀ j, i ≠ j →
      Touch G D B → Touch G D (P.bag j) → Touch G B (P.bag j)) : EggCover G w k := by
  classical
  refine {
    bag := Function.update P.bag i B
    yolk := Function.update P.yolk i Y
    color := Function.update P.color i c
    root := ?_
    connected := ?_
    disjoint := ?_
    yolk_subset := ?_
    stable := ?_
    half := ?_
    proper := ?_
    frontier := ?_ }
  · intro j hj
    by_cases he : j = i
    · subst j; simpa using hroot (by simpa using hj)
    · simpa [Function.update_of_ne he] using P.root j (by simpa [Function.update_of_ne he] using hj)
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [Function.update_self]
      exact hconn
    · rw [Function.update_of_ne he]
      exact P.connected j (by simpa [Function.update_of_ne he] using hj)
  · intro a b hab
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact (hab (ha.trans hb.symm)).elim
    · subst a; simpa [Function.update_of_ne hb] using hdisj b hb
    · subst b; simpa [Function.update_of_ne ha] using (hdisj a ha).symm
    · simpa [Function.update_of_ne ha,Function.update_of_ne hb] using P.disjoint a b hab
  · intro j
    by_cases he : j = i
    · subst j; simpa using hY
    · simpa [Function.update_of_ne he] using P.yolk_subset j
  · intro j
    by_cases he : j = i
    · subst j; simpa using hstable
    · simpa [Function.update_of_ne he] using P.stable j
  · intro j
    by_cases he : j = i
    · subst j; simpa using hhalf
    · simpa [Function.update_of_ne he] using P.half j
  · intro a b hab ht
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact (hab (ha.trans hb.symm)).elim
    · subst a
      simpa [Function.update_of_ne hb] using hproper b hab (by simpa [Function.update_of_ne hb] using ht)
    · subst b
      simpa [Function.update_of_ne ha] using
        (hproper a hab.symm (by simpa [Function.update_of_ne ha] using ht.symm)).symm
    · simpa [Function.update_of_ne ha,Function.update_of_ne hb] using
        P.proper a b hab (by simpa [Function.update_of_ne ha,Function.update_of_ne hb] using ht)
  · intro D hD hc a b hab hDa hDb
    have hDold := hD.trans (outside_update_subset hinc)
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact (hab (ha.trans hb.symm)).elim
    · subst a
      simpa [Function.update_of_ne hb] using hfront D hD hc b hab (by simpa using hDa)
        (by simpa [Function.update_of_ne hb] using hDb)
    · subst b
      simpa [Function.update_of_ne ha] using (hfront D hD hc a hab.symm (by simpa using hDb)
        (by simpa [Function.update_of_ne ha] using hDa)).symm
    · simpa [Function.update_of_ne ha,Function.update_of_ne hb] using
        P.frontier D hDold hc a b hab
          (by simpa [Function.update_of_ne ha] using hDa)
          (by simpa [Function.update_of_ne hb] using hDb)

noncomputable def EggCover.absorb [DecidableEq V] {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) {X : Set V} (hX : Region P X) (i : V)
    (Q J : Set V) (hQX : Q ⊆ X) (hQ : (G.induce Q).Connected)
    (ht : Touch G Q (P.bag i)) (hJ : J ⊆ Q) (hstable : Independent G J)
    (hhalf : mass w Q ≤ 2 * mass w J) (hnot : ¬Touch G (P.yolk i) J) : EggCover G w k := by
  have hQO := hQX.trans hX.subset
  have hBQ := (P.outside_disjoint hQO i).symm
  have hYJ := hBQ.mono (P.yolk_subset i) hJ
  have hiX : Touch G X (P.bag i) := ht.mono hQX Set.Subset.rfl
  refine P.replace i (P.bag i ∪ Q) (P.yolk i ∪ J) (P.color i) Set.subset_union_left
    (fun _ => Or.inl (P.root i ht.right_nonempty))
    (connected_union_of_touch (P.connected i ht.right_nonempty) hQ ht.symm) ?_ ?_
    (independent_union (P.stable i) hstable hnot) ?_ ?_ ?_
  · intro j hji
    refine Set.disjoint_left.mpr ?_
    intro x hx hj
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp (P.disjoint i j hji.symm) hx hj
    · exact hQO hx j hj
  · intro x hx
    exact hx.elim (fun hx => Or.inl (P.yolk_subset i hx)) (fun hx => Or.inr (hJ hx))
  · rw [mass_union hBQ, mass_union hYJ]
    have hh := P.half i
    linarith
  · intro j hij htj
    apply P.proper i j hij
    rcases touch_union_left.mp htj with htj | htj
    · exact htj
    · exact P.frontier X hX.subset hX.connected i j hij hiX (htj.mono hQX Set.Subset.rfl)
  · intro D hD hconn j hij hDi hDj
    have hDold := hD.trans (outside_update_subset (show P.bag i ⊆ P.bag i ∪ Q from Set.subset_union_left))
    apply Touch.mono (hA := Set.subset_union_left) (hB := Set.Subset.rfl)
    rcases touch_union_right.mp hDi with hDi | hDi
    · exact P.frontier D hDold hconn i j hij hDi hDj
    · have hDX := hX.contains_of_touch hDold hconn hQX hDi
      exact P.frontier X hX.subset hX.connected i j hij hiX (hDj.mono hDX Set.Subset.rfl)

lemma outside_update_strict [DecidableEq V] {B : V → Set V} {i : V} {S : Set V}
    (hi : B i ⊆ S) (hnew : (S ∩ Outside B).Nonempty) :
    Outside (Function.update B i S) ⊂ Outside B := by
  refine ⟨outside_update_subset hi, ?_⟩
  intro hback
  obtain ⟨x,hxS,hxO⟩ := hnew
  have hh := hback hxO i
  simp only [Function.update_self] at hh
  exact hh hxS

lemma outside_update_ncard_lt [DecidableEq V] {B : V → Set V} {i : V} {S : Set V}
    (hi : B i ⊆ S) (hnew : (S ∩ Outside B).Nonempty) :
    (Outside (Function.update B i S)).ncard < (Outside B).ncard :=
  Set.ncard_lt_ncard (outside_update_strict hi hnew)

lemma EggCover.absorb_improves {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) {X : Set V} (hX : Region P X) (i : V)
    (Q J : Set V) (hQX : Q ⊆ X) (hQ : (G.induce Q).Connected)
    (ht : Touch G Q (P.bag i)) (hJ : J ⊆ Q) (hstable : Independent G J)
    (hhalf : mass w Q ≤ 2 * mass w J) (hnot : ¬Touch G (P.yolk i) J) :
    ∃ P' : EggCover G w k, (Outside P'.bag).ncard < (Outside P.bag).ncard := by
  classical
  let P' := P.absorb hX i Q J hQX hQ ht hJ hstable hhalf hnot
  refine ⟨P', ?_⟩
  change (Outside (Function.update P.bag i (P.bag i ∪ Q))).ncard < (Outside P.bag).ncard
  apply outside_update_ncard_lt Set.subset_union_left
  obtain ⟨x,hx⟩ := (connected_iff_reachOn.mp hQ).1
  exact ⟨x,Or.inr hx,hX.subset (hQX hx)⟩

def CliqueBound (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (I : Type u) [Fintype I] (B : I → Set V),
    (∀ i, (G.induce (B i)).Connected) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    (∀ i j, i ≠ j → Touch G (B i) (B j)) → Fintype.card I ≤ k

lemma EggCover.free_color {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (hb : CliqueBound G k) {X U : Set V} (hX : Region P X)
    (hUX : U ⊆ X) (hU : (G.induce U).Connected)
    (ht : ∀ i, Touch G X (P.bag i) → Touch G U (P.bag i)) :
    ∃ c : Fin k, ∀ i, Touch G X (P.bag i) → c ≠ P.color i := by
  classical
  let I := {i : V // Touch G X (P.bag i)}
  let B : Option I → Set V := fun o => o.elim U (fun i => P.bag i.val)
  have hconn : ∀ o, (G.induce (B o)).Connected := by
    intro o
    cases o with
    | none => exact hU
    | some i => exact P.connected i i.property.right_nonempty
  have hdisj : ∀ a b, a ≠ b → Disjoint (B a) (B b) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some j => exact P.outside_disjoint (hUX.trans hX.subset) j
    | some i =>
      cases b with
      | none => exact (P.outside_disjoint (hUX.trans hX.subset) i).symm
      | some j => exact P.disjoint i j (fun he => hab (congrArg some (Subtype.ext he)))
  have htouch : ∀ a b, a ≠ b → Touch G (B a) (B b) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some j => exact ht j j.property
    | some i =>
      cases b with
      | none => exact (ht i i.property).symm
      | some j =>
        exact P.frontier X hX.subset hX.connected i j
          (fun he => hab (congrArg some (Subtype.ext he))) i.property j.property
  have hcard : Fintype.card I < k := by
    have hh := hb (Option I) B hconn hdisj htouch
    simp only [Fintype.card_option] at hh
    omega
  have hn : ¬Function.Surjective (fun i : I => P.color i) := by
    intro hs
    have hh := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin] at hh
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hn
  obtain ⟨c,hc⟩ := hn
  exact ⟨c, fun i hi => Ne.symm (hc ⟨i,hi⟩)⟩

lemma EggCover.add_improves {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) (hb : CliqueBound G k) {X : Set V} (hX : Region P X)
    (U J : Set V) (hUX : U ⊆ X) (hU : (G.induce U).Connected)
    (ht : ∀ i, Touch G X (P.bag i) → Touch G U (P.bag i))
    (hJ : J ⊆ U) (hstable : Independent G J) (hhalf : mass w U ≤ 2 * mass w J) :
    ∃ P' : EggCover G w k, (Outside P'.bag).ncard < (Outside P.bag).ncard := by
  classical
  obtain ⟨u,hu⟩ := (connected_iff_reachOn.mp hU).1
  have huO := hX.subset (hUX hu)
  have hbag : P.bag u = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact huO u (P.root u ⟨x,hx⟩)
  have hinc : P.bag u ⊆ U := by simp [hbag]
  obtain ⟨c,hc⟩ := P.free_color hb hX hUX hU ht
  have hproper : ∀ j, u ≠ j → Touch G U (P.bag j) → c ≠ P.color j :=
    fun j _ hj => hc j (hj.mono hUX Set.Subset.rfl)
  have hfront : ∀ D : Set V, D ⊆ Outside (Function.update P.bag u U) →
      (G.induce D).Connected → ∀ j, u ≠ j →
      Touch G D U → Touch G D (P.bag j) → Touch G U (P.bag j) := by
    intro D hD hDconn j _ hDU hDj
    have hDX := hX.contains_of_touch (hD.trans (outside_update_subset hinc)) hDconn hUX hDU
    exact ht j (hDj.mono hDX Set.Subset.rfl)
  let P' := P.replace u U J c hinc (fun _ => hu) hU
    (fun j _ => P.outside_disjoint (hUX.trans hX.subset) j)
    hJ hstable hhalf hproper hfront
  refine ⟨P', ?_⟩
  change (Outside (Function.update P.bag u U)).ncard < (Outside P.bag).ncard
  exact outside_update_ncard_lt hinc ⟨u,hu,huO⟩

def Interface (G : SimpleGraph V) (B : Set V) : Set V := {x | ∃ y ∈ B, G.Adj x y}

lemma touch_iff_interface {V : Type u} {G : SimpleGraph V} [Fintype V] {A B : Set V} : Touch G A B ↔ (A ∩ Interface G B).Nonempty := by
  rfl

lemma EggCover.improve_region {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) (hb : CliqueBound G k) {X : Set V} (hX : Region P X) :
    ∃ P' : EggCover G w k, (Outside P'.bag).ncard < (Outside P.bag).ncard := by
  classical
  let I := {i : V // Touch G X (P.bag i)}
  let N : I → Set V := fun i => Interface G (P.bag i)
  have hN : ∀ i, (X ∩ N i).Nonempty := fun i => touch_iff_interface.mp i.property
  rcases connected_transversal_or_split_on hX.connected hN with ⟨U,hUX,hU,hmeet,hcolor⟩ | ⟨s,hsX⟩
  · obtain ⟨c,hc⟩ := colorable_induce_iff_total.mp hcolor
    obtain ⟨q,hq⟩ := heavy_color w U c
    refine P.add_improves hb hX U {v | v ∈ U ∧ c v = q} hUX hU ?_
      (fun _ h => h.1) (independent_color_class hc q) hq
    intro i hi
    exact touch_iff_interface.mpr (hmeet ⟨i,hi⟩)
  · obtain ⟨q,hq⟩ := heavy_color w s.carrier s.color
    have hJ := independent_color_class s.proper q
    by_cases he : q = 0
    · refine P.absorb_improves hX s.right.val s.carrier
        {v | v ∈ s.carrier ∧ s.color v = q} hsX s.connected
        (touch_iff_interface.mpr s.meets_right) (fun _ h => h.1) hJ hq ?_
      rintro ⟨a,ha,b,⟨hb,hbq⟩,hab⟩
      have hbi : b ∈ N s.right := ⟨a,P.yolk_subset s.right.val ha,hab.symm⟩
      have hh := s.right_color b hb hbi
      rw [he] at hbq
      exact (show (0 : Fin 2) ≠ 1 by decide) (hbq.symm.trans hh)
    · have he' : q = 1 := by omega
      refine P.absorb_improves hX s.left.val s.carrier
        {v | v ∈ s.carrier ∧ s.color v = q} hsX s.connected
        (touch_iff_interface.mpr s.meets_left) (fun _ h => h.1) hJ hq ?_
      rintro ⟨a,ha,b,⟨hb,hbq⟩,hab⟩
      have hbi : b ∈ N s.left := ⟨a,P.yolk_subset s.left.val ha,hab.symm⟩
      have hh := s.left_color b hb hbi
      rw [he'] at hbq
      exact (show (1 : Fin 2) ≠ 0 by decide) (hbq.symm.trans hh)

theorem exists_complete_egg_cover (w : V → ℝ) {k : ℕ} (hk : 0 < k)
    (hb : CliqueBound G k) : ∃ P : EggCover G w k, Outside P.bag = ∅ := by
  classical
  have hex : ∃ n : ℕ, ∃ P : EggCover G w k, (Outside P.bag).ncard = n :=
    ⟨_,EggCover.empty G w hk,rfl⟩
  obtain ⟨P,hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨P',hP'⟩ := P.improve_region hb (P.component_region ha)
  have hh := Nat.find_min' hex ⟨P',rfl⟩
  omega

lemma mass_iUnion {I : Type*} [Fintype I] (w : V → ℝ) (A : I → Set V)
    (hd : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    mass w (⋃ i, A i) = ∑ i, mass w (A i) := by
  classical
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : ∃ i, v ∈ A i
  · obtain ⟨i,hi⟩ := hv
    rw [ite_eq_left (Set.mem_iUnion.mpr ⟨i,hi⟩)]
    symm
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : v ∉ A j := fun hj => Set.disjoint_left.mp (hd j i hji) hj hi
      simp [hj]
    · simp
  · have hn : v ∉ ⋃ i, A i := by simpa using hv
    simp only [hn,ite_false]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hv ⟨i,hi⟩)

lemma EggCover.bag_mass {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (hP : Outside P.bag = ∅) : (∑ v, w v) = ∑ i, mass w (P.bag i) := by
  have hcov : (⋃ i, P.bag i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    by_contra hv
    have hout : v ∈ Outside P.bag := fun i hi => hv (Set.mem_iUnion.mpr ⟨i,hi⟩)
    rw [hP] at hout
    exact hout
  rw [← mass_iUnion w P.bag P.disjoint,hcov,mass_univ]

def EggCover.colorYolk {w : V → ℝ} {k : ℕ} (P : EggCover G w k) (c : Fin k) : Set V :=
  ⋃ i, {v | v ∈ P.yolk i ∧ P.color i = c}

lemma EggCover.colorYolk_independent {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (c : Fin k) : Independent G (P.colorYolk c) := by
  rintro x hx y hy hxy
  obtain ⟨i,hxi,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j,hyj,hj⟩ := Set.mem_iUnion.mp hy
  by_cases he : i = j
  · subst j
    exact P.stable i x hxi y hyj hxy
  · exact P.proper i j he ⟨x,P.yolk_subset i hxi,y,P.yolk_subset j hyj,hxy⟩
      (hi.trans hj.symm)

lemma EggCover.colorYolk_mass {w : V → ℝ} {k : ℕ} (P : EggCover G w k) (c : Fin k) :
    mass w (P.colorYolk c) = ∑ i, if P.color i = c then mass w (P.yolk i) else 0 := by
  classical
  rw [colorYolk,mass_iUnion]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P.color i = c
    · simp [hi]
    · simp [hi,mass_empty]
  · intro i j hij
    exact (P.disjoint i j hij).mono (fun _ h => P.yolk_subset i h.1)
      (fun _ h => P.yolk_subset j h.1)

lemma EggCover.sum_yolk_mass {w : V → ℝ} {k : ℕ} (P : EggCover G w k) :
    (∑ c : Fin k, mass w (P.colorYolk c)) = ∑ i, mass w (P.yolk i) := by
  classical
  simp_rw [P.colorYolk_mass]
  rw [Finset.sum_comm]
  simp

theorem dual_weight_bound (w : V → ℝ) {k : ℕ} (hk : 0 < k) (hb : CliqueBound G k)
    (hw : ∀ S : Set V, Independent G S → mass w S ≤ 1) : (∑ v, w v) ≤ 2 * k := by
  classical
  obtain ⟨P,hP⟩ := exists_complete_egg_cover w hk hb
  have hsum : (∑ i, mass w (P.yolk i)) ≤ (k : ℝ) := by
    rw [← P.sum_yolk_mass]
    calc
      (∑ c : Fin k, mass w (P.colorYolk c)) ≤ ∑ _c : Fin k, (1 : ℝ) :=
        Finset.sum_le_sum (fun c _ => hw _ (P.colorYolk_independent c))
      _ = k := by simp
  calc
    (∑ v, w v) = ∑ i, mass w (P.bag i) := P.bag_mass hP
    _ ≤ ∑ i, 2 * mass w (P.yolk i) := Finset.sum_le_sum (fun i _ => P.half i)
    _ = 2 * ∑ i, mass w (P.yolk i) := by rw [Finset.mul_sum]
    _ ≤ 2 * k := by linarith

end Weights
end ReedSeymour

end OAI
