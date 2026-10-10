import OAI.Computability.Scheduling.SplitPaths

namespace OAI

section

namespace ThreeMachine.Structure
section SamePaths
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {P : Set J → Prop}

theorem EdgeData.child_ssubset {a b v ap bp : ℕ} {B V A' B' : Boundary J}
    (D : EdgeData r rank atoms p W a b v ap bp B V A' B') :
    Window p.time ap bp ⊂ W := by
  have hsub : Window p.time ap bp ⊆ W := by
    intro x hx
    rw [D.parent]
    exact ⟨D.start_le.trans_lt hx.1, (hx.2.trans_le D.target_le).trans D.center_lt⟩
  have hv : 1 ≤ v ∧ v ≤ Fintype.card J / 3 := by
    have := Boundary.at_bounds D.endAt
    have := D.start_le
    have := D.strict
    have := D.target_le
    have := D.center_lt
    omega
  have hc := p.card_slot D.full.1 v hv.1 hv.2
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (p.slot v).card by omega)
  have ht := (p.mem_slot v x).mp hx
  have hxW : x ∈ W := by
    rw [D.parent]
    exact ⟨by have := D.start_le; have := D.strict; have := D.target_le; omega,
      ht ▸ D.center_lt⟩
  refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro he
  have hh : ap < p.time x ∧ p.time x < bp :=
    show x ∈ Window p.time ap bp from he.symm ▸ hxW
  have := D.target_le
  omega

omit [Fintype J] [DecidableEq J] in
theorem GlobalList.samePriority_final {K : GlobalList J} {B : ℕ} {Q : Set J}
    (hrank : ∀ x, rank x < B) (hhigh : ∀ x ∈ W, x ∈ K.Qual → x ∈ Q) :
    ∀ x ∈ W, x ∈ PriorityCut (K.samePriority rank B Q)
      (B + (K.indices.sup id + 1)*B) ↔ x ∈ Q := by
  classical
  intro x hx
  have hr := hrank x
  have hk := K.keyValue_bound hrank x
  change K.samePriority rank B Q x < B + (K.indices.sup id + 1)*B ↔ x ∈ Q
  by_cases hq : x ∈ K.Qual
  · have hQ := hhigh x hx hq
    simp only [samePriority, ite_eq_left hq, hQ, iff_true]
    omega
  · by_cases hQ : x ∈ Q <;>
      simp only [samePriority, ite_eq_right hq, hQ, ite_true, ite_false, iff_true, iff_false] <;> omega

theorem same_path_normalized (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) {B v : ℕ} {V : Boundary J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hv : D.a < v ∧ v < D.b)
    (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (D.right.pred r) v)
    (hnorm : p.NormalizedOn (Window p.time D.a v) r
      (D.list.samePriority rank B (D.right.pred r)))
    (hchild : ∀ U, U ⊂ W → Nonempty (NodeData r rank atoms p U) → P U) :
    Reached P r atoms W p.time D.a v := by
  classical
  let E := (Window p.time D.a v).toFinset
  have hE : ∀ x, x ∈ E ↔ x ∈ Window p.time D.a v := by intro x; simp [E]
  have hEeq : (↑E : Set J) = Window p.time D.a v := Set.ext hE
  have hsub : Window p.time D.a v ⊆ W := by
    intro x hx
    exact (D.window x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  let priority := D.list.samePriority rank B (D.right.pred r)
  let count := (D.list.indices.sup id + 1) * B
  have hfinalAgree : ∀ x ∈ Window p.time D.a v,
      x ∈ PriorityCut priority (B+count) ↔ x ∈ D.right.pred r := by
    intro x hx
    exact GlobalList.samePriority_final hrank D.high x (hsub hx)
  have hfinalSep : V.Separates r p.time (Window p.time D.a v)
      (PriorityCut priority (B+count)) v :=
    (Boundary.separates_congr (fun x hx => (hfinalAgree x hx).symm)).mp
      (hcenter.mono_domain hsub)
  have hvbounds : 1 ≤ v ∧ v ≤ Fintype.card J / 3 := by
    have := Boundary.at_bounds D.rightAt
    omega
  have hVactual := Boundary.actual_of_interior hV hvbounds
  have hedge {ap bp t : ℕ} {A' B' : Boundary J}
      (hap : D.a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
      (hAA : A'.At p.time (Fintype.card J / 3) ap)
      (hBB : B'.At p.time (Fintype.card J / 3) bp)
      (hact : ∃ Z, B' = Boundary.actual Z) (ht : t ≤ count)
      (hstart : A'.Separates r p.time (Window p.time D.a v)
        (PriorityCut priority (B+t)) ap)
      (hend : B'.Separates r p.time (Window p.time D.a v)
        (PriorityCut priority (B+t)) bp)
      (hwalk : CutoffWalk E r p.time priority (PriorityCut priority (B+t)) D.a ap)
      (hprev : Reached P r atoms W p.time D.a ap) :
      Reached P r atoms W p.time D.a bp := by
    obtain ⟨F⟩ := exists_same_edge D htrans hA hB hrank hstrict hv hV hcenter
      hap hab hbp hAA hBB hact ht hnorm hstart hend E hE hwalk
    exact F.reached hA F.finalSmall hprev
      (hchild _ F.child_ssubset ⟨F.toNode htrans hA⟩)
  by_cases ha : D.a = 0
  · have hL : D.left = Boundary.left := Boundary.at_unique D.leftAt ha
    apply hedge le_rfl hv.1 le_rfl D.leftAt hV hVactual le_rfl _ hfinalSep .refl (Or.inl rfl)
    rw [hL, ha]
    exact Boundary.left_separates
  · have habounds : 1 ≤ D.a ∧ D.a ≤ Fintype.card J / 3 := by omega
    obtain ⟨Z, hZ⟩ := Boundary.actual_of_interior D.leftAt habounds
    have hstartBoundary : D.left.Separates r p.time (Window p.time D.a v)
        (PriorityCut priority B) D.a := by
      constructor
      · intro x hx ht _
        have := hx.1
        omega
      · intro x hx _ hs
        apply D.low x (hsub hx)
        intro hq
        have hs' : priority x < B := hs
        dsimp only [priority, GlobalList.samePriority] at hs'
        rw [ite_eq_left hq] at hs'
        omega
    have hstart : Separator E r p.time (PriorityCut priority B) D.a := by
      apply (Boundary.actual_separates (hZ ▸ D.leftAt)).mp
      simpa only [hEeq, ← hZ] using hstartBoundary
    have hclosed : SlotClosed E p.time := by
      intro x hx y hy
      apply (hE y).mpr
      have hh := (hE x).mp hx
      simpa only [Window, Set.mem_ofPred, hy] using hh
    have hpriority := GlobalList.samePriority_extends hrank hstrict D.upsets
      (fun _ _ hxy hy => Boundary.pred_downset htrans D.right hxy hy) D.high
    have hnormE : LocalObstruction E r p.time priority :=
      normalizedOn_local_obstruction (hEeq.symm ▸ hnorm) hE
    obtain ⟨walk⟩ := exists_numeric_walk htrans D.full.2 hclosed
      (Or.inr fun x hx => ((hE x).mp hx).1)
      (GlobalList.samePriority_injective hrank hinj).injOn
      (fun x hx y hy hxy => hpriority x (hsub ((hE x).mp hx)) y (hsub ((hE y).mp hy)) hxy)
      hnormE hstart count
    have hpos : ∀ i, walk.position i < v := by
      intro i
      rcases walk.endpoint i with he | ⟨x, hx, ht⟩
      · simpa only [he] using hv.1
      · exact ht ▸ ((hE x).mp hx).2
    apply walk.reached hpos
    · intro i bp hab hbp hsep hprev
      have hap := (walk.history i).le
      have haps : 1 ≤ walk.position i ∧ walk.position i ≤ Fintype.card J / 3 := by
        have := hpos i
        omega
      have hbps : 1 ≤ bp ∧ bp ≤ Fintype.card J / 3 := by omega
      exact hedge hap hab hbp (p.triple_at D.full.1 _ haps.1 haps.2)
        (p.triple_at D.full.1 _ hbps.1 hbps.2) ⟨_, rfl⟩ (by have := i.isLt; omega)
        (separator_at D.full hE haps (walk.separator i))
        (separator_at D.full hE hbps hsep) (walk.history i) hprev
    · obtain ⟨Q, hQ⟩ := hVactual
      apply (Boundary.actual_separates (hQ ▸ hV)).mp
      simpa only [hEeq, ← hQ] using hfinalSep

end SamePaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SwitchPaths
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p q : Layout J} {W : Set J} {P : Set J → Prop}

omit [DecidableEq J] in
def SwitchSeed.reorder {L : Boundary J} {a b : ℕ}
    (G : SwitchSeed r p.time atoms W L a)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b) (hfix : p.FixedOutside q W) :
    SwitchSeed r q.time atoms W L a := by
  refine { G with later := ?_ }
  intro x hx
  by_cases hxW : x ∈ W
  · exact ((hfix.window hW x).mp hxW).1
  · rw [hfix.time hxW]
    exact G.later x hx

omit [Fintype J] [DecidableEq J] in
theorem switchPriority_final {B : ℕ} {D : Set J} (hrank : ∀ x, rank x < B) :
    PriorityCut (switchPriority rank B D) B = Dᶜ := by
  classical
  ext x
  have := hrank x
  change (if x ∈ D then B+rank x else rank x) < B ↔ x ∉ D
  split_ifs <;> simp_all

theorem switch_path_normalized {a b v B : ℕ} {L R V : Boundary J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) (hrank : ∀ x, rank x < B)
    (hinj : Function.Injective rank) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hL : L.At p.time (Fintype.card J / 3) a)
    (hR : R.At p.time (Fintype.card J / 3) b)
    (hcover : ∀ x ∈ W, x ∈ L.desc r ∨ x ∈ R.pred r)
    (G : SwitchSeed r p.time atoms W L a)
    (hv : a < v ∧ v < b) (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (L.desc r)ᶜ v)
    (hnorm : p.NormalizedOn (Window p.time a v) r (switchPriority rank B (L.desc r)))
    (hchild : ∀ U, U ⊂ W → Nonempty (NodeData r rank atoms p U) → P U) :
    Reached P r atoms W p.time a v := by
  classical
  let E := (Window p.time a v).toFinset
  have hE : ∀ x, x ∈ E ↔ x ∈ Window p.time a v := by intro x; simp [E]
  have hEeq : (↑E : Set J) = Window p.time a v := Set.ext hE
  have hsub : Window p.time a v ⊆ W := by
    intro x hx
    exact (hW x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  let priority := switchPriority rank B (L.desc r)
  have hfinalSep : V.Separates r p.time (Window p.time a v)
      (PriorityCut priority B) v := by
    rw [show PriorityCut priority B = (L.desc r)ᶜ from switchPriority_final hrank]
    exact hcenter.mono_domain hsub
  have hvbounds : 1 ≤ v ∧ v ≤ Fintype.card J / 3 := by
    have := Boundary.at_bounds hR
    omega
  have hVactual := Boundary.actual_of_interior hV hvbounds
  have hedge {ap bp t : ℕ} {A' B' : Boundary J}
      (hap : a ≤ ap) (hab : ap < bp) (hbp : bp ≤ v)
      (hAA : A'.At p.time (Fintype.card J / 3) ap)
      (hBB : B'.At p.time (Fintype.card J / 3) bp)
      (hact : ∃ Z, B' = Boundary.actual Z) (ht : t ≤ B)
      (hstart : A'.Separates r p.time (Window p.time a v) (PriorityCut priority t) ap)
      (hend : B'.Separates r p.time (Window p.time a v) (PriorityCut priority t) bp)
      (hprev : Reached P r atoms W p.time a ap) :
      Reached P r atoms W p.time a bp := by
    obtain ⟨F⟩ := exists_switch_edge hp htrans hA hrank hstrict hW hL hR hcover G
      hv hV hcenter hap hab hbp hAA hBB hact ht hnorm hstart hend
    exact F.reached hA F.finalSmall hprev
      (hchild _ F.child_ssubset ⟨F.toNode htrans hA⟩)
  by_cases ha : a = 0
  · have hLL : L = Boundary.left := Boundary.at_unique hL ha
    apply hedge le_rfl hv.1 le_rfl hL hV hVactual le_rfl _ hfinalSep (Or.inl rfl)
    rw [hLL, ha]
    exact Boundary.left_separates
  · have habounds : 1 ≤ a ∧ a ≤ Fintype.card J / 3 := by omega
    have hstart : Separator E r p.time (PriorityCut priority 0) a := by
      constructor
      · intro x hx ht _
        have := ((hE x).mp hx).1
        omega
      · intro x _ _ hs
        exact (Nat.not_lt_zero _ hs).elim
    have hclosed : SlotClosed E p.time := by
      intro x hx y hy
      apply (hE y).mpr
      have hh := (hE x).mp hx
      simpa only [Window, Set.mem_ofPred, hy] using hh
    have hpriority := switchPriority_extends hrank hstrict (Boundary.desc_upset htrans L)
    have hnormE : LocalObstruction E r p.time priority :=
      normalizedOn_local_obstruction (hEeq.symm ▸ hnorm) hE
    obtain ⟨walk⟩ := exists_numeric_walk htrans hp.2 hclosed
      (Or.inr fun x hx => ((hE x).mp hx).1)
      (switchPriority_injective hrank hinj).injOn
      (fun x _ y _ hxy => hpriority x y hxy) hnormE hstart B
    have hpos : ∀ i, walk.position i < v := by
      intro i
      rcases walk.endpoint i with he | ⟨x, hx, ht⟩
      · simpa only [he] using hv.1
      · exact ht ▸ ((hE x).mp hx).2
    apply walk.reached hpos
    · intro i bp hab hbp hsep hprev
      have hap := (walk.history i).le
      have haps : 1 ≤ walk.position i ∧ walk.position i ≤ Fintype.card J / 3 := by
        have := hpos i
        omega
      have hbps : 1 ≤ bp ∧ bp ≤ Fintype.card J / 3 := by omega
      exact hedge (t := i.val) hap hab hbp (p.triple_at hp.1 _ haps.1 haps.2)
        (p.triple_at hp.1 _ hbps.1 hbps.2) ⟨_, rfl⟩ (by have := i.isLt; omega)
        (separator_at hp hE haps (by simpa only [Nat.zero_add] using walk.separator i))
        (separator_at hp hE hbps (by simpa only [Nat.zero_add] using hsep)) hprev
    · obtain ⟨Q, hQ⟩ := hVactual
      apply (Boundary.actual_separates (hQ ▸ hV)).mp
      simpa only [Nat.zero_add, hEeq, ← hQ] using hfinalSep

end SwitchPaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section SideNormalization
variable {J A : Type} [Fintype J] [DecidableEq J]
    {r : J → J → Prop} {rank : J → ℕ} {atoms : A → Set J}
    {p : Layout J} {W : Set J} {P : Set J → Prop}

theorem same_path (D : NodeData r rank atoms p W)
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) {B v : ℕ} {V : Boundary J}
    (hB : 0 < B) (hrank : ∀ x, rank x < B) (hinj : Function.Injective rank)
    (hstrict : ∀ x y, r x y → rank x < rank y)
    (hv : D.a < v ∧ v < D.b)
    (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (D.right.pred r) v)
    (hchild : ∀ q U, U ⊂ W → Nonempty (NodeData r rank atoms q U) → P U) :
    Reached P r atoms W p.time D.a v := by
  let E := Window p.time D.a v
  have hsub : E ⊆ W := fun x hx => (D.window x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  obtain ⟨q, hfix, hnorm⟩ := exists_normalizedOn p E r
    (D.list.samePriority rank B (D.right.pred r)) D.full.2
  let Dq := D.reorder (hfix.mono hsub) hnorm.1
  have hE : E = Window q.time D.a v := Set.ext (hfix.window (fun _ => Iff.rfl))
  have hVq := hfix.boundary (fun _ => Iff.rfl) (Or.inr le_rfl) hV
  have hcenterq := hcenter.reorder hfix (fun _ => Iff.rfl) (Or.inr le_rfl)
  have hnormq : q.NormalizedOn (Window q.time Dq.a v) r
      (Dq.list.samePriority rank B (Dq.right.pred r)) := by
    change q.NormalizedOn (Window q.time D.a v) r
      (D.list.samePriority rank B (D.right.pred r))
    exact hE ▸ hnorm
  have hreach := same_path_normalized Dq htrans hA hB hrank hinj hstrict hv hVq
    hcenterq hnormq (hchild q)
  exact hreach.congr_time
    (fun x => (hfix.before_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)
    (fun x => (hfix.after_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)

theorem switch_path {a b v B : ℕ} {L R V : Boundary J}
    (hp : p.Full r) (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    (hA : AtomSupport atoms r rank) (hrank : ∀ x, rank x < B)
    (hinj : Function.Injective rank) (hstrict : ∀ x y, r x y → rank x < rank y)
    (hW : ∀ x, x ∈ W ↔ x ∈ Window p.time a b)
    (hL : L.At p.time (Fintype.card J / 3) a)
    (hR : R.At p.time (Fintype.card J / 3) b)
    (hcover : ∀ x ∈ W, x ∈ L.desc r ∨ x ∈ R.pred r)
    (G : SwitchSeed r p.time atoms W L a)
    (hv : a < v ∧ v < b) (hV : V.At p.time (Fintype.card J / 3) v)
    (hcenter : V.Separates r p.time W (L.desc r)ᶜ v)
    (hchild : ∀ q U, U ⊂ W → Nonempty (NodeData r rank atoms q U) → P U) :
    Reached P r atoms W p.time a v := by
  let E := Window p.time a v
  have hsub : E ⊆ W := fun x hx => (hW x).mpr ⟨hx.1, hx.2.trans hv.2⟩
  obtain ⟨q, hfix, hnorm⟩ := exists_normalizedOn p E r
    (switchPriority rank B (L.desc r)) hp.2
  have hE : E = Window q.time a v := Set.ext (hfix.window (fun _ => Iff.rfl))
  have hfixW := hfix.mono hsub
  have hWq := hfixW.window hW
  have hLq := hfixW.boundary hW (Or.inl le_rfl) hL
  have hRq := hfixW.boundary hW (Or.inr le_rfl) hR
  have hVq := hfix.boundary (fun _ => Iff.rfl) (Or.inr le_rfl) hV
  have hcenterq := hcenter.reorder hfix (fun _ => Iff.rfl) (Or.inr le_rfl)
  have hnormq : q.NormalizedOn (Window q.time a v) r
      (switchPriority rank B (L.desc r)) := by simpa only [hE] using hnorm
  have hreach := switch_path_normalized ⟨hp.1, hnorm.1⟩ htrans hA hrank hinj hstrict
    hWq hLq hRq hcover (G.reorder hW hfixW) hv hVq hcenterq hnormq (hchild q)
  exact hreach.congr_time
    (fun x => (hfix.before_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)
    (fun x => (hfix.after_iff (fun _ => Iff.rfl) (Or.inr le_rfl) x).symm)

end SideNormalization
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section ReversePaths
variable {J A : Type} [Fintype J] {r : J → J → Prop}
    {atoms : A → Set J} {p : Layout J} {W S : Set J}

theorem Boundary.Separates.reverse {B : Boundary J} {s : ℕ}
    (hfull : 3 ∣ Fintype.card J) (hs : s ≤ Fintype.card J / 3 + 1)
    (h : B.Separates r p.time W S s) :
    B.reverse.Separates (fun x y => r y x) p.reverse.time W Sᶜ
      (Fintype.card J / 3 + 1 - s) := by
  constructor
  · intro x hx ht hn
    have hxbound := p.time_bounds hfull x
    rw [p.reverse_time hfull] at ht
    have hl : s < p.time x := by omega
    have hxS : x ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hn
    simpa only [Boundary.pred_reverse] using h.2 x hx hl hxS
  · intro x hx ht hn
    have hxbound := p.time_bounds hfull x
    rw [p.reverse_time hfull] at ht
    have hl : p.time x < s := by omega
    simpa only [Boundary.desc_reverse] using h.1 x hx hl hn

theorem SplitVertex.AtTime.reverse {u : SplitVertex r atoms W} {s : ℕ}
    (hfull : 3 ∣ Fintype.card J) (hs : s ≤ Fintype.card J / 3 + 1)
    (h : u.AtTime p.time s) :
    u.reverse.AtTime p.reverse.time (Fintype.card J / 3 + 1 - s) := by
  constructor
  · intro x
    change x ∈ u.right ↔ _
    rw [h.2.2 x, p.reverse_time hfull]
    have := p.time_bounds hfull x
    apply and_congr_right
    intro _
    omega
  · constructor
    · intro x
      change x ∈ u.middle.val ↔ _
      rw [h.2.1 x, p.reverse_time hfull]
      have := p.time_bounds hfull x
      apply and_congr_right
      intro _
      omega
    · intro x
      change x ∈ u.left ↔ _
      rw [h.1 x, p.reverse_time hfull]
      have := p.time_bounds hfull x
      apply and_congr_right
      intro _
      omega

theorem window_reverse {a b : ℕ} (hfull : 3 ∣ Fintype.card J)
    (ha : a ≤ Fintype.card J / 3 + 1) (hb : b ≤ Fintype.card J / 3 + 1) :
    Window p.reverse.time (Fintype.card J / 3 + 1 - b) (Fintype.card J / 3 + 1 - a) =
      Window p.time a b := by
  ext x
  change (_ < p.reverse.time x ∧ p.reverse.time x < _) ↔ _ < p.time x ∧ p.time x < _
  rw [p.reverse_time hfull]
  have := p.time_bounds hfull x
  omega

end ReversePaths
end ThreeMachine.Structure

namespace ThreeMachine.Structure
section Completeness
variable {J A : Type} [Fintype J] [DecidableEq J] {atoms : A → Set J}

theorem node_complete (n : ℕ) :
    ∀ (r : J → J → Prop) (rank reverseRank : J → ℕ) (p : Layout J) (W : Set J) (B : ℕ),
    (∀ ⦃x y z⦄, r x y → r y z → r x z) →
    AtomSupport atoms r rank → AtomSupport atoms (fun x y => r y x) reverseRank →
    0 < B → (∀ x, rank x < B) → (∀ x, reverseRank x < B) →
    Function.Injective rank → Function.Injective reverseRank →
    (∀ x y, r x y → rank x < rank y) →
    (∀ x y, r y x → reverseRank x < reverseRank y) →
    NodeData r rank atoms p W → W.ncard ≤ n → AcceptedAt r atoms n W := by
  induction n with
  | zero =>
    intro r rank reverseRank p W B _ _ _ _ _ _ _ _ _ _ D hcard
    have hW : W = ∅ := (Set.ncard_eq_zero (Set.toFinite W)).mp (Nat.eq_zero_of_le_zero hcard)
    exact ⟨D.small.mono (by omega), hW⟩
  | succ n ih =>
    intro r rank reverseRank p W B htrans hA hAR hB hrank hrankR hinj hinjR hstrict hstrictR D hcard
    have hsmall : Described atoms W 10000 := D.small.mono (by omega)
    by_cases hWempty : W = ∅
    · exact ⟨hsmall, Or.inl hWempty⟩
    have hne : W.Nonempty := Set.nonempty_iff_ne_empty.mpr hWempty
    obtain ⟨q, hfix, hq, v, V, hav, hvb, hV, hcenter⟩ := exists_node_center D htrans hne
    let Dq := D.reorder hfix hq
    have hchild : ∀ q U, U ⊂ W → Nonempty (NodeData r rank atoms q U) →
        AcceptedAt r atoms n U := by
      intro q U hU hDU
      obtain ⟨DU⟩ := hDU
      have hlt := Set.ncard_lt_ncard hU
      exact ih r rank reverseRank q U B htrans hA hAR hB hrank hrankR
        hinj hinjR hstrict hstrictR DU (by omega)
    have hchildR : ∀ q U, U ⊂ W →
        Nonempty (NodeData (fun x y => r y x) reverseRank atoms q U) →
        AcceptedAt (fun x y => r y x) atoms n U := by
      intro q U hU hDU
      obtain ⟨DU⟩ := hDU
      have hlt := Set.ncard_lt_ncard hU
      exact ih (fun x y => r y x) reverseRank rank q U B
        (fun {_ _ _} hxy hyz => htrans hyz hxy) hAR hA hB hrankR hrank
        hinjR hinj hstrictR hstrict DU (by omega)
    have hleft := same_path Dq htrans hA hB hrank hinj hstrict ⟨hav, hvb⟩ hV hcenter hchild
    let T := Fintype.card J / 3
    have ha : D.a ≤ T+1 := Boundary.at_bounds D.leftAt
    have hb : D.b ≤ T+1 := Boundary.at_bounds D.rightAt
    have hv : v ≤ T+1 := by omega
    have hfrom : T+1-D.b < T+1-v := by omega
    have hto : T+1-v < T+1-D.a := by omega
    have hWr : ∀ x, x ∈ W ↔ x ∈ Window q.reverse.time (T+1-D.b) (T+1-D.a) := by
      rw [window_reverse D.full.1 ha hb]
      exact Dq.window
    have hcoverr : ∀ x ∈ W, x ∈ Dq.right.reverse.desc (fun x y => r y x) ∨
        x ∈ Dq.left.reverse.pred (fun x y => r y x) := by
      intro x hx
      simpa only [Boundary.desc_reverse, Boundary.pred_reverse, or_comm] using Dq.cover x hx
    have hcenterr : V.reverse.Separates (fun x y => r y x) q.reverse.time W
        (Dq.right.reverse.desc (fun x y => r y x))ᶜ (T+1-v) := by
      rw [Boundary.desc_reverse]
      exact hcenter.reverse D.full.1 hv
    have hright := switch_path (Layout.reverse_full Dq.full) (fun {_ _ _} hxy hyz => htrans hyz hxy)
      hAR hrankR hinjR hstrictR hWr (Boundary.at_reverse D.full.1 Dq.rightAt)
      (Boundary.at_reverse D.full.1 Dq.leftAt) hcoverr
      (Dq.reverseSeed.toSwitch D.full.1 hb) ⟨hfrom, hto⟩
      (Boundary.at_reverse D.full.1 hV) hcenterr hchildR
    rcases hleft with he | ⟨ul, vl, hul, hpl, hvl⟩
    · change v = D.a at he
      omega
    rcases hright with he | ⟨ur, vr, hur, hpr, hvr⟩
    · change T+1-v = T+1-D.b at he
      omega
    have hvback : T+1-(T+1-v) = v := by omega
    have hvr' : vr.reverse.AtTime q.time v := by
      have hh := hvr.reverse D.full.1 (Nat.sub_le (T+1) v)
      change vr.reverse.AtTime q.reverse.reverse.time (T+1-(T+1-v)) at hh
      rw [hvback] at hh
      simpa only [Layout.reverse_reverse] using hh
    have hsame : vl = vr.reverse := hvl.unique hvr'
    have hpr' := SplitVertex.path_reverse (fun _ h => AcceptedAt.reverse h) hpr
    refine ⟨hsmall, Or.inr ⟨ul, ur.reverse, hul, ?_, AcceptedAt.reverse hur⟩⟩
    exact hpl.trans (hsame.symm ▸ hpr')

end Completeness
end ThreeMachine.Structure

end

end OAI
