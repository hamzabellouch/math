import OAI.Combinatorics.HalvingLines.Greedy

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep
open Set

lemma state_eq_insert_below {n k : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {s : ℝ} {M : Finset (Fin n)} (hM : Separates P s M) (hcard : M.card=k)
    {a b : Fin n} (hab : a≠b) (hx : (P a).1≠(P b).1)
    (hR : Refines P (slope (P a) (P b)) s)
    (hs : projection s (P a)<projection s (P b)) (hk : 0<k)
    (hbelow : belowCount P a b=k-1) : M=insert a (belowSet P a b) := by
  classical
  apply states_unique hM (below_insert_separates hP hab hx hR hs)
  have hna : a∉belowSet P a b := by simp only [mem_belowSet,lt_self_iff_false,not_false_eq_true]
  rw [hcard,Finset.card_insert_of_notMem hna,card_belowSet,hbelow]
  omega

lemma states_change_of_pair {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    (i : Fin (traversal (criticalSlopes P)).size) {a b : Fin n} (hab : a≠b)
    (hc : (traversal (criticalSlopes P)).cut i.succ.castSucc=slope (P a) (P b))
    (hkpos : 0<k) (hbelow : belowCount P a b=k-1) :
    (states P hP hk).marks i.castSucc≠(states P hP hk).marks i.succ := by
  classical
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  have aux (a b : Fin n) (hx : (P a).1<(P b).1)
      (hc : T.cut i.succ.castSucc=slope (P a) (P b))
      (hb : belowCount P a b=k-1) : S.marks i.castSucc≠S.marks i.succ := by
    have hbounds := T.cut_bounds i
    rw [hc] at hbounds
    have ho := projection_order_at_slope hx hbounds.1 hbounds.2
    have hR := (T.sample_refines hP i).1
    rw [hc] at hR
    have hab' : a≠b := fun he => ne_of_lt hx (congrArg (fun x => (P x).1) he)
    have he := state_eq_insert_below hP.1 (S.separates i.castSucc) (S.card_marks i.castSucc)
      hab' hx.ne hR ho.1 hkpos hb
    intro hsame
    have ha : a∈S.marks i.succ := by rw [← hsame,he];exact Finset.mem_insert_self _ _
    have hb' : b∉S.marks i.succ := by
      rw [← hsame,he,Finset.mem_insert]
      simp only [mem_belowSet,tied_projection (P a) (P b) hx.ne,lt_self_iff_false,or_false]
      exact hab'.symm
    exact not_lt_of_gt ho.2 (S.separates i.succ a ha b hb')
  rcases lt_or_gt_of_ne (hP.2.1 a b hab) with hx | hx
  · exact aux a b hx hc hbelow
  · apply aux b a hx
    · simpa only [slope_symm (P b) (P a)] using hc
    · simpa only [belowCount_symm (hP.2.1 a b hab)] using hbelow

noncomputable def switchPairs {n : ℕ} (P : Fin n → Point) (k : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ 0<k ∧ k<n ∧ belowCount P ij.1 ij.2=k-1)

lemma mem_switchPairs {n : ℕ} (P : Fin n → Point) (k : ℕ) (p : Fin n × Fin n) :
    p∈switchPairs P k ↔ p.1<p.2 ∧ 0<k ∧ k<n ∧ belowCount P p.1 p.2=k-1 := by
  classical
  simp only [switchPairs,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def States.changeSteps {n T k : ℕ} {P : Fin n → Point} (S : @States n T k P) : Finset (Fin T) :=
  Finset.univ.filter (fun i => S.marks i.castSucc≠S.marks i.succ)

lemma States.mem_changeSteps {n T k : ℕ} {P : Fin n → Point} (S : @States n T k P) (i : Fin T) :
    i∈S.changeSteps ↔ S.marks i.castSucc≠S.marks i.succ := by
  classical
  simp only [States.changeSteps,Finset.mem_filter,Finset.mem_univ,true_and]

lemma switchCount_le_changes {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n) :
    switchCount P k≤(states P hP hk).changeSteps.card := by
  classical
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  have hex (p : ↥(switchPairs P k)) : ∃ i : Fin T.size, i∈S.changeSteps ∧
      T.cut i.succ.castSucc=slope (P p.val.1) (P p.val.2) := by
    have hp := (mem_switchPairs P k p.val).mp p.property
    obtain ⟨i,hi⟩ := (T.critical _).mp (mem_criticalSlopes P hp.1.ne)
    exact ⟨i,(S.mem_changeSteps i).mpr (states_change_of_pair hP hk i hp.1.ne hi hp.2.1 hp.2.2.2),hi⟩
  choose f hf hs using hex
  let g : ↥(switchPairs P k) → ↥S.changeSteps := fun p => ⟨f p,hf p⟩
  have hg : Function.Injective g := by
    intro p q h
    have he : f p=f q := congrArg Subtype.val h
    have heq := (hs p).symm.trans ((congrArg (fun j => T.cut j.succ.castSucc) he).trans (hs q))
    have hp := (mem_switchPairs P k p.val).mp p.property
    have hq := (mem_switchPairs P k q.val).mp q.property
    obtain ⟨h1,h2⟩ := hP.2.2.1 _ _ _ _ hp.1 hq.1 heq
    exact Subtype.ext (Prod.ext h1 h2)
  change (switchPairs P k).card≤S.changeSteps.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

lemma local_change_event {n k : ℕ} {P : Fin n → Point} (hP : Generic P)
    {s t c : ℝ} {M N : Finset (Fin n)}
    (hM : Separates P s M) (hN : Separates P t N) (hcardM : M.card=k) (hcardN : N.card=k)
    (hRs : Refines P c s) (hRt : Refines P c t) (hne : M≠N) :
    ∃ p∈switchPairs P k, slope (P p.1) (P p.2)=c := by
  classical
  have hneM : (M\N).Nonempty := by
    by_contra hh
    have hsub : M⊆N := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hh)
    exact hne (Finset.eq_of_subset_of_card_le hsub (hcardN.trans hcardM.symm).le)
  obtain ⟨a,ha⟩ := hneM
  have hneN : (N\M).Nonempty := by
    rw [← Finset.card_pos,← Finset.card_sdiff_comm (hcardM.trans hcardN.symm)]
    exact Finset.card_pos.mpr ⟨a,ha⟩
  obtain ⟨b,hb⟩ := hneN
  have haM := (Finset.mem_sdiff.mp ha).1
  have haN := (Finset.mem_sdiff.mp ha).2
  have hbN := (Finset.mem_sdiff.mp hb).1
  have hbM := (Finset.mem_sdiff.mp hb).2
  have hab : a≠b := fun he => hbM (he ▸ haM)
  have hc : projection c (P a)=projection c (P b) := by
    apply le_antisymm
    · by_contra h
      exact not_lt_of_gt (hM a haM b hbM) (hRs b a (lt_of_not_ge h))
    · by_contra h
      exact not_lt_of_gt (hN b hbN a haN) (hRt a b (lt_of_not_ge h))
  have hsc : c=slope (P a) (P b) := (projection_eq_iff_slope (hP.2.1 a b hab)).mp hc
  have hbelow : belowCount P a b=k-1 := by
    rw [← card_belowSet,belowSet_eq_erase hP.1 hM haM hbM (hP.2.1 a b hab) (hsc ▸ hRs),
      Finset.card_erase_of_mem haM,hcardM]
  have hkpos : 0<k := hcardM ▸ Finset.card_pos.mpr ⟨a,haM⟩
  have hkn : k<n := by
    have he : M⊂Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,by intro h;apply hbM;rw [h];exact Finset.mem_univ _⟩
    simpa only [hcardM,Finset.card_univ,Fintype.card_fin] using Finset.card_lt_card he
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨(a,b),(mem_switchPairs P k _).mpr ⟨hab,hkpos,hkn,hbelow⟩,hsc.symm⟩
  · exact ⟨(b,a),(mem_switchPairs P k _).mpr ⟨hba,hkpos,hkn,by rw [belowCount_symm (hP.2.1 a b (ne_of_gt hba)),hbelow]⟩,
      (slope_symm (P b) (P a)).trans hsc.symm⟩

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

noncomputable def subsetIndex {n : ℕ} (A : Finset (Fin n)) : Fin A.card → Fin n :=
  fun i => (A.orderIsoOfFin rfl i : Fin n)

lemma subsetIndex_strictMono {n : ℕ} (A : Finset (Fin n)) : StrictMono (subsetIndex A) :=
  fun _ _ h => (A.orderIsoOfFin rfl).strictMono h

lemma subsetIndex_mem {n : ℕ} (A : Finset (Fin n)) (i : Fin A.card) : subsetIndex A i∈A :=
  (A.orderIsoOfFin rfl i).property

lemma subsetIndex_surj {n : ℕ} (A : Finset (Fin n)) {x : Fin n} (hx : x∈A) :
    ∃ i, subsetIndex A i=x := by
  exact ⟨(A.orderIsoOfFin rfl).symm ⟨x,hx⟩,congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩)⟩

noncomputable def subsetPoints {n : ℕ} (P : Fin n → Point) (A : Finset (Fin n)) : Fin A.card → Point :=
  P∘subsetIndex A

lemma subsetPoints_generic {n : ℕ} {P : Fin n → Point} (hP : Generic P) (A : Finset (Fin n)) :
    Generic (subsetPoints P A) := hP.comp_strictMono (subsetIndex_strictMono A)

noncomputable def restrictMarks {n : ℕ} (A M : Finset (Fin n)) : Finset (Fin A.card) :=
  Finset.univ.filter (fun i => subsetIndex A i∈M)

lemma mem_restrictMarks {n : ℕ} (A M : Finset (Fin n)) (i : Fin A.card) :
    i∈restrictMarks A M ↔ subsetIndex A i∈M := by
  classical
  simp only [restrictMarks,Finset.mem_filter,Finset.mem_univ,true_and]

lemma card_restrictMarks {n : ℕ} (A M : Finset (Fin n)) :
    (restrictMarks A M).card=(M∩A).card := by
  classical
  have he : (restrictMarks A M).image (subsetIndex A)=M∩A := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨(mem_restrictMarks A M i).mp hi,subsetIndex_mem A i⟩
    · intro hx
      obtain ⟨i,rfl⟩ := subsetIndex_surj A (Finset.mem_inter.mp hx).2
      exact Finset.mem_image.mpr ⟨i,(mem_restrictMarks A M i).mpr (Finset.mem_inter.mp hx).1,rfl⟩
  rw [← he,Finset.card_image_of_injective _ (subsetIndex_strictMono A).injective]

lemma restrictMarks_separates {n : ℕ} {P : Fin n → Point} {s : ℝ} {M : Finset (Fin n)}
    (hM : Separates P s M) (A : Finset (Fin n)) :
    Separates (subsetPoints P A) s (restrictMarks A M) := by
  intro i hi j hj
  exact hM _ ((mem_restrictMarks A M i).mp hi) _ (fun h => hj ((mem_restrictMarks A M j).mpr h))

lemma Refines.subset {n : ℕ} {P : Fin n → Point} {c s : ℝ} (hR : Refines P c s)
    (A : Finset (Fin n)) : Refines (subsetPoints P A) c s := fun _ _ h => hR _ _ h

variable {n T k : ℕ} {P : Fin n → Point}

lemma States.restrict_activity_card (S : @States n T k P)
    {u v : Fin (T+1)} (huv : u ≤ v) {i : Fin (T+1)} (hui : u ≤ i) (hiv : i ≤ v) :
    (restrictMarks (S.intervalActivity u v huv) (S.marks i)).card=
      ((S.marks u)∩S.intervalActivity u v huv).card := by
  classical
  let A := S.intervalActivity u v huv
  have he : S.marks i\A=S.marks u\A := by
    ext x
    simp only [Finset.mem_sdiff]
    by_cases hx : x∈A
    · simp [hx]
    · rw [S.outside_activity_constant huv hx hui hiv]
  have h1 := Finset.card_inter_add_card_sdiff (S.marks i) A
  have h2 := Finset.card_inter_add_card_sdiff (S.marks u) A
  rw [S.card_marks] at h1 h2
  rw [he] at h1
  rw [card_restrictMarks]
  change (S.marks i∩A).card=(S.marks u∩A).card
  omega

lemma States.restrict_activity_change (S : @States n T k P)
    {u v : Fin (T+1)} (huv : u ≤ v) {i j : Fin (T+1)}
    (hui : u ≤ i) (hiv : i ≤ v) (huj : u ≤ j) (hjv : j ≤ v)
    (hne : S.marks i≠S.marks j) :
    restrictMarks (S.intervalActivity u v huv) (S.marks i)≠
      restrictMarks (S.intervalActivity u v huv) (S.marks j) := by
  classical
  intro he
  apply hne
  ext x
  by_cases hx : x∈S.intervalActivity u v huv
  · obtain ⟨a,rfl⟩ := subsetIndex_surj _ hx
    exact (mem_restrictMarks _ _ a).symm.trans ((congrArg (fun M => a∈M) he).to_iff.trans (mem_restrictMarks _ _ a))
  · exact (S.outside_activity_constant huv hx hui hiv).trans (S.outside_activity_constant huv hx huj hjv).symm

noncomputable def States.blockSteps (S : @States n T k P) (u v : Fin (T+1)) : Finset (Fin T) :=
  S.changeSteps.filter (fun i => u ≤ i.castSucc ∧ i.succ ≤ v)

lemma States.mem_blockSteps (S : @States n T k P) (u v : Fin (T+1)) (i : Fin T) :
    i∈S.blockSteps u v ↔ i∈S.changeSteps ∧ u ≤ i.castSucc ∧ i.succ ≤ v := by
  classical
  simp only [States.blockSteps,Finset.mem_filter]

lemma card_le_of_injective_labels {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → γ) (g : β → γ)
    (hf : Set.InjOn f A) (hex : ∀ a∈A, ∃ b∈B, g b=f a) : A.card≤B.card := by
  classical
  choose h hh he using (fun a : ↥A => hex a a.property)
  let F : ↥A → ↥B := fun a => ⟨h a,hh a⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hh' : h a=h b := congrArg Subtype.val hab
    exact Subtype.ext (hf a.property b.property ((he a).symm.trans ((congrArg g hh').trans (he b))))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF

lemma block_step_event {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    {u v : Fin ((traversal (criticalSlopes P)).size+1)} (huv : u ≤ v)
    {i : Fin (traversal (criticalSlopes P)).size} (hi : i∈(states P hP hk).blockSteps u v) :
    let A := (states P hP hk).intervalActivity u v huv
    let r := ((states P hP hk).marks u∩A).card
    ∃ p∈switchPairs (subsetPoints P A) r,
      slope (subsetPoints P A p.1) (subsetPoints P A p.2)=(traversal (criticalSlopes P)).cut i.succ.castSucc := by
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  let A := S.intervalActivity u v huv
  have hi' := (S.mem_blockSteps u v i).mp hi
  have hs := T.sample_refines hP i
  exact local_change_event (subsetPoints_generic hP A)
    (restrictMarks_separates (S.separates i.castSucc) A)
    (restrictMarks_separates (S.separates i.succ) A)
    (S.restrict_activity_card huv hi'.2.1 ((Fin.castSucc_le_succ _).trans hi'.2.2))
    (S.restrict_activity_card huv (hi'.2.1.trans (Fin.castSucc_le_succ _)) hi'.2.2)
    (hs.1.subset A) (hs.2.subset A)
    (S.restrict_activity_change huv hi'.2.1 ((Fin.castSucc_le_succ _).trans hi'.2.2)
      (hi'.2.1.trans (Fin.castSucc_le_succ _)) hi'.2.2 ((S.mem_changeSteps _).mp hi'.1))

lemma block_count_le {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    {u v : Fin ((traversal (criticalSlopes P)).size+1)} (huv : u ≤ v) :
    ∃ r : ℕ, r≤((states P hP hk).intervalActivity u v huv).card ∧
      ((states P hP hk).blockSteps u v).card≤
        switchCount (subsetPoints P ((states P hP hk).intervalActivity u v huv)) r := by
  classical
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  let A := S.intervalActivity u v huv
  let r := (S.marks u∩A).card
  refine ⟨r,(Finset.card_le_card (Finset.inter_subset_right)),?_⟩
  change (S.blockSteps u v).card≤(switchPairs (subsetPoints P A) r).card
  apply card_le_of_injective_labels _ _ (fun i => T.cut i.succ.castSucc)
    (fun p => slope (subsetPoints P A p.1) (subsetPoints P A p.2))
  · intro i _ j _ he
    exact Fin.succ_inj.mp (Fin.castSucc_inj.mp (T.increasing.injective he))
  · exact fun i hi => block_step_event hP hk huv hi

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.blockSteps_self (S : @States n T k P) (u : Fin (T+1)) : S.blockSteps u u=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h := (S.mem_blockSteps u u i).mp hi
  exact not_lt_of_ge (h.2.2.trans h.2.1) (Fin.castSucc_lt_succ (i:=i))

lemma States.blockSteps_all (S : @States n T k P) : S.blockSteps 0 (Fin.last T)=S.changeSteps := by
  classical
  ext i
  simp only [S.mem_blockSteps,Fin.zero_le,Fin.le_last,and_true]

lemma States.blockSteps_card_add (S : @States n T k P) {u v w : Fin (T+1)}
    (huv : u ≤ v) (hvw : v ≤ w) :
    (S.blockSteps u v).card+(S.blockSteps v w).card=(S.blockSteps u w).card := by
  classical
  have hdis : Disjoint (S.blockSteps u v) (S.blockSteps v w) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := (S.mem_blockSteps u v i).mp hi
    have hj' := (S.mem_blockSteps v w i).mp hj
    exact not_lt_of_ge (hi'.2.2.trans hj'.2.1) (Fin.castSucc_lt_succ (i:=i))
  have he : S.blockSteps u v ∪ S.blockSteps v w=S.blockSteps u w := by
    ext i
    simp only [Finset.mem_union,S.mem_blockSteps]
    constructor
    · rintro (⟨hi,hu,hv⟩ | ⟨hi,hv,hw⟩)
      · exact ⟨hi,hu,hv.trans hvw⟩
      · exact ⟨hi,huv.trans hv,hw⟩
    · rintro ⟨hi,hu,hw⟩
      by_cases h : i.succ ≤ v
      · exact Or.inl ⟨hi,hu,h⟩
      · exact Or.inr ⟨hi,(by change v.val ≤ i.val;change ¬i.val+1 ≤ v.val at h;omega),hw⟩
  rw [← he,Finset.card_union_of_disjoint hdis]

lemma States.sum_blockSteps (S : @States n T k P) (m : ℕ)
    (f : Fin (m+1) → Fin (T+1)) (hf : Monotone f) :
    ∑ j : Fin m, (S.blockSteps (f j.castSucc) (f j.succ)).card=
      (S.blockSteps (f 0) (f (Fin.last m))).card := by
  induction m with
  | zero => simp [S.blockSteps_self]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hh := ih (fun j : Fin (m+1) => f j.castSucc) (fun _ _ h => hf (Fin.castSucc_le_castSucc_iff.mpr h))
    simp only [Fin.castSucc_succ] at hh
    rw [hh]
    exact S.blockSteps_card_add (hf (Fin.zero_le _)) (hf (Fin.castSucc_le_succ _))

noncomputable def States.ActivityGreedy.fullIndex (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : Fin (G.count+2) → Fin (T+1) :=
  Fin.snoc G.index (Fin.last T)

lemma States.ActivityGreedy.fullIndex_mono (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : Monotone (G.fullIndex S) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro _
    simpa only [States.ActivityGreedy.fullIndex,Fin.snoc_last] using (Fin.le_last (G.fullIndex S i))
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      exact False.elim (not_le_of_gt (Fin.castSucc_lt_last j) hij)
    · intro hij
      simpa only [States.ActivityGreedy.fullIndex,Fin.snoc_castSucc] using G.increasing.monotone (Fin.castSucc_le_castSucc_iff.mp hij)

lemma States.ActivityGreedy.fullIndex_first (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : G.fullIndex S 0=s := by
  simpa only [States.ActivityGreedy.fullIndex,←Fin.castSucc_zero,Fin.snoc_castSucc] using G.first

lemma States.ActivityGreedy.fullIndex_last (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : G.fullIndex S (Fin.last (G.count+1))=Fin.last T := Fin.snoc_last _ _

lemma States.ActivityGreedy.fullIndex_activity (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) (j : Fin (G.count+1)) :
    S.activitySize (G.fullIndex S j.castSucc) (G.fullIndex S j.succ)≤b+1 := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [States.ActivityGreedy.fullIndex,Fin.snoc_castSucc,Fin.succ_last,Fin.snoc_last] using G.tail.le.trans (Nat.le_succ b)
  · simpa only [States.ActivityGreedy.fullIndex,←Fin.castSucc_succ,Fin.snoc_castSucc] using G.upper i

lemma activity_decomposition {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    {b : ℕ} (hb : 0<b) :
    ∃ (A : Fin (((states P hP hk).activityGreedy 0 b hb).count+1) → Finset (Fin n))
      (r : Fin (((states P hP hk).activityGreedy 0 b hb).count+1) → ℕ),
      (∀ j, (A j).card≤b+1) ∧ (∀ j, r j≤(A j).card) ∧
      switchCount P k ≤ ∑ j, switchCount (subsetPoints P (A j)) (r j) := by
  classical
  let S := states P hP hk
  let G := S.activityGreedy 0 b hb
  let f := G.fullIndex S
  have hf : Monotone f := G.fullIndex_mono S
  let A (j : Fin (G.count+1)) := S.intervalActivity (f j.castSucc) (f j.succ) (hf (Fin.castSucc_le_succ j))
  have hex (j : Fin (G.count+1)) : ∃ r : ℕ, r≤(A j).card ∧
      (S.blockSteps (f j.castSucc) (f j.succ)).card ≤ switchCount (subsetPoints P (A j)) r :=
    block_count_le hP hk (hf (Fin.castSucc_le_succ j))
  choose r hr hcount using hex
  refine ⟨A,r,?_,hr,?_⟩
  · intro j
    rw [← S.activitySize_eq]
    exact G.fullIndex_activity S j
  · have hsum := S.sum_blockSteps (G.count+1) f hf
    dsimp only [f] at hsum
    rw [G.fullIndex_first S,G.fullIndex_last S,S.blockSteps_all] at hsum
    calc
      switchCount P k ≤ S.changeSteps.card := switchCount_le_changes hP hk
      _ = ∑ j : Fin (G.count+1), (S.blockSteps (f j.castSucc) (f j.succ)).card := hsum.symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hcount j)

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep

lemma division_scale {n q : ℕ} (hq : 4≤q) (hn : 4*q≤n) :
    let b := n/q-1
    0<b ∧ b+1=n/q ∧ (b+1:ℝ)≤(n:ℝ)/q ∧ n≤2*q*b ∧ (b+1)<n := by
  have hq0 : 0<q := by omega
  have hd : 4≤n/q := (Nat.le_div_iff_mul_le hq0).mpr hn
  have hbd : n/q-1+1=n/q := by omega
  refine ⟨by omega,hbd,?_,?_,?_⟩
  · have he : ((n/q-1:ℕ):ℝ)+1=(n/q:ℕ) := by exact_mod_cast hbd
    rw [he]
    exact (le_div_iff₀ (by exact_mod_cast hq0)).mpr (by exact_mod_cast Nat.div_mul_le_self n q)
  · have he := Nat.mod_add_div n q
    have hm := Nat.mod_lt n hq0
    nlinarith
  · rw [hbd]
    exact Nat.div_lt_self (by omega) (by omega)

lemma greedy_count_bound {q : ℕ} (hq : 4≤q) {m n b : ℕ} (hb : 0<b)
    (hn : n≤2*q*b) (hp : (m:ℝ)^3*(b:ℝ)^4≤(n:ℝ)^4/1024) :
    (m:ℝ)+1≤(q:ℝ)^((4:ℝ)/3)/2 := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hnr : (n:ℝ)≤2*(q:ℝ)*b := by exact_mod_cast hn
  have hpow : ((q:ℝ)^((4:ℝ)/3))^3=(q:ℝ)^4 := by
    rw [←Real.rpow_mul_natCast hq0.le]
    norm_num
  have hm : (m:ℝ)≤(q:ℝ)^((4:ℝ)/3)/4 := by
    apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ)≠0) (by positivity)
    have hn4 := pow_le_pow_left₀ (show (0:ℝ)≤n by positivity) hnr 4
    have ht : (m:ℝ)^3*(b:ℝ)^4≤((q:ℝ)^((4:ℝ)/3)/4)^3*(b:ℝ)^4 := by
      rw [div_pow,hpow]
      nlinarith
    exact (mul_le_mul_iff_left₀ (pow_pos hbr 4)).mp ht
  have hqpow : (4:ℝ)≤(q:ℝ)^((4:ℝ)/3) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤q by exact_mod_cast (show 1≤q by omega)) (by norm_num : (1:ℝ)≤4/3)
    rw [Real.rpow_one] at h1
    exact (show (4:ℝ)≤q by exact_mod_cast hq).trans h1
  linarith

lemma recurrence_exponent {q : ℕ} (hq : 4≤q) :
    ∃ ε : ℝ, 0<ε ∧ 0<(4:ℝ)/3-ε ∧
      (q:ℝ)^((4:ℝ)/3)/2≤(q:ℝ)^((4:ℝ)/3-ε) := by
  have hq2 : (2:ℝ)≤q := by exact_mod_cast (show 2≤q by omega)
  have hq0 : (0:ℝ)<q := lt_of_lt_of_le (by norm_num) hq2
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlq : 0<Real.log (q:ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log 2≤Real.log (q:ℝ) := Real.log_le_log (by norm_num) hq2
  let ε : ℝ := Real.log 2/(2*Real.log (q:ℝ))
  have he : 0<ε := div_pos hl2 (by positivity)
  have hehalf : ε≤1/2 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0<2*Real.log (q:ℝ))).mpr
    nlinarith
  refine ⟨ε,he,by linarith,?_⟩
  rw [Real.rpow_sub hq0]
  apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hq0 ε)
  rw [Real.rpow_def_of_pos hq0]
  calc
    Real.exp (Real.log (q:ℝ)*ε) ≤ Real.exp (Real.log 2) := by
      apply Real.exp_le_exp.mpr
      dsimp [ε]
      have hl0 := ne_of_gt hlq
      field_simp
      nlinarith
    _ = 2 := Real.exp_log (by norm_num)

end PlanarHalving.Sweep

end OAI
