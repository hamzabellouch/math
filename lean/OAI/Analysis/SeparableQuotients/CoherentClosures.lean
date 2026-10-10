import OAI.Analysis.SeparableQuotients.EvaluationCriterion

namespace OAI

namespace SeparableQuotient.CoherentClosures

open Set
universe u
variable {Γ : Type u} [LinearOrder Γ]

/-- Finite closures on the strict initial segment at β. -/
abbrev PreSystem (β : Γ) := Set.Iio β → ℕ → Finset Γ

/-- Coherence conditions below β. -/
structure PreGood (β : Γ) (G : PreSystem β) : Prop where
  lower : ∀ (a : Set.Iio β) n, ∀ x ∈ G a n, x ≤ a.val
  self : ∀ (a : Set.Iio β) n, a.val ∈ G a n
  mono : ∀ a : Set.Iio β, Monotone (G a)
  exhaust : ∀ (a : Set.Iio β) x, x ≤ a.val → ∃ n, x ∈ G a n
  coherent : ∀ (a b : Set.Iio β) n, b.val ∈ G a n →
    G b n = (G a n).filter (fun x => x ≤ b.val)

/-- The closure conditions at a new endpoint, relative to earlier closures. -/
structure ExtensionGood (β : Γ) (G : PreSystem β) (H : ℕ → Finset Γ) : Prop where
  lower : ∀ n, ∀ x ∈ H n, x ≤ β
  self : ∀ n, β ∈ H n
  mono : Monotone H
  exhaust : ∀ x, x ≤ β → ∃ n, x ∈ H n
  coherent : ∀ (a : Set.Iio β) n, a.val ∈ H n →
    G a n = (H n).filter (fun x => x ≤ a.val)

/-- A threshold beyond which two specified earlier coordinates are recorded. -/
lemma exists_next_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (a b : Set.Iio β) (p : ℕ) :
    ∃ q > p, a.val ∈ G (max a b) q ∧ b.val ∈ G (max a b) q := by
  obtain ⟨i, hi⟩ := hg.exhaust (max a b) a.val (le_max_left _ _)
  obtain ⟨j, hj⟩ := hg.exhaust (max a b) b.val (le_max_right _ _)
  refine ⟨max (max i j) (p + 1), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self p) (le_max_right _ _)
  · exact hg.mono (max a b) (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  · exact hg.mono (max a b) (le_trans (le_max_right _ _) (le_max_left _ _)) hj

/-- Each stage of the endpoint construction keeps one earlier endpoint and an
activation threshold. The next endpoint is the maximum of the old endpoint
and the next enumerated predecessor. -/
noncomputable def stage {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : ℕ → Set.Iio β × ℕ
  | 0 => (e 0, 0)
  | n+1 => let v := stage hg e n
    (max v.1 (e (n+1)), (exists_next_threshold hg v.1 (e (n+1)) v.2).choose)

lemma stage_zero {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : stage hg e 0 = (e 0, 0) := rfl

lemma stage_succ_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) :
    (stage hg e n).2 < (stage hg e (n+1)).2 ∧
    (stage hg e n).1.val ∈ G (stage hg e (n+1)).1 (stage hg e (n+1)).2 ∧
    (e (n+1)).val ∈ G (stage hg e (n+1)).1 (stage hg e (n+1)).2 := by
  exact (exists_next_threshold hg (stage hg e n).1 (e (n+1))
    (stage hg e n).2).choose_spec

lemma stage_threshold_strictMono {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : StrictMono (fun n => (stage hg e n).2) :=
  strictMono_nat_of_lt_succ fun n => (stage_succ_threshold hg e n).1

lemma stage_threshold_ge {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) : n ≤ (stage hg e n).2 :=
  (stage_threshold_strictMono hg e).id_le n

/-- The last activated stage at parameter p. -/
noncomputable def active {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : ℕ :=
  Nat.findGreatest (fun n => (stage hg e n).2 ≤ p) p

lemma active_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : (stage hg e (active hg e p)).2 ≤ p := by
  exact Nat.findGreatest_spec (P := fun n => (stage hg e n).2 ≤ p)
    (Nat.zero_le p) (show (stage hg e 0).2 ≤ p from Nat.zero_le p)

lemma stage_le_active {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) {n p : ℕ} (h : (stage hg e n).2 ≤ p) :
    n ≤ active hg e p :=
  Nat.le_findGreatest (le_trans (stage_threshold_ge hg e n) h) h

lemma active_mono {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : Monotone (active hg e) := by
  intro p q hpq
  exact stage_le_active hg e (le_trans (active_threshold hg e p) hpq)

lemma active_at_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) : active hg e (stage hg e n).2 = n := by
  apply le_antisymm
  · exact (stage_threshold_strictMono hg e).le_iff_le.mp (active_threshold hg e _)
  · exact stage_le_active hg e le_rfl

/-- Earlier stage closures embed in later ones once the later stage is active. -/
lemma stage_subset_succ {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n p : ℕ) (hp : (stage hg e (n+1)).2 ≤ p) :
    G (stage hg e n).1 p ⊆ G (stage hg e (n+1)).1 p := by
  have hm := hg.mono (stage hg e (n+1)).1 hp (stage_succ_threshold hg e n).2.1
  rw [hg.coherent (stage hg e (n+1)).1 (stage hg e n).1 p hm]
  exact Finset.filter_subset _ _

lemma stage_subset {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) {n m p : ℕ} (hnm : n ≤ m)
    (hp : (stage hg e m).2 ≤ p) : G (stage hg e n).1 p ⊆ G (stage hg e m).1 p := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    apply Finset.Subset.trans (ih ((stage_threshold_strictMono hg e).monotone
      (Nat.le_succ m) |>.trans hp))
    exact stage_subset_succ hg e m p hp

/-- The new closure: keep the activated earlier closure and append β. -/
noncomputable def extended {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : Finset Γ :=
  insert β (G (stage hg e (active hg e p)).1 p)

lemma extended_good {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (he : Function.Surjective e) :
    ExtensionGood β G (extended hg e) := by
  classical
  constructor
  · intro n x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hg.lower _ _ _ hx).trans (stage hg e (active hg e n)).1.property.le
  · intro n
    exact Finset.mem_insert_self _ _
  · intro p q hpq
    apply Finset.insert_subset_insert
    exact (hg.mono _ hpq).trans
      (stage_subset hg e (active_mono hg e hpq) (active_threshold hg e q))
  · intro x hx
    rcases lt_or_eq_of_le hx with hx | rfl
    · obtain ⟨i, hi⟩ := he ⟨x, hx⟩
      refine ⟨(stage hg e i).2, Finset.mem_insert_of_mem ?_⟩
      rw [active_at_threshold]
      cases i with
      | zero => simpa [stage_zero, hi] using hg.self (e 0) 0
      | succ i => simpa only [hi] using (stage_succ_threshold hg e i).2.2
    · exact ⟨0, Finset.mem_insert_self _ _⟩
  · intro a n ha
    have hab : a.val ≠ β := ne_of_lt a.property
    have ha' := (Finset.mem_insert.mp ha).resolve_left hab
    rw [hg.coherent _ a n ha']
    apply Finset.ext
    intro x
    simp only [extended, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxa⟩; exact ⟨Or.inr hx, hxa⟩
    · rintro ⟨rfl | hx, hxa⟩
      · exact (not_le_of_gt a.property hxa).elim
      · exact ⟨hx, hxa⟩

/-- Empty strict segments require no recursive information. -/
lemma singleton_good {β : Γ} {G : PreSystem β} (h : IsEmpty (Set.Iio β)) :
    ExtensionGood β G (fun _ => {β}) := by
  classical
  constructor
  · intro n x hx; exact (Finset.mem_singleton.mp hx).le
  · intro n; simp
  · intro p q hpq; exact le_rfl
  · intro x hx
    have he : x = β := (lt_or_eq_of_le hx).resolve_left fun hlt => h.false ⟨x, hlt⟩
    subst x; exact ⟨0, by simp⟩
  · intro a; exact h.false a |>.elim

/-- Countability of the strict segment suffices to extend the coherent system. -/
lemma exists_extension {β : Γ} [Countable (Set.Iio β)]
    {G : PreSystem β} (hg : PreGood β G) :
    ∃ H : ℕ → Finset Γ, ExtensionGood β G H := by
  classical
  cases isEmpty_or_nonempty (Set.Iio β) with
  | inl h => exact ⟨fun _ => {β}, singleton_good h⟩
  | inr h =>
    let := h
    obtain ⟨e, he⟩ := exists_surjective_nat (Set.Iio β)
    exact ⟨extended hg e, extended_good hg e he⟩

/-- Full endpoint property for a total system. -/
structure GoodAt (F : Γ → ℕ → Finset Γ) (β : Γ) : Prop where
  lower : ∀ n, ∀ x ∈ F β n, x ≤ β
  self : ∀ n, β ∈ F β n
  mono : Monotone (F β)
  exhaust : ∀ x, x ≤ β → ∃ n, x ∈ F β n
  coherent : ∀ α n, α ∈ F β n → F α n = (F β n).filter (fun x => x ≤ α)

variable [WellFoundedLT Γ] [∀ β : Γ, Countable (Set.Iio β)]

/-- The recursion step is defined even on bad predecessor data; the bad branch
is never used in the well-founded construction. -/
noncomputable def next (β : Γ) (G : PreSystem β) : ℕ → Finset Γ := by
  classical
  exact if h : PreGood β G then (exists_extension h).choose else fun _ => {β}

omit [WellFoundedLT Γ] in
lemma next_good (β : Γ) (G : PreSystem β) (h : PreGood β G) :
    ExtensionGood β G (next β G) := by
  classical
  rw [next, dite_eq_left h]
  exact (exists_extension h).choose_spec

/-- The actual coherently nested finite closures on the well-order. -/
noncomputable def system : Γ → ℕ → Finset Γ :=
  WellFounded.fix wellFounded_lt fun β rec => next β (fun a => rec a.val a.property)

lemma system_eq (β : Γ) : system β = next β (fun a => system a.val) := by
  rw [system, WellFounded.fix_eq]

/-- Transfinite induction establishes the coherent closure properties. -/
theorem system_goodAt (β : Γ) : GoodAt system β := by
  classical
  refine (wellFounded_lt : WellFounded ((· < ·) : Γ → Γ → Prop)).induction β ?_
  intro β ih
  have hg : PreGood β (fun a => system a.val) := by
    constructor
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).lower
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).self
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).mono
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).exhaust
    · intro a b n hb; exact (ih a.val (Set.mem_Iio.mp a.property)).coherent b.val n hb
  have he := next_good β (fun a => system a.val) hg
  rw [← system_eq] at he
  refine ⟨he.lower, he.self, he.mono, he.exhaust, ?_⟩
  intro α n hα
  rcases lt_or_eq_of_le (he.lower n α hα) with hlt | rfl
  · exact he.coherent ⟨α, hlt⟩ n hα
  · exact (Finset.filter_eq_self.mpr fun x hx => he.lower n x hx).symm

/-- Coherent finite closures on a well-order with countable initial segments, indexed from zero. -/
theorem exists_coherent_closures : ∃ F : Γ → ℕ → Finset Γ,
    (∀ β n, β ∈ F β n) ∧
    (∀ β n x, x ∈ F β n → x ≤ β) ∧
    (∀ β, Monotone (F β)) ∧
    (∀ β x, x ≤ β → ∃ n, x ∈ F β n) ∧
    (∀ β α n, α ∈ F β n → F α n = (F β n).filter (fun x => x ≤ α)) := by
  refine ⟨system, ?_, ?_, ?_, ?_, ?_⟩
  · intro β; exact (system_goodAt β).self
  · intro β; exact (system_goodAt β).lower
  · intro β; exact (system_goodAt β).mono
  · intro β; exact (system_goodAt β).exhaust
  · intro β; exact (system_goodAt β).coherent

end SeparableQuotient.CoherentClosures

namespace SeparableQuotient.CoherentClosures

open Set

/-- The coordinate set of the negative construction is really ω₁. -/
abbrev OmegaOne := (Cardinal.aleph 1).ord.ToType

instance omegaOne_initialSegment_countable (β : OmegaOne) : Countable (Set.Iio β) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt β (by simp [OmegaOne])
  simpa [OmegaOne] using h

/-- Positive-indexed finite closures. -/
noncomputable def F (β : OmegaOne) (p : ℕ) : Finset OmegaOne :=
  system β (p - 1)

lemma F_self (β : OmegaOne) (p : ℕ) : β ∈ F β p :=
  (system_goodAt β).self (p - 1)

lemma F_lower (β : OmegaOne) (p : ℕ) (α : OmegaOne) (h : α ∈ F β p) : α ≤ β :=
  (system_goodAt β).lower (p - 1) α h

lemma F_mono (β : OmegaOne) : Monotone (F β) := by
  intro p q hpq
  exact (system_goodAt β).mono (Nat.sub_le_sub_right hpq 1)

lemma F_exhaust (β α : OmegaOne) (h : α ≤ β) : ∃ p ≥ 1, α ∈ F β p := by
  obtain ⟨n, hn⟩ := (system_goodAt β).exhaust α h
  exact ⟨n+1, by omega, by simpa [F] using hn⟩

lemma F_coherent (β α : OmegaOne) (p : ℕ) (h : α ∈ F β p) :
    F α p = (F β p).filter (fun x => x ≤ α) :=
  (system_goodAt β).coherent α (p - 1) h

/-- Two closures containing α have the same ordered initial segment through α. -/
lemma shared_initial_segment (β γ α : OmegaOne) (p : ℕ)
    (hβ : α ∈ F β p) (hγ : α ∈ F γ p) :
    (F β p).filter (fun x => x ≤ α) = (F γ p).filter (fun x => x ≤ α) := by
  rw [← F_coherent β α p hβ, ← F_coherent γ α p hγ]

/-- The first positive parameter at which α enters the closure of β. The
irrelevant case α > β is set to zero. -/
noncomputable def rho (α β : OmegaOne) : ℕ := by
  classical
  exact if h : α ≤ β then Nat.find ((system_goodAt β).exhaust α h) + 1 else 0

lemma rho_pos (α β : OmegaOne) (h : α ≤ β) : 1 ≤ rho α β := by
  classical
  simp only [rho, dite_eq_left h]
  omega

lemma mem_F_rho (α β : OmegaOne) (h : α ≤ β) : α ∈ F β (rho α β) := by
  classical
  simp only [rho, dite_eq_left h, F, Nat.add_sub_cancel]
  exact Nat.find_spec ((system_goodAt β).exhaust α h)

lemma rho_le_iff (α β : OmegaOne) (h : α ≤ β) (p : ℕ) (hp : 1 ≤ p) :
    rho α β ≤ p ↔ α ∈ F β p := by
  classical
  constructor
  · intro hr
    exact F_mono β hr (mem_F_rho α β h)
  · intro ha
    have hn := Nat.find_min' ((system_goodAt β).exhaust α h) ha
    simp only [rho, dite_eq_left h]
    omega

/-- A finite nonempty set is contained in a common closure of its largest
coordinate, with one positive parameter for all its elements. -/
lemma finite_cover {A : Finset OmegaOne} (hA : A.Nonempty) :
    ∃ p ≥ 1, A ⊆ F (A.max' hA) p := by
  classical
  let p := A.sup (fun α => rho α (A.max' hA))
  refine ⟨max 1 p, le_max_left _ _, ?_⟩
  intro α hα
  apply (rho_le_iff α (A.max' hA) (Finset.le_max' _ _ hα) _ (le_max_left _ _)).mp
  exact (Finset.le_sup (f := fun α => rho α (A.max' hA)) hα).trans (le_max_right _ _)

end SeparableQuotient.CoherentClosures

end OAI
