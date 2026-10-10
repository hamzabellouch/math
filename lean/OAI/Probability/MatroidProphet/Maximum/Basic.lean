import OAI.Probability.MatroidProphet.Rounding
import OAI.Probability.MatroidProphet.Candidates

namespace OAI

namespace MatroidProphet
namespace Maximum

open MeasureTheory Finset Set

variable {n bits : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K]

noncomputable def firstRule (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop) : OnlineRule n bits := by
  classical
  exact discreteOnlineRule key hkey (fun k r s hist => decide
    (allowed r s (hist ⟨k.val, Nat.lt_succ_self _⟩) ∧
      ∀ j : Fin (k.val + 1), j.val < k.val → ¬ allowed r s (hist j)))

lemma firstRule_decision (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) :
    decisionAt (firstRule key hkey allowed) r s v π k = true ↔
      allowed r (fun e => key (s e)) (π k, key (v (π k))) ∧
      ∀ i : Fin n, i.val < k.val →
        ¬ allowed r (fun e => key (s e)) (π i, key (v (π i))) := by
  classical
  change decide (allowed r (fun e => key (s e)) (π k, key (v (π k))) ∧
    ∀ j : Fin (k.val + 1), j.val < k.val →
      ¬ allowed r (fun e => key (s e))
        (π (prefixIndex k j), key (v (π (prefixIndex k j))))) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨hc, fun i hi => ?_⟩
    exact hp ⟨i.val, by omega⟩ hi
  · rintro ⟨hc, hp⟩
    exact ⟨hc, fun j hj => hp (prefixIndex k j) hj⟩

lemma firstRule_unique (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ)
    {e f : Fin n}
    (he : e ∈ acceptedThrough (firstRule key hkey allowed) r s v π t)
    (hf : f ∈ acceptedThrough (firstRule key hkey allowed) r s v π t) : e = f := by
  have he' := (firstRule_decision key hkey allowed r s v π (π.symm e)).1
    ((Finset.mem_filter.mp he).2).2
  have hf' := (firstRule_decision key hkey allowed r s v π (π.symm f)).1
    ((Finset.mem_filter.mp hf).2).2
  rcases lt_trichotomy (π.symm e).val (π.symm f).val with hlt | heq | hgt
  · exact False.elim (hf'.2 (π.symm e) hlt he'.1)
  · exact π.symm.injective (Fin.ext heq)
  · exact False.elim (he'.2 (π.symm f) hgt hf'.1)

lemma firstRule_feasible (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (ha : ∀ r s x, allowed r s x → M.Indep ({x.1} : Set (Fin n))) :
    Feasible M (firstRule key hkey allowed) := by
  intro r s v π t _ _
  classical
  by_cases h : (acceptedThrough (firstRule key hkey allowed) r s v π t).Nonempty
  · obtain ⟨e, he⟩ := h
    have ha' := (firstRule_decision key hkey allowed r s v π (π.symm e)).1
      ((Finset.mem_filter.mp he).2).2
    have hi : M.Indep ({e} : Set (Fin n)) := by
      simpa only [Equiv.apply_symm_apply] using ha r (fun f => key (s f)) _ ha'.1
    apply hi.subset
    intro f hf
    exact Set.mem_singleton_iff.mpr (firstRule_unique key hkey allowed r s v π t hf he)
  · have he : acceptedThrough (firstRule key hkey allowed) r s v π t = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

lemma firstRule_single_qualifier (key : ℝ → K) (hkey : Measurable key)
    (allowed : Seed bits → (Fin n → K) → (Fin n × K) → Prop)
    (r : Seed bits) (s v : Weights n) (g : Fin n)
    (ha : ∀ e, allowed r (fun f => key (s f)) (e, key (v e)) ↔ e = g)
    (π : ArrivalOrder n) : accepted (firstRule key hkey allowed) r s v π = {g} := by
  classical
  ext e
  simp only [accepted, acceptedThrough, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨_, hd⟩
    have hc := ((firstRule_decision key hkey allowed r s v π (π.symm e)).1 hd).1
    exact (ha e).1 (by simpa using hc)
  · intro heg
    subst e
    refine ⟨(π.symm g).isLt, (firstRule_decision key hkey allowed r s v π (π.symm g)).2 ?_⟩
    constructor
    · simpa using (ha g).2 rfl
    · intro i hi hallowed
      have heq : π i = g := (ha (π i)).1 hallowed
      have hieq : i = π.symm g := by simpa using congrArg π.symm heq
      exact Nat.lt_irrefl _ (hieq ▸ hi)

def higher [LinearOrder K] (x y : Fin n × K) : Prop :=
  y.2 < x.2 ∨ (x.2 = y.2 ∧ x.1 < y.1)

def threshold [LinearOrder K] (M : Matroid (Fin n)) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (r : Seed bits) (s : Fin n → K)
    (x : Fin n × K) : Prop :=
  x.1 ∉ mask r ∧ M.Indep ({x.1} : Set (Fin n)) ∧ active x.2 ∧
    ∀ f ∈ mask r, M.Indep ({f} : Set (Fin n)) → active (s f) → higher x (f, s f)

noncomputable def maximumRule [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : OnlineRule n bits :=
  firstRule key hkey (threshold M active mask)

lemma maximumRule_feasible [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : Feasible M (maximumRule M key hkey active mask) :=
  firstRule_feasible M key hkey _ (fun _ _ _ hx => hx.2.1)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_irrefl [LinearOrder K] (x : Fin n × K) : ¬ higher x x := by
  simp [higher]

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_trans [LinearOrder K] {x y z : Fin n × K}
    (hxy : higher x y) (hyz : higher y z) : higher x z := by
  rcases hxy with hxy | ⟨hxy, hxy'⟩ <;> rcases hyz with hyz | ⟨hyz, hyz'⟩
  · exact Or.inl (hyz.trans hxy)
  · exact Or.inl (hyz ▸ hxy)
  · exact Or.inl (hxy ▸ hyz)
  · exact Or.inr ⟨hxy.trans hyz, hxy'.trans hyz'⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma higher_total [LinearOrder K] {x y : Fin n × K} (h : x ≠ y) :
    higher x y ∨ higher y x := by
  rcases lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · have hn : x.1 ≠ y.1 := fun hxy => h (Prod.ext hxy heq)
    rcases lt_or_gt_of_ne hn with hxy | hyx
    · exact Or.inl (Or.inr ⟨heq, hxy⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hyx⟩)
  · exact Or.inl (Or.inl hgt)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in

lemma threshold_top_two [LinearOrder K] (M : Matroid (Fin n))
    (active : K → Prop) (mask : Seed bits → Finset (Fin n))
    (r : Seed bits) (a : Fin n → K) (g h : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (a g))
    (hh : M.Indep ({h} : Set (Fin n))) (hah : active (a h))
    (htop : ∀ f, M.Indep ({f} : Set (Fin n)) → active (a f) → f ≠ g →
      higher (g, a g) (f, a f))
    (hsecond : ∀ f, M.Indep ({f} : Set (Fin n)) → active (a f) → f ≠ g → f ≠ h →
      higher (h, a h) (f, a f))
    (hgm : g ∉ mask r) (hhm : h ∈ mask r) :
    ∀ e, threshold M active mask r a (e, a e) ↔ e = g := by
  intro e
  constructor
  · intro he
    by_contra heg
    have heh : e ≠ h := fun heq => he.1 (heq ▸ hhm)
    have heh' := he.2.2.2 h hhm hh hah
    exact higher_irrefl _ (higher_trans heh' (hsecond e he.2.1 he.2.2.1 heg heh))
  · rintro rfl
    refine ⟨hgm, hg, hag, ?_⟩
    intro f hfm hf haf
    exact htop f hf haf (fun hfg => hgm (hfg ▸ hfm))

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma threshold_congr_samples [LinearOrder K] (M : Matroid (Fin n))
    (active : K → Prop) (mask : Seed bits → Finset (Fin n)) (r : Seed bits)
    (s t : Fin n → K) (hst : ∀ f ∈ mask r, s f = t f) (x : Fin n × K) :
    threshold M active mask r s x ↔ threshold M active mask r t x := by
  unfold threshold
  constructor <;> rintro ⟨hm, hi, ha, h⟩ <;> refine ⟨hm, hi, ha, ?_⟩
  · intro f hf hfi hfa
    simpa only [hst f hf] using h f hf hfi (by simpa only [hst f hf] using hfa)
  · intro f hf hfi hfa
    simpa only [hst f hf] using h f hf hfi (by simpa only [hst f hf] using hfa)

noncomputable def maximumHidden [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) : HiddenRule n bits :=
  ⟨mask, maximumRule M key hkey active mask⟩

lemma maximumHidden_feasible [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (r : Seed bits) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (maximumHidden M key hkey active mask) r w π t :
      Set (Fin n)) := by
  apply (maximumRule_feasible M key hkey active mask r
    (observed (maximumHidden M key hkey active mask) r w) w π t ?_ hw).subset
  · intro e he
    exact (Finset.mem_sdiff.mp he).1
  · intro e
    classical
    simp only [observed]
    split_ifs
    · exact hw e
    · exact le_rfl

lemma maximumHidden_single_qualifier [LinearOrder K] (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (r : Seed bits) (g : Fin n)
    (hg : g ∉ mask r)
    (ha : ∀ e, threshold M active mask r (fun f => key (w f)) (e, key (w e)) ↔ e = g)
    (π : ArrivalOrder n) :
    hiddenReward (maximumHidden M key hkey active mask) r w π = w g := by
  classical
  let A := maximumHidden M key hkey active mask
  have hsingle : accepted A.core r (observed A r w) w π = {g} := by
    apply firstRule_single_qualifier key hkey (threshold M active mask)
    intro e
    rw [threshold_congr_samples M active mask r
      (fun f => key (observed A r w f)) (fun f => key (w f))]
    · exact ha e
    · intro f hf
      simp [observed, A, maximumHidden, hf]
  change (∑ e ∈ accepted A.core r (observed A r w) w π \ mask r, w e) = w g
  rw [hsingle]
  have hd : ({g} : Finset (Fin n)) \ mask r = {g} := by
    apply Finset.sdiff_eq_self_of_disjoint
    simpa only [Finset.disjoint_singleton_left] using hg
  rw [hd, Finset.sum_singleton]

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma exists_top [LinearOrder K] (a : Fin n → K) (V : Finset (Fin n)) (hV : V.Nonempty) :
    ∃ g ∈ V, ∀ f ∈ V, f ≠ g → higher (g, a g) (f, a f) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp at hV
  | @insert e V he ih =>
    by_cases hn : V.Nonempty
    · obtain ⟨g, hg, htop⟩ := ih hn
      have heg : e ≠ g := fun heq => he (heq ▸ hg)
      by_cases heg' : higher (e, a e) (g, a g)
      · refine ⟨e, Finset.mem_insert_self _ _, ?_⟩
        intro f hf hfe
        have hfV : f ∈ V := (Finset.mem_insert.mp hf).resolve_left hfe
        by_cases hfg : f = g
        · simpa [hfg] using heg'
        · exact higher_trans heg' (htop f hfV hfg)
      · refine ⟨g, Finset.mem_insert_of_mem hg, ?_⟩
        intro f hf hfg
        rcases Finset.mem_insert.mp hf with hfe | hfV
        · subst f
          exact (higher_total (show (e, a e) ≠ (g, a g) from
            fun h => heg (congrArg Prod.fst h))).resolve_left heg'
        · exact htop f hfV hfg
    · have hv : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst V
      exact ⟨e, by simp, by simp⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] in
lemma threshold_only_positive [LinearOrder K] (M : Matroid (Fin n))
    (active : K → Prop) (mask : Seed bits → Finset (Fin n))
    (r : Seed bits) (a : Fin n → K) (g : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (a g))
    (honly : ∀ f, M.Indep ({f} : Set (Fin n)) → active (a f) → f = g)
    (hgm : g ∉ mask r) :
    ∀ e, threshold M active mask r a (e, a e) ↔ e = g := by
  intro e
  constructor
  · intro he
    exact honly e he.2.1 he.2.2.1
  · intro heq
    subst e
    refine ⟨hgm, hg, hag, ?_⟩
    intro f hfm hf haf
    exact False.elim (hgm (honly f hf haf ▸ hfm))

end Maximum
end MatroidProphet

end OAI
