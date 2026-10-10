import OAI.Combinatorics.TreewidthL1.AnchorExperiment

namespace OAI

namespace BoundedTreewidthL1
open Filter

def InfinitesimalAlong {I : Type*} (U : Ultrafilter I) (x : I → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, x i < ε

/-- A reservation interval whose effective start is early and terminal time is
late. Validity is explicit; no anchor is created merely by taking a quotient. -/
def CrossingSequence {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ)
    (δ : I → ℕ → ℝ) (a : I → ℕ) : Prop :=
  (∀ᶠ i in U, valid i (a i)) ∧
  ¬InfinitesimalAlong U (fun i => δ i (start i (a i))) ∧
  InfinitesimalAlong U (fun i => δ i (finish i (a i)))

/-- Crossing anchor sequences identified precisely when they agree eventually. -/
def CrossingGerms {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ) :
    Set (Germ (U : Filter I) ℕ) :=
  {x | ∃ a : I → ℕ, (a : Germ (U : Filter I) ℕ) = x ∧
    CrossingSequence U valid start finish δ a}

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter

lemma noninfinitesimal_iff {I : Type*} (U : Ultrafilter I) (x : I → ℝ) :
    ¬InfinitesimalAlong U x ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ i in U, ε ≤ x i := by
  classical
  simp only [InfinitesimalAlong, not_forall]
  constructor
  · rintro ⟨ε, hε, hn⟩
    refine ⟨ε, hε, ?_⟩
    simpa only [not_lt] using (Ultrafilter.eventually_not.mpr hn)
  · rintro ⟨ε, hε, hx⟩
    refine ⟨ε, hε, ?_⟩
    intro h
    obtain ⟨i, hi, hi'⟩ := (hx.and h).exists
    exact (not_lt_of_ge hi) hi'

lemma early_precedes_late {I : Type*} (U : Ultrafilter I) (δ : I → ℕ → ℝ)
    (hmono : ∀ i, Antitone (δ i)) (s t : I → ℕ)
    (hs : ¬InfinitesimalAlong U (fun i => δ i (s i)))
    (ht : InfinitesimalAlong U (fun i => δ i (t i))) :
    ∀ᶠ i in U, s i < t i := by
  obtain ⟨ε, hε, he⟩ := (noninfinitesimal_iff U _).mp hs
  filter_upwards [he, ht ε hε] with i hi hi'
  by_contra h
  have hm := hmono i (Nat.le_of_not_gt h)
  exact (not_lt_of_ge (hi.trans hm)) hi'

lemma germ_total {I : Type*} (U : Ultrafilter I)
    (a b : Germ (U : Filter I) ℕ) : a ≤ b ∨ b ≤ a := by
  induction a using Germ.inductionOn with
  | h a =>
    induction b using Germ.inductionOn with
    | h b =>
      exact Ultrafilter.eventually_or.mp (Eventually.of_forall (fun i => le_total (a i) (b i)))

/-- Any fixed finite collection of pairwise distinct crossing reservations is
simultaneously present at the latest of its effective start times. -/
theorem crossing_family_card_le {I J : Type*} [Fintype J] (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ)
    (cache : I → ℕ → Finset ℕ) (N : ℕ)
    (hmono : ∀ i, Antitone (δ i))
    (hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a → a ∈ cache i t)
    (hsize : ∀ i t, (cache i t).card ≤ N)
    (a : J → I → ℕ) (ha : ∀ j, CrossingSequence U valid start finish δ (a j))
    (hdistinct : ∀ j k, j ≠ k → ∀ᶠ i in U, a j i ≠ a k i) :
    Fintype.card J ≤ N := by
  classical
  let latest (i : I) := Finset.univ.sup (fun j => start i (a j i))
  have hva : ∀ᶠ i in U, ∀ j, valid i (a j i) :=
    eventually_all.mpr (fun j => (ha j).1)
  have hbefore : ∀ᶠ i in U, ∀ j k, start i (a j i) < finish i (a k i) := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    exact early_precedes_late U δ hmono _ _ (ha j).2.1 (ha k).2.2
  have hinj : ∀ᶠ i in U, Function.Injective (fun j => a j i) := by
    have hef : ∀ᶠ i in U, ∀ j k, j ≠ k → a j i ≠ a k i := by
      apply eventually_all.mpr
      intro j
      apply eventually_all.mpr
      intro k
      by_cases h : j = k
      · exact Eventually.of_forall (by simp [h])
      · exact (hdistinct j k h).mono (fun _ hi _ => hi)
    exact hef.mono (fun i hi j k hjk => by_contra (fun hne => hi j k hne hjk))
  obtain ⟨i, hvi, hbi, hii⟩ := (hva.and (hbefore.and hinj)).exists
  have hmem : ∀ j, a j i ∈ cache i (latest i) := by
    intro j
    apply hcache i (a j i) (latest i) (hvi j)
    · exact Finset.le_sup (s := Finset.univ) (f := fun j => start i (a j i)) (Finset.mem_univ j)
    · exact Finset.sup_le (fun k _ => (hbi k j).le)
  let f : J → ↥(cache i (latest i)) := fun j => ⟨a j i, hmem j⟩
  have hf : Function.Injective f := by
    intro j k h
    exact hii (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hc
  exact hc.trans (hsize i (latest i))

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter

lemma crossing_finset_card_le {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ)
    (cache : I → ℕ → Finset ℕ) (N : ℕ)
    (hmono : ∀ i, Antitone (δ i))
    (hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a → a ∈ cache i t)
    (hsize : ∀ i t, (cache i t).card ≤ N)
    (s : Finset (Germ (U : Filter I) ℕ))
    (hs : ∀ x ∈ s, x ∈ CrossingGerms U valid start finish δ) : s.card ≤ N := by
  classical
  have hrep : ∀ j : ↥s, ∃ a : I → ℕ,
      (a : Germ (U : Filter I) ℕ) = j.val ∧ CrossingSequence U valid start finish δ a :=
    fun j => hs j.val j.property
  choose a heq ha using hrep
  have hd : ∀ j k : ↥s, j ≠ k → ∀ᶠ i in U, a j i ≠ a k i := by
    intro j k hjk
    apply Ultrafilter.eventually_not.mpr
    intro h
    apply hjk
    apply Subtype.ext
    exact (heq j).symm.trans ((Germ.coe_eq.mpr h).trans (heq k))
  have hc := crossing_family_card_le U valid start finish δ cache N hmono hcache hsize a ha hd
  simpa only [Fintype.card_coe] using hc

/-- The youngest crossing, with the inclusive cache bound and monotone
normalized distances made explicit. -/
theorem youngest_crossing {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ)
    (cache : I → ℕ → Finset ℕ) (N : ℕ)
    (hmono : ∀ i, Antitone (δ i))
    (hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a → a ∈ cache i t)
    (hsize : ∀ i t, (cache i t).card ≤ N)
    (hne : (CrossingGerms U valid start finish δ).Nonempty) :
    (CrossingGerms U valid start finish δ).Finite ∧
    (CrossingGerms U valid start finish δ).ncard ≤ N ∧
    ∃ youngest ∈ CrossingGerms U valid start finish δ,
      ∀ a ∈ CrossingGerms U valid start finish δ, a ≤ youngest := by
  classical
  let C := CrossingGerms U valid start finish δ
  have hb : ∀ s : Finset (Germ (U : Filter I) ℕ), (∀ x ∈ s, x ∈ C) → s.card ≤ N :=
    crossing_finset_card_le U valid start finish δ cache N hmono hcache hsize
  have hfin : C.Finite := by
    by_contra h
    obtain ⟨t, ht, htf, htc⟩ := Set.Infinite.exists_subset_ncard_eq h (N + 1)
    have hbound := hb htf.toFinset (fun x hx => ht (htf.mem_toFinset.mp hx))
    have hc : htf.toFinset.card = t.ncard := (Set.ncard_eq_toFinset_card t htf).symm
    rw [hc, htc] at hbound
    omega
  refine ⟨hfin, ?_, ?_⟩
  · have hbound := hb hfin.toFinset (fun x hx => hfin.mem_toFinset.mp hx)
    rw [show CrossingGerms U valid start finish δ = C from rfl, Set.ncard_eq_toFinset_card C hfin]
    exact hbound
  · obtain ⟨a, ha, hmax⟩ := hfin.exists_maximal hne
    refine ⟨a, ha, ?_⟩
    intro b hb
    rcases germ_total U b a with hba | hab
    · exact hba
    · exact hmax hb hab

end BoundedTreewidthL1

namespace BoundedTreewidthL1

namespace ReservationPath

def Present (P : ReservationPath) (a t : ℕ) : Prop := a ≤ t ∧ t ≤ P.finish a

def Successor (P : ReservationPath) (a b t : ℕ) : Prop :=
  P.Present a t ∧ P.Present b t ∧ a < b ∧
    ∀ c, P.Present c t → a < c → b ≤ c

lemma mem_inclusive (P : ReservationPath) {a t : ℕ} (ht : t ≤ P.last) :
    a ∈ P.inclusive t ↔ P.Present a t := by
  classical
  simp only [inclusive, ht, ↓reduceIte, Finset.mem_filter, Finset.mem_range, Present]
  omega

lemma proposal_present (P : ReservationPath) (t : ℕ) (ht : t ≤ P.last) :
    P.Present t t := ⟨le_rfl, P.launch_le_finish t ht⟩

lemma successor_exists (P : ReservationPath) (a t : ℕ)
    (ht : t ≤ P.last) (ha : P.Present a t) (hat : a < t) :
    ∃ b, P.Successor a b t := by
  classical
  let S := (P.inclusive t).filter (fun b => a < b)
  have hS : S.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨(P.mem_inclusive ht).mpr
    (P.proposal_present t ht), hat⟩⟩
  refine ⟨S.min' hS, ha, ?_, ?_, ?_⟩
  · exact (P.mem_inclusive ht).mp (Finset.mem_filter.mp (Finset.min'_mem S hS)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  · intro c hc hac
    exact Finset.min'_le S c (Finset.mem_filter.mpr ⟨(P.mem_inclusive ht).mpr hc, hac⟩)

lemma proposal_retained_of_other_release (P : ReservationPath) (a t : ℕ)
    (hat : a < t) (ht : t < P.last) (ha : P.finish a = t) : t < P.finish t := by
  have hp := P.launch_le_finish t ht.le
  by_contra h
  have hft : P.finish t = t := Nat.le_antisymm (Nat.le_of_not_gt h) hp
  have := P.one_release a t t hat.le le_rfl ht ha hft
  omega

/-- Once b immediately follows a after an eviction test, no subsequent insertion
can appear between them: new anchors have later launch times. -/
lemma successor_at_later_test (P : ReservationPath) (a b t u : ℕ)
    (hab : a < b) (hbt : b ≤ t) (htu : t < u)
    (ha : P.Present a u) (hb : P.Present b u)
    (hmin : ∀ c, a < c → c ≤ t → t < P.finish c → b ≤ c) :
    P.Successor a b u := by
  refine ⟨ha, hb, hab, ?_⟩
  intro c hc hac
  by_cases hct : c ≤ t
  · exact hmin c hac hct (htu.trans_le hc.2)
  · exact hbt.trans (Nat.le_of_not_ge hct)

/-- A surviving younger anchor exists after the last eviction of any younger
anchor launched above S. The only use of protection is for a successor already
launched at or after `S`. -/
lemma retained_successor (P : ReservationPath) (a S t : ℕ)
    (haS : a < S) (hSt : S ≤ t) (ht : t < P.last)
    (ha : t < P.finish a)
    (hold : ∀ c, a < c → c < S → P.finish c ≤ t)
    (hprotect : ∀ b, S ≤ b → P.Successor a b t → t < P.finish b) :
    ∃ b, a < b ∧ S ≤ b ∧ b ≤ t ∧ t < P.finish b ∧
      ∀ c, a < c → c ≤ t → t < P.finish c → b ≤ c := by
  classical
  obtain ⟨b, hb⟩ := P.successor_exists a t ht.le ⟨haS.le.trans hSt, ha.le⟩
    (haS.trans_le hSt)
  have hex : ∃ c, a < c ∧ c ≤ t ∧ t < P.finish c := by
    by_cases hSb : S ≤ b
    · exact ⟨b, hb.2.2.1, hb.2.1.1, hprotect b hSb hb⟩
    · have hbS : b < S := Nat.lt_of_not_ge hSb
      have hbf : P.finish b = t := (hold b hb.2.2.1 hbS).antisymm hb.2.1.2
      exact ⟨t, haS.trans_le hSt, le_rfl,
        P.proposal_retained_of_other_release b t (hbS.trans_le hSt) ht hbf⟩
  let A := (Finset.range (t + 1)).filter (fun c => a < c ∧ t < P.finish c)
  have hA : A.Nonempty := by
    obtain ⟨c, hac, hct, hcf⟩ := hex
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hac, hcf⟩⟩
  let b' := A.min' hA
  have hb' : a < b' ∧ b' ≤ t ∧ t < P.finish b' := by
    have hm := Finset.mem_filter.mp (Finset.min'_mem A hA)
    exact ⟨hm.2.1, Nat.le_of_lt_succ (Finset.mem_range.mp hm.1), hm.2.2⟩
  refine ⟨b', hb'.1, ?_, hb'.2.1, hb'.2.2, ?_⟩
  · by_contra h
    have := hold b' hb'.1 (Nat.lt_of_not_ge h)
    omega
  · intro c hac hct hcf
    exact Finset.min'_le A c (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hac, hcf⟩)

end ReservationPath
end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter

def PathCrossing {I : Type*} (U : Ultrafilter I) (P : I → ReservationPath)
    (S : I → ℕ) (δ : I → ℕ → ℝ) (a : I → ℕ) : Prop :=
  CrossingSequence U
    (fun i b => b ≤ (P i).last ∧ S i ≤ (P i).finish b)
    (fun i b => max (S i) b) (fun i => (P i).finish) δ a

lemma infinitesimal_congr {I : Type*} (U : Ultrafilter I) {x y : I → ℝ}
    (h : ∀ᶠ i in U, x i = y i) : InfinitesimalAlong U x ↔ InfinitesimalAlong U y := by
  constructor
  · intro hx ε hε
    filter_upwards [h, hx ε hε] with i hi hi'
    simpa only [← hi] using hi'
  · intro hy ε hε
    filter_upwards [h, hy ε hε] with i hi hi'
    simpa only [hi] using hi'

lemma infinitesimal_mono {I : Type*} (U : Ultrafilter I) {x y : I → ℝ}
    (h : ∀ᶠ i in U, x i ≤ y i) (hy : InfinitesimalAlong U y) :
    InfinitesimalAlong U x := by
  intro ε hε
  filter_upwards [h, hy ε hε] with i hi hi'
  exact hi.trans_lt hi'

lemma eventually_choose_nat {I : Type*} (U : Ultrafilter I) (p : I → ℕ → Prop)
    (h : ∀ᶠ i in U, ∃ b, p i b) : ∃ b : I → ℕ, ∀ᶠ i in U, p i (b i) := by
  classical
  let b i := if h : ∃ a, p i a then Classical.choose h else 0
  refine ⟨b, h.mono ?_⟩
  intro i hi
  simpa only [b, dite_eq_left hi] using Classical.choose_spec hi

theorem younger_crossing {I : Type*} (U : Ultrafilter I)
    (P : I → ReservationPath) (S : I → ℕ) (δ : I → ℕ → ℝ)
    (hSL : ∀ i, S i ≤ (P i).last) (hmono : ∀ i, Antitone (δ i))
    (hSearly : ¬InfinitesimalAlong U (fun i => δ i (S i)))
    (hXlate : InfinitesimalAlong U (fun i => δ i (P i).last))
    (a : I → ℕ) (ha : PathCrossing U P S δ a)
    (haold : ∀ᶠ i in U, a i < S i)
    (hprotect : ∀ t : I → ℕ, ¬InfinitesimalAlong U (fun i => δ i (t i)) →
      ∀ᶠ i in U, ∀ b, S i ≤ b → (P i).Successor (a i) b (t i) →
        t i < (P i).finish b) :
    ∃ b : I → ℕ, PathCrossing U P S δ b ∧ ∀ᶠ i in U, a i < b i := by
  classical
  by_contra hno
  have hnone : ∀ b : I → ℕ, PathCrossing U P S δ b →
      ¬(∀ᶠ i in U, a i < b i) := by
    intro b hb hab
    exact hno ⟨b, hb, hab⟩
  let O (i : I) := (Finset.range (S i)).filter (fun b => a i < b)
  let t (i : I) := max (S i) ((O i).sup (P i).finish)
  have hSt : ∀ i, S i ≤ t i := fun i => le_max_left _ _
  have hold : ∀ i c, a i < c → c < S i → (P i).finish c ≤ t i := by
    intro i c hac hcS
    exact (Finset.le_sup (s := O i) (f := (P i).finish)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcS, hac⟩)).trans (le_max_right _ _)
  have htL : ∀ i, t i ≤ (P i).last := by
    intro i
    apply max_le (hSL i)
    apply Finset.sup_le
    intro b hb
    have hbS := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    exact (P i).finish_le_last b (hbS.le.trans (hSL i))
  have hattain : ∀ i, S i < t i →
      ∃ b, a i < b ∧ b < S i ∧ (P i).finish b = t i := by
    intro i hi
    have hsup : t i = (O i).sup (P i).finish := max_eq_right (by dsimp [t] at hi; omega)
    have hO : (O i).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he, Finset.sup_empty, bot_eq_zero] at hsup
      omega
    obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_sup (O i) hO (P i).finish
    exact ⟨b, (Finset.mem_filter.mp hb).2,
      Finset.mem_range.mp (Finset.mem_filter.mp hb).1, he.symm.trans hsup.symm⟩
  have htearly : ¬InfinitesimalAlong U (fun i => δ i (t i)) := by
    intro htlate
    have hbefore := early_precedes_late U δ hmono S t hSearly htlate
    obtain ⟨b, hb⟩ := eventually_choose_nat U
      (fun i b => a i < b ∧ b < S i ∧ (P i).finish b = t i)
      (hbefore.mono fun i hi => hattain i hi)
    have hcross : PathCrossing U P S δ b := by
      refine ⟨?_, ?_, ?_⟩
      · filter_upwards [hb] with i hi
        exact ⟨hi.2.1.le.trans (hSL i), hi.2.2 ▸ hSt i⟩
      · have heq : ∀ᶠ i in U, δ i (max (S i) (b i)) = δ i (S i) := by
          filter_upwards [hb] with i hi
          rw [max_eq_left hi.2.1.le]
        exact fun h => hSearly ((infinitesimal_congr U heq).mp h)
      · have heq : ∀ᶠ i in U, δ i ((P i).finish (b i)) = δ i (t i) :=
          hb.mono (fun i hi => congrArg (δ i) hi.2.2)
        exact (infinitesimal_congr U heq).mpr htlate
    exact hnone b hcross (hb.mono (fun _ hi => hi.1))
  have hta := early_precedes_late U δ hmono t (fun i => (P i).finish (a i))
    htearly ha.2.2
  have htX := early_precedes_late U δ hmono t (fun i => (P i).last) htearly hXlate
  have hprot := hprotect t htearly
  have hex : ∀ᶠ i in U, ∃ b, a i < b ∧ S i ≤ b ∧ b ≤ t i ∧
      t i < (P i).finish b ∧
      ∀ c, a i < c → c ≤ t i → t i < (P i).finish c → b ≤ c := by
    filter_upwards [haold, hta, htX, hprot] with i hai htai htXi hpi
    exact (P i).retained_successor (a i) (S i) (t i) hai (hSt i) htXi htai
      (hold i) hpi
  obtain ⟨b, hb⟩ := eventually_choose_nat U _ hex
  have hbearly : ¬InfinitesimalAlong U (fun i => δ i (max (S i) (b i))) := by
    intro hblate
    exact htearly (infinitesimal_mono U (hb.mono (fun i hi =>
      hmono i (max_le (hSt i) hi.2.2.1))) hblate)
  have hbvalid : ∀ᶠ i in U, b i ≤ (P i).last ∧ S i ≤ (P i).finish (b i) := by
    filter_upwards [hb] with i hi
    exact ⟨hi.2.2.1.trans (htL i), (hSt i).trans hi.2.2.2.1.le⟩
  have hbendearly : ¬InfinitesimalAlong U (fun i => δ i ((P i).finish (b i))) := by
    intro hlate
    exact hnone b ⟨hbvalid, hbearly, hlate⟩ (hb.mono (fun _ hi => hi.1))
  let u i := (P i).finish (b i)
  have hua := early_precedes_late U δ hmono u (fun i => (P i).finish (a i))
    hbendearly ha.2.2
  have huprot := hprotect u hbendearly
  have hcontr : ∀ᶠ i : I in (U : Filter I), False := by
    filter_upwards [hb, hbvalid, hua, huprot] with i hi hvi huai hpi
    have hsucc : (P i).Successor (a i) (b i) (u i) := by
      apply (P i).successor_at_later_test (a i) (b i) (t i) (u i)
        hi.1 hi.2.2.1 hi.2.2.2.1
      · exact ⟨hi.1.le.trans ((P i).launch_le_finish (b i) hvi.1), huai.le⟩
      · exact ⟨(P i).launch_le_finish (b i) hvi.1, le_rfl⟩
      · exact hi.2.2.2.2
    have hbad := hpi (b i) hi.2.1 hsucc
    exact (lt_irrefl (u i)) hbad
  exact hcontr.exists.elim (fun _ h => h)

theorem cache_no_failure {I : Type*} (U : Ultrafilter I)
    (P : I → ReservationPath) (S : I → ℕ) (δ : I → ℕ → ℝ) (N : ℕ)
    (hSL : ∀ i, S i ≤ (P i).last) (hmono : ∀ i, Antitone (δ i))
    (hSearly : ¬InfinitesimalAlong U (fun i => δ i (S i)))
    (hXlate : InfinitesimalAlong U (fun i => δ i (P i).last))
    (hsize : ∀ i t, ((P i).inclusive t).card ≤ N)
    (hold : ∀ a, PathCrossing U P S δ a → ∀ᶠ i in U, a i < S i)
    (hprotect : ∀ a, PathCrossing U P S δ a →
      ∀ t : I → ℕ, ¬InfinitesimalAlong U (fun i => δ i (t i)) →
        ∀ᶠ i in U, ∀ b, S i ≤ b → (P i).Successor (a i) b (t i) →
          t i < (P i).finish b) : False := by
  classical
  let valid i b := b ≤ (P i).last ∧ S i ≤ (P i).finish b
  let start i b := max (S i) b
  let finish i := (P i).finish
  have hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a →
      a ∈ (P i).inclusive t := by
    intro i a t hv hst htf
    have htL : t ≤ (P i).last := htf.trans ((P i).finish_le_last a hv.1)
    exact ((P i).mem_inclusive htL).mpr ⟨(le_max_right _ _).trans hst, htf⟩
  have hroot : PathCrossing U P S δ (fun _ => 0) := by
    refine ⟨Eventually.of_forall ?_, ?_, ?_⟩
    · intro i
      exact ⟨Nat.zero_le _, (P i).root_permanent.symm ▸ hSL i⟩
    · simpa only [Nat.max_zero] using hSearly
    · simpa only [ReservationPath.root_permanent] using hXlate
  have hne : (CrossingGerms U valid start finish δ).Nonempty :=
    ⟨((fun _ : I => 0) : Germ (U : Filter I) ℕ), (fun _ => 0), rfl, hroot⟩
  obtain ⟨_, _, g, hg, hmax⟩ := youngest_crossing U valid start finish δ
    (fun i => (P i).inclusive) N hmono hcache hsize hne
  obtain ⟨a, heq, ha⟩ := hg
  obtain ⟨b, hb, hab⟩ := younger_crossing U P S δ hSL hmono hSearly hXlate a
    ha (hold a ha) (hprotect a ha)
  have hbg : (b : Germ (U : Filter I) ℕ) ≤ g := hmax _ ⟨b, rfl, hb⟩
  rw [← heq] at hbg
  have hba : ∀ᶠ i in U, b i ≤ a i := Germ.coe_le.mp hbg
  obtain ⟨i, hi, hi'⟩ := (hab.and hba).exists
  exact (not_lt_of_ge hi') hi

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter
/-- Numerical interface to the actual cached ensemble. The three tests below
are proved from that ensemble, rather than postulated in the embedding theorem. -/
structure CacheControl (N : ℕ) (Q H : ℝ) where
  path : ReservationPath
  start : ℕ
  start_le : start ≤ path.last
  delta : ℕ → ℝ
  antitone : Antitone delta
  nonneg : ∀ t, 0 ≤ delta t
  at_start : delta start = 1
  at_end : delta path.last = 0
  error : ℝ
  error_nonneg : 0 ≤ error
  size : ∀ t, (path.inclusive t).card ≤ N
  launch : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → start ≤ a →
    delta a ≤ Q*(error+delta e)
  distant : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → a < start →
    delta a ≤ H → 1 ≤ Q*(error+delta e)
  protect : ∀ a e t b, e ≤ path.last → a ∈ path.inclusive e → a < start →
    H < delta a → start ≤ t → t < e → start ≤ b → path.Successor a b t →
    Q*(error+delta e) < delta t → t < path.finish b

lemma infinitesimal_add_mul {I : Type*} (U : Ultrafilter I) (x y : I → ℝ)
    (hx : InfinitesimalAlong U x) (hy : InfinitesimalAlong U y) (Q : ℝ) (hQ : 0 < Q) :
    InfinitesimalAlong U (fun i => Q*(x i+y i)) := by
  intro ε hε
  have he : 0 < ε/(2*Q) := by positivity
  filter_upwards [hx _ he,hy _ he] with i hxi hyi
  have heq : ε/(2*Q)+ε/(2*Q) = ε/Q := by ring
  have hh : x i+y i < ε/Q := by rw [← heq]; exact add_lt_add hxi hyi
  simpa only [mul_comm] using (lt_div_iff₀ hQ).mp hh

lemma CacheControl.no_failure {I : Type*} (U : Ultrafilter I) (N : ℕ) (Q H : ℝ)
    (hQ : 0 < Q) (C : I → CacheControl N Q H)
    (herror : InfinitesimalAlong U (fun i => (C i).error)) : False := by
  have hear : ¬InfinitesimalAlong U (fun i => (C i).delta (C i).start) := by
    intro hh
    obtain ⟨i,hi⟩ := (hh 1 (by norm_num)).exists
    change (C i).delta (C i).start < 1 at hi
    rw [(C i).at_start] at hi
    exact (lt_irrefl _ hi)
  have hlate : InfinitesimalAlong U (fun i => (C i).delta (C i).path.last) := by
    intro ε hε
    exact Eventually.of_forall (fun i => by dsimp only; rw [(C i).at_end]; exact hε)
  apply cache_no_failure U (fun i => (C i).path) (fun i => (C i).start)
    (fun i => (C i).delta) N (fun i => (C i).start_le)
    (fun i => (C i).antitone) hear hlate (fun i => (C i).size)
  · intro a ha
    have herr := infinitesimal_add_mul U _ _ herror ha.2.2 Q hQ
    change ∀ᶠ i in U, a i < (C i).start
    simp only [← not_le]
    apply Ultrafilter.eventually_not.mpr
    intro hnot
    have haS : ∀ᶠ i in U, (C i).start ≤ a i := hnot.mono (fun _ hi => hi)
    apply ha.2.1
    apply infinitesimal_mono U _ herr
    filter_upwards [ha.1,haS] with i hi hiS
    rw [max_eq_right hiS]
    apply (C i).launch (a i) ((C i).path.finish (a i))
      ((C i).path.finish_le_last _ hi.1) _ hiS
    exact ((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
      ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩
  · intro a ha t ht
    have herr := infinitesimal_add_mul U _ _ herror ha.2.2 Q hQ
    have hold : ∀ᶠ i in U, a i < (C i).start := by
      simp only [← not_le]
      apply Ultrafilter.eventually_not.mpr
      intro hnot
      apply ha.2.1
      apply infinitesimal_mono U _ herr
      filter_upwards [ha.1,hnot] with i hi hiS
      rw [max_eq_right hiS]
      apply (C i).launch (a i) ((C i).path.finish (a i))
        ((C i).path.finish_le_last _ hi.1) _ hiS
      exact ((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
        ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩
    have hdist : ∀ᶠ i in U, H < (C i).delta (a i) := by
      filter_upwards [ha.1,hold,herr 1 (by norm_num)] with i hi hoi hei
      by_contra hn
      have hh := (C i).distant (a i) ((C i).path.finish (a i))
        ((C i).path.finish_le_last _ hi.1)
        (((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
          ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩) hoi (le_of_not_gt hn)
      exact (not_lt_of_ge hh) hei
    have hte := early_precedes_late U (fun i => (C i).delta)
      (fun i => (C i).antitone) t (fun i => (C i).path.finish (a i)) ht ha.2.2
    obtain ⟨ε,hε,htearly⟩ := (noninfinitesimal_iff U _).mp ht
    filter_upwards [ha.1,hold,hdist,hte,htearly,herr ε hε] with i hi hoi hdi hti het her
    intro b hbS hsucc
    apply (C i).protect (a i) ((C i).path.finish (a i)) (t i) b
      ((C i).path.finish_le_last _ hi.1)
      (((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
        ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩) hoi hdi
      (hbS.trans hsucc.2.1.1) hti hbS hsucc (her.trans_le het)

/-- Compactness is used only on numerical cache data, not on random samplers or
on a bounded number of vertices. -/
theorem CacheControl.uniform_lower (N : ℕ) (Q H : ℝ) (hQ : 0 < Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ C : CacheControl N Q H, c ≤ C.error := by
  classical
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ C : CacheControl N Q H, C.error < 1/((n:ℝ)+1) :=
    hn _ (by positivity)
  choose C hC using hex
  let U := Ultrafilter.of (atTop : Filter ℕ)
  apply CacheControl.no_failure U N Q H hQ C
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε)
  apply (Ultrafilter.of_le atTop) (mem_atTop_sets.mpr ⟨n,?_⟩)
  intro m hm
  have hnm : (n:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m:ℝ)+1 := by positivity
  apply (hC m).trans
  apply (div_lt_iff₀ hmpos).mpr
  have hh := (div_lt_iff₀ hε).mp (hn.trans_le hnm)
  nlinarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1

theorem protected_threshold (K J H D₀ δ L older younger : ℝ)
    (hK : 2 < K) (hJ : J = 10 * (K + 1)) (hH : 10 ^ 5 * J < H)
    (hD : H < D₀) (hδ : 0 < δ) (_ : δ ≤ 1)
    (hLlo : δ / 4 ≤ L) (hLhi : L ≤ 10 * D₀)
    (hyδ : younger ≤ K * δ) (hy2 : younger ≤ 2)
    (holder : D₀ - 1 ≤ older) :
    ∃ τ ∈ ({L / 100, J * L} : Set ℝ), younger ≤ τ ∧ τ < older := by
  have hJpos : 0 < J := by linarith
  have hDlarge : 10 < D₀ := by norm_num at hH; linarith
  by_cases hL : L ≤ 300
  · refine ⟨J * L, by simp, ?_, ?_⟩
    · have hmul := mul_le_mul_of_nonneg_left hLlo hJpos.le
      have hgap : K * δ < J * (δ / 4) := by rw [hJ]; nlinarith
      exact hyδ.trans (hgap.le.trans hmul)
    · have hmul := mul_le_mul_of_nonneg_left hL hJpos.le
      norm_num at hH
      linarith
  · refine ⟨L / 100, by simp, ?_, ?_⟩
    · linarith
    · linarith

end BoundedTreewidthL1

end OAI
