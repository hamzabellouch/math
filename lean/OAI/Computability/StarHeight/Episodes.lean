import OAI.Computability.StarHeight.Height

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uS

namespace EpisodeAlgebra

open scoped Computability

variable {Alphabet : Type u} {S : Type uS}

def PrefixCode (E : Language Alphabet) : Prop :=
  [] ∉ E ∧ ∀ e ∈ E, ∀ f ∈ E, e <+: f → e = f

def AllIn (D : Language Alphabet) (es : List (List Alphabet)) : Prop :=
  ∀ e ∈ es, e ∈ D

def updateWord (G : List Alphabet → S → S) (x : S) (es : List (List Alphabet)) : S :=
  es.foldl (fun z e => G e z) x

def graph (D : Language Alphabet) (G : List Alphabet → S → S) (x y : S) : Language Alphabet :=
  {w | ∃ es, AllIn D es ∧ es.flatten = w ∧ updateWord G x es = y}

lemma AllIn.mono {D E : Language Alphabet} {es : List (List Alphabet)}
    (h : AllIn D es) (hDE : D ≤ E) : AllIn E es := fun e he => hDE (h e he)

lemma AllIn.append {D : Language Alphabet} {es fs : List (List Alphabet)}
    (he : AllIn D es) (hf : AllIn D fs) : AllIn D (es ++ fs) := by
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · exact he e hm
  · exact hf e hm

lemma AllIn.of_append_right {D : Language Alphabet} {es fs : List (List Alphabet)}
    (h : AllIn D (es ++ fs)) : AllIn D fs := fun e he => h e (List.mem_append_right _ he)

@[simp] lemma updateWord_nil (G : List Alphabet → S → S) (x : S) :
    updateWord G x [] = x := rfl

@[simp] lemma updateWord_cons (G : List Alphabet → S → S) (x : S)
    (e : List Alphabet) (es : List (List Alphabet)) :
    updateWord G x (e :: es) = updateWord G (G e x) es := rfl

lemma updateWord_append (G : List Alphabet → S → S) (x : S)
    (es fs : List (List Alphabet)) :
    updateWord G x (es ++ fs) = updateWord G (updateWord G x es) fs :=
  List.foldl_append

lemma graph_nil (D : Language Alphabet) (G : List Alphabet → S → S) (x : S) :
    [] ∈ graph D G x x := ⟨[], by simp [AllIn], rfl, rfl⟩

lemma graph_singleton {D : Language Alphabet} (G : List Alphabet → S → S)
    (x : S) {e : List Alphabet} (he : e ∈ D) : e ∈ graph D G x (G e x) :=
  ⟨[e], by simpa [AllIn], by simp, rfl⟩

lemma graph_mono {D E : Language Alphabet} (hDE : D ≤ E)
    (G : List Alphabet → S → S) (x y : S) : graph D G x y ≤ graph E G x y := by
  rintro w ⟨es, he, hw, hx⟩
  exact ⟨es, he.mono hDE, hw, hx⟩

lemma graph_concat {D : Language Alphabet} {G : List Alphabet → S → S}
    {x y z : S} {u v : List Alphabet} (hu : u ∈ graph D G x y)
    (hv : v ∈ graph D G y z) : u ++ v ∈ graph D G x z := by
  obtain ⟨es, he, rfl, hx⟩ := hu
  obtain ⟨fs, hf, rfl, hy⟩ := hv
  exact ⟨es ++ fs, he.append hf, List.flatten_append,
    by rw [updateWord_append, hx, hy]⟩

lemma flatten_prefix {E : Language Alphabet} (hE : PrefixCode E)
    {es fs : List (List Alphabet)} (he : AllIn E es) (hf : AllIn E fs)
    (hp : es.flatten <+: fs.flatten) : es <+: fs := by
  induction es generalizing fs with
  | nil => exact List.nil_prefix
  | cons e es ih =>
      have heE : e ∈ E := he e (by simp)
      cases fs with
      | nil =>
          obtain ⟨r, hr⟩ := hp
          have he0 : e = [] := by
            have hh : e ++ (es.flatten ++ r) = [] := by simpa [List.append_assoc] using hr
            exact (List.append_eq_nil_iff.mp hh).1
          exact False.elim (hE.1 (he0 ▸ heE))
      | cons f fs =>
          have hfE : f ∈ E := hf f (by simp)
          have hePre : e <+: (f :: fs).flatten :=
            (List.prefix_append e es.flatten).trans hp
          have hfPre : f <+: (f :: fs).flatten := List.prefix_append _ _
          have hef : e = f := by
            rcases List.prefix_or_prefix_of_prefix hePre hfPre with h | h
            · exact hE.2 e heE f hfE h
            · exact (hE.2 f hfE e heE h).symm
          subst f
          obtain ⟨r, hr⟩ := hp
          have htail : es.flatten ++ r = fs.flatten := by
            apply List.append_cancel_left (as := e)
            simpa only [List.flatten_cons, List.append_assoc] using hr
          have hrec := ih (fun a ha => he a (by simp [ha]))
            (fun a ha => hf a (by simp [ha])) ⟨r, htail⟩
          obtain ⟨gs, hgs⟩ := hrec
          exact ⟨gs, by simp [hgs]⟩

lemma consume_graph_prefix {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) {G : List Alphabet → S → S}
    {x z : S} {u v : List Alphabet} {es : List (List Alphabet)}
    (hu : u ∈ graph D' G x z) (hes : AllIn D es) (hword : u ++ v = es.flatten) :
    ∃ fs, AllIn D fs ∧ fs.flatten = v ∧ updateWord G x es = updateWord G z fs := by
  obtain ⟨pre, hp, hu, hx⟩ := hu
  have hpre := flatten_prefix hE (hp.mono (hD'D.trans hDE)) (hes.mono hDE)
    (show pre.flatten <+: es.flatten from ⟨v, by rw [hu, hword]⟩)
  obtain ⟨fs, rfl⟩ := hpre
  refine ⟨fs, hes.of_append_right, ?_, ?_⟩
  · apply List.append_cancel_left (as := u)
    simpa only [List.flatten_append, hu] using hword.symm
  · rw [updateWord_append, hx]

lemma flatten_injective {E : Language Alphabet} (hE : PrefixCode E)
    {es fs : List (List Alphabet)} (he : AllIn E es) (hf : AllIn E fs)
    (h : es.flatten = fs.flatten) : es = fs := by
  have hp := flatten_prefix hE he hf (h ▸ List.prefix_rfl)
  have hq := flatten_prefix hE hf he (h.symm ▸ List.prefix_rfl)
  exact hp.sublist.antisymm hq.sublist

lemma graph_iff_update {E D : Language Alphabet} (hE : PrefixCode E) (hDE : D ≤ E)
    (G : List Alphabet → S → S) (x y : S) {es : List (List Alphabet)}
    (he : AllIn D es) : es.flatten ∈ graph D G x y ↔ updateWord G x es = y := by
  constructor
  · rintro ⟨fs, hf, hw, hx⟩
    have hfs := flatten_injective hE (hf.mono hDE) (he.mono hDE) hw
    simpa only [hfs] using hx
  · exact fun hx => ⟨es, he, rfl, hx⟩

def SplitSound (D : Language Alphabet) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) : Prop :=
  ∀ (x y : S) (es : List (List Alphabet)) (u v : List Alphabet),
    AllIn D es → u ∈ P x → v ∈ Q y → u ++ v <+: es.flatten →
      ∃ e fs, es = e :: fs ∧ u ++ v = e ∧ G e x = y

def SplitAvailable (D D' : Language Alphabet) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) : Prop :=
  ∀ e ∈ D, e ∉ D' → ∀ x, e ∈ P x * Q (G e x)

lemma consume_pair_prefix {D : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (hs : SplitSound D G P Q)
    {x y : S} {u v r : List Alphabet} {es : List (List Alphabet)}
    (he : AllIn D es) (hu : u ∈ P x) (hv : v ∈ Q y)
    (hw : (u ++ v) ++ r = es.flatten) :
    ∃ fs, AllIn D fs ∧ fs.flatten = r ∧ updateWord G x es = updateWord G y fs := by
  obtain ⟨e, fs, rfl, huv, hxy⟩ := hs x y es u v he hu hv ⟨r, hw⟩
  refine ⟨fs, fun a ha => he a (by simp [ha]), ?_, ?_⟩
  · apply List.append_cancel_left (as := e)
    simpa only [List.flatten_cons, huv] using hw.symm
  · simp only [updateWord_cons, hxy]

def start (W : S → S → Language Alphabet) (P : S → Language Alphabet) (x : S) :=
  ⨆ i, W x i * P i

def middle (W : S → S → Language Alphabet) (P Q : S → Language Alphabet) :=
  ⨆ j, ⨆ i, Q j * W j i * P i

def finish (W : S → S → Language Alphabet) (Q : S → Language Alphabet) (y : S) :=
  ⨆ l, Q l * W l y

def body (W : S → S → Language Alphabet) (P Q : S → Language Alphabet) (x y : S) :=
  W x y + start W P x * (middle W P Q)∗ * finish W Q y

lemma mem_start_iff {W : S → S → Language Alphabet} {P : S → Language Alphabet}
    {x : S} {w : List Alphabet} : w ∈ start W P x ↔
    ∃ i u v, u ∈ W x i ∧ v ∈ P i ∧ u ++ v = w := by
  simp only [start, Language.mem_iSup, Language.mem_mul]
  aesop

lemma mem_middle_iff {W : S → S → Language Alphabet} {P Q : S → Language Alphabet}
    {w : List Alphabet} : w ∈ middle W P Q ↔
    ∃ j i u v p, u ∈ Q j ∧ v ∈ W j i ∧ p ∈ P i ∧ (u ++ v) ++ p = w := by
  simp only [middle, Language.mem_iSup, Language.mem_mul]
  constructor
  · rintro ⟨j, i, a, ⟨u, hu, v, hv, rfl⟩, p, hp, rfl⟩
    exact ⟨j, i, u, v, p, hu, hv, hp, rfl⟩
  · rintro ⟨j, i, u, v, p, hu, hv, hp, rfl⟩
    exact ⟨j, i, u ++ v, ⟨u, hu, v, hv, rfl⟩, p, hp, rfl⟩

lemma mem_finish_iff {W : S → S → Language Alphabet} {Q : S → Language Alphabet}
    {y : S} {w : List Alphabet} : w ∈ finish W Q y ↔
    ∃ j u v, u ∈ Q j ∧ v ∈ W j y ∧ u ++ v = w := by
  simp only [finish, Language.mem_iSup, Language.mem_mul]
  aesop

lemma mem_body_iff {W : S → S → Language Alphabet} {P Q : S → Language Alphabet}
    {x y : S} {w : List Alphabet} : w ∈ body W P Q x y ↔
    w ∈ W x y ∨ ∃ a ms b, a ∈ start W P x ∧ AllIn (middle W P Q) ms ∧
      b ∈ finish W Q y ∧ (a ++ ms.flatten) ++ b = w := by
  simp only [body, Language.mem_add, Language.mem_mul, Language.mem_kstar]
  constructor
  · rintro (h | ⟨c, ⟨a, ha, m, ⟨ms, rfl, hm⟩, rfl⟩, b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ms, b, ha, hm, hb, rfl⟩
  · rintro (h | ⟨a, ms, b, ha, hm, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a ++ ms.flatten, ⟨a, ha, ms.flatten, ⟨ms, rfl, hm⟩, rfl⟩,
        b, hb, rfl⟩

lemma suffix_sound {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (hs : SplitSound D G P Q)
    (ms : List (List Alphabet)) (hm : AllIn (middle (graph D' G) P Q) ms)
    {x y : S} {p b : List Alphabet} {es : List (List Alphabet)}
    (hp : p ∈ P x) (hb : b ∈ finish (graph D' G) Q y) (he : AllIn D es)
    (hw : (p ++ ms.flatten) ++ b = es.flatten) : updateWord G x es = y := by
  induction ms generalizing x p es with
  | nil =>
      obtain ⟨j, q, w, hq, hwg, rfl⟩ := mem_finish_iff.mp hb
      have hw' : (p ++ q) ++ w = es.flatten := by simpa [List.append_assoc] using hw
      obtain ⟨fs, hf, hfw, hxy⟩ := consume_pair_prefix hs he hp hq hw'
      rw [hxy]
      apply (graph_iff_update hE hDE G j y hf).mp
      rw [hfw]
      exact graph_mono hD'D G j y hwg
  | cons m ms ih =>
      obtain ⟨j, i, q, w, p', hq, hwg, hp', rfl⟩ :=
        mem_middle_iff.mp (hm m (by simp))
      have hw' : (p ++ q) ++ (w ++ ((p' ++ ms.flatten) ++ b)) = es.flatten := by
        simpa only [List.flatten_cons, List.append_assoc] using hw
      obtain ⟨fs, hf, hfw, hxy⟩ := consume_pair_prefix hs he hp hq hw'
      obtain ⟨gs, hg, hgw, hj⟩ := consume_graph_prefix hE hDE hD'D hwg hf hfw.symm
      rw [hxy, hj]
      exact ih (fun a ha => hm a (by simp [ha])) hp' hg hgw.symm

lemma body_sound {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (hs : SplitSound D G P Q)
    {x y : S} {es : List (List Alphabet)} (he : AllIn D es)
    (hb : es.flatten ∈ body (graph D' G) P Q x y) : updateWord G x es = y := by
  rcases mem_body_iff.mp hb with hw | ⟨a, ms, b, ha, hm, hb, hword⟩
  · exact (graph_iff_update hE hDE G x y he).mp (graph_mono hD'D G x y hw)
  · obtain ⟨i, w, p, hw, hp, rfl⟩ := mem_start_iff.mp ha
    have hword' : w ++ ((p ++ ms.flatten) ++ b) = es.flatten := by
      simpa only [List.append_assoc] using hword
    obtain ⟨fs, hf, hfw, hxy⟩ := consume_graph_prefix hE hDE hD'D hw he hword'
    rw [hxy]
    exact suffix_sound hE hDE hD'D hs ms hm hp hb hf hfw.symm

lemma body_prepend_skip {D' : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} {x z y : S} {u v : List Alphabet}
    (hu : u ∈ graph D' G x z) (hv : v ∈ body (graph D' G) P Q z y) :
    u ++ v ∈ body (graph D' G) P Q x y := by
  apply mem_body_iff.mpr
  rcases mem_body_iff.mp hv with hv | ⟨a, ms, b, ha, hm, hb, rfl⟩
  · exact Or.inl (graph_concat hu hv)
  · obtain ⟨i, w, p, hw, hp, rfl⟩ := mem_start_iff.mp ha
    apply Or.inr
    refine ⟨(u ++ w) ++ p, ms, b, ?_, hm, hb, ?_⟩
    · exact mem_start_iff.mpr ⟨i, u ++ w, p, graph_concat hu hw, hp, rfl⟩
    · simp only [List.append_assoc]

lemma body_prepend_pair {D' : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} {x z y : S} {p q v : List Alphabet}
    (hp : p ∈ P x) (hq : q ∈ Q z) (hv : v ∈ body (graph D' G) P Q z y) :
    (p ++ q) ++ v ∈ body (graph D' G) P Q x y := by
  have hstart : p ∈ start (graph D' G) P x :=
    mem_start_iff.mpr ⟨x, [], p, graph_nil D' G x, hp, by simp⟩
  apply mem_body_iff.mpr
  rcases mem_body_iff.mp hv with hv | ⟨a, ms, b, ha, hm, hb, rfl⟩
  · refine Or.inr ⟨p, [], q ++ v, hstart, by simp [AllIn], ?_, ?_⟩
    · exact mem_finish_iff.mpr ⟨z, q, v, hq, hv, rfl⟩
    · simp [List.append_assoc]
  · obtain ⟨i, w, r, hw, hr, rfl⟩ := mem_start_iff.mp ha
    have hmid : (q ++ w) ++ r ∈ middle (graph D' G) P Q :=
      mem_middle_iff.mpr ⟨z, i, q, w, r, hq, hw, hr, rfl⟩
    refine Or.inr ⟨p, ((q ++ w) ++ r) :: ms, b, hstart, ?_, hb, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hmid
      · exact hm a ha
    · simp only [List.flatten_cons, List.append_assoc]

lemma body_available {D D' : Language Alphabet} {G : List Alphabet → S → S}
    {P Q : S → Language Alphabet} (ha : SplitAvailable D D' G P Q)
    (es : List (List Alphabet)) (he : AllIn D es) (x : S) :
    es.flatten ∈ body (graph D' G) P Q x (updateWord G x es) := by
  classical
  induction es generalizing x with
  | nil => exact mem_body_iff.mpr (Or.inl (graph_nil D' G x))
  | cons e es ih =>
      have heD := he e (by simp)
      have hes : AllIn D es := fun a ha => he a (by simp [ha])
      have hind := ih hes (G e x)
      by_cases he' : e ∈ D'
      · exact body_prepend_skip (graph_singleton G x he') hind
      · obtain ⟨p, hp, q, hq, heq⟩ := Language.mem_mul.mp (ha e heD he' x)
        simpa only [heq, List.flatten_cons, updateWord_cons] using body_prepend_pair hp hq hind

theorem split_identity {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) (hs : SplitSound D G P Q)
    (ha : SplitAvailable D D' G P Q) (x y : S) :
    graph D G x y = D∗ ⊓ body (graph D' G) P Q x y := by
  ext w
  constructor
  · rintro ⟨es, he, rfl, rfl⟩
    exact ⟨Language.join_mem_kstar he, body_available ha es he x⟩
  · rintro ⟨⟨es, rfl, he⟩, hb⟩
    exact ⟨es, he, rfl, body_sound hE hDE hD'D hs he hb⟩

theorem split_height [Finite S] {E D D' : Language Alphabet} (hE : PrefixCode E)
    (hDE : D ≤ E) (hD'D : D' ≤ D) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet) (hs : SplitSound D G P Q)
    (ha : SplitAvailable D D' G P Q) (H : ℕ)
    (hD : HasHeightAtMost D 1) (hP : ∀ x, HasHeightAtMost (P x) 1)
    (hQ : ∀ y, HasHeightAtMost (Q y) 1)
    (hW : ∀ x y, HasHeightAtMost (graph D' G x y) H) (x y : S) :
    HasHeightAtMost (graph D G x y) (max 2 (1 + H)) := by
  rw [split_identity hE hDE hD'D G P Q hs ha]
  have hH : H ≤ max 2 (1 + H) := by omega
  have h1 : 1 ≤ max 1 H := le_max_left _ _
  have hh : H ≤ max 1 H := le_max_right _ _
  have hm : max 1 H ≤ max 2 (1 + H) := by omega
  have hstar : 1 + max 1 H ≤ max 2 (1 + H) := by omega
  apply (hD.star.mono (le_max_left _ _)).inter
  apply (hW x y |>.mono hH).union
  apply HasHeightAtMost.concat
  · apply HasHeightAtMost.concat
    · exact (HasHeightAtMost.iSup _ (fun i => (hW x i |>.mono hh).concat
        (hP i |>.mono h1))).mono hm
    · exact (HasHeightAtMost.iSup _ (fun j => HasHeightAtMost.iSup _ (fun i =>
        ((hQ j |>.mono h1).concat (hW j i |>.mono hh)).concat (hP i |>.mono h1)))).star.mono hstar
  · exact (HasHeightAtMost.iSup _ (fun l => (hQ l |>.mono h1).concat
      (hW l y |>.mono hh))).mono hm

lemma graph_empty [DecidableEq S] (G : List Alphabet → S → S) (x y : S) :
    graph (0 : Language Alphabet) G x y = if x = y then 1 else 0 := by
  classical
  ext w
  by_cases h : x = y
  · subst y
    simp only [ite_true, Language.mem_one]
    constructor
    · rintro ⟨es, he, rfl, _⟩
      have hes : es = [] := by
        cases es with
        | nil => rfl
        | cons e es => exact False.elim (he e (by simp))
      simp [hes]
    · rintro rfl
      exact graph_nil 0 G x
  · simp only [h, ite_false, Language.notMem_zero, iff_false]
    rintro ⟨es, he, _, hu⟩
    have hes : es = [] := by
      cases es with
      | nil => rfl
      | cons e es => exact False.elim (he e (by simp))
    exact h (by simpa [hes] using hu)

lemma empty_skip_height (G : List Alphabet → S → S) (x y : S) :
    HasHeightAtMost (graph (0 : Language Alphabet) G x y) 0 := by
  classical
  rw [graph_empty]
  split
  · exact HasHeightAtMost.one 0
  · exact HasHeightAtMost.zero 0

end EpisodeAlgebra

end GeneralizedStarHeight

end OAI
