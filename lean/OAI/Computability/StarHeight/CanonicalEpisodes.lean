import OAI.Computability.StarHeight.ScheduleClock

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uAlphabet2 uAlphabet3

namespace WordIntervals

open LocalMarkers

variable {Alphabet : Type uAlphabet}

def segment (f : ℤ → Alphabet) (s : ℤ) (n : ℕ) : List Alphabet :=
  List.ofFn (fun i : Fin n => f (s + i.val))

@[simp] lemma length_segment (f : ℤ → Alphabet) (s : ℤ) (n : ℕ) :
    (segment f s n).length = n := List.length_ofFn

lemma segment_add (f : ℤ → Alphabet) (s : ℤ) (n m : ℕ) :
    segment f s (n + m) = segment f s n ++ segment f (s + n) m := by
  rw [segment, List.ofFn_add]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  congr 1
  simp only [Fin.val_natAdd, Nat.cast_add]
  omega

lemma segment_congr {f g : ℤ → Alphabet} {s : ℤ} {n : ℕ}
    (he : AgreesOn f g s (s + n)) : segment f s n = segment g s n := by
  apply List.ofFn_inj.mpr
  funext i
  exact he _ (by omega) (by omega)

lemma segment_translate (f : ℤ → Alphabet) (s a : ℤ) (n : ℕ) :
    segment (fun x => f (x + a)) s n = segment f (s + a) n := by
  apply List.ofFn_inj.mpr
  funext i
  change f (s + (i.val : ℤ) + a) = f (s + a + i.val)
  congr 1
  omega

def Realizes (w : List Alphabet) (s : ℤ) (f : ℤ → Alphabet) : Prop :=
  ∀ i : Fin w.length, f (s + i.val) = w[i.val]

lemma realizes_iff_segment {w : List Alphabet} {s : ℤ} {f : ℤ → Alphabet} :
    Realizes w s f ↔ segment f s w.length = w := by
  constructor
  · intro h
    calc
      segment f s w.length = List.ofFn (fun i : Fin w.length => w[i.val]) :=
        List.ofFn_inj.mpr (funext h)
      _ = w := List.ofFn_getElem
  · intro h i
    have he := congrArg (fun w => w[i.val]?) h
    simpa [segment, List.getElem?_eq_getElem, i.isLt] using he

lemma realizes_segment (f : ℤ → Alphabet) (s : ℤ) (n : ℕ) :
    Realizes (segment f s n) s f := by
  apply realizes_iff_segment.mpr
  simp

lemma realizes_exists [Nonempty Alphabet] (w : List Alphabet) (s : ℤ) :
    ∃ f, Realizes w s f := by
  classical
  let f (x : ℤ) : Alphabet :=
    if h : 0 ≤ x - s ∧ x - s < w.length then
      w[(x - s).toNat]'(by omega) else Classical.choice inferInstance
  refine ⟨f, fun i => ?_⟩
  dsimp [f]
  simp only [add_sub_cancel_left, Nat.cast_nonneg, i.isLt, Nat.cast_lt, and_self, dite_true,
    Int.toNat_natCast]

lemma Realizes.prefix {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (h : Realizes v s f) (hp : u <+: v) : Realizes u s f := by
  intro i
  exact (h ⟨i.val, lt_of_lt_of_le i.isLt hp.length_le⟩).trans (hp.getElem i.isLt).symm

lemma Realizes.agrees {u v : List Alphabet} {s : ℤ} {f g : ℤ → Alphabet}
    (hf : Realizes u s f) (hg : Realizes v s g) (hp : u <+: v) :
    AgreesOn f g s (s + u.length) := by
  have hg' := hg.prefix hp
  intro x hx hx'
  let i : Fin u.length := ⟨(x - s).toNat, by omega⟩
  have hi : s + (i.val : ℤ) = x := by dsimp [i]; omega
  exact hi ▸ (hf i).trans (hg' i).symm

lemma Realizes.append {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (hu : Realizes u s f) (hv : Realizes v (s + u.length) f) : Realizes (u ++ v) s f := by
  apply realizes_iff_segment.mpr
  rw [List.length_append, segment_add, realizes_iff_segment.mp hu, realizes_iff_segment.mp hv]

lemma Realizes.append_left {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (h : Realizes (u ++ v) s f) : Realizes u s f := h.prefix ⟨v, rfl⟩

lemma Realizes.append_right {u v : List Alphabet} {s : ℤ} {f : ℤ → Alphabet}
    (h : Realizes (u ++ v) s f) : Realizes v (s + u.length) f := by
  intro i
  have he := h ⟨u.length + i.val, by simp only [List.length_append]; omega⟩
  change f (s + ((u.length + i.val : ℕ) : ℤ)) = (u ++ v)[u.length + i.val] at he
  have hp : s + ((u.length + i.val : ℕ) : ℤ) = s + u.length + i.val := by push_cast; ring
  rw [hp, List.getElem_append_right (show u.length ≤ u.length + i.val by omega)] at he
  simpa only [Nat.add_sub_cancel_left] using he

def piece (f : ℤ → Alphabet) (s t : ℤ) : List Alphabet := segment f s (t - s).toNat

lemma length_piece {f : ℤ → Alphabet} {s t : ℤ} (hst : s ≤ t) :
    ((piece f s t).length : ℤ) = t - s := by
  simp only [piece, length_segment]
  exact Int.toNat_of_nonneg (by omega)

lemma piece_append (f : ℤ → Alphabet) {s t u : ℤ} (hst : s ≤ t) (htu : t ≤ u) :
    piece f s u = piece f s t ++ piece f t u := by
  have hn : (u - s).toNat = (t - s).toNat + (u - t).toNat := by omega
  have hs : s + ((t - s).toNat : ℤ) = t := by omega
  simp only [piece, hn, segment_add, hs]

lemma piece_congr {f g : ℤ → Alphabet} {s t : ℤ} (hst : s ≤ t)
    (he : AgreesOn f g s t) : piece f s t = piece g s t := by
  apply segment_congr
  have hs : s + ((t - s).toNat : ℤ) = t := by omega
  simpa only [hs] using he

lemma realizes_piece {f : ℤ → Alphabet} {w : List Alphabet} {s : ℤ}
    (h : Realizes w s f) : piece f s (s + w.length) = w := by
  simpa only [piece, add_sub_cancel_left, Int.toNat_natCast] using realizes_iff_segment.mp h

variable {M : Type uM} [Monoid M]

def product (h : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet) (s t : ℤ) : M := h (piece f s t)

lemma product_append (h : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    {s t u : ℤ} (hst : s ≤ t) (htu : t ≤ u) :
    product h f s u = product h f s t * product h f t u := by
  unfold product
  rw [piece_append f hst htu]
  exact map_mul h _ _

lemma product_congr (h : FreeMonoid Alphabet →* M) {f g : ℤ → Alphabet} {s t : ℤ}
    (hst : s ≤ t) (he : AgreesOn f g s t) : product h f s t = product h g s t :=
  congrArg h (piece_congr hst he)

end WordIntervals

namespace CanonicalEpisodes

open LocalMarkers WordIntervals EpisodeEnd

variable {Alphabet : Type uAlphabet2}

structure Parameters (Alphabet : Type uAlphabet3) where
  B : ℤ
  S : ℤ
  d : ℕ
  K : ℕ
  offset : ℤ
  tail : ℤ
  rule : Rule Alphabet d K
  B_pos : 0 < B
  S_nonneg : 0 ≤ S
  d_ge : 2 ≤ d
  seed_long : 3 * d ^ 2 < K
  tail_pos : 0 < tail

namespace Parameters

variable (C : Parameters Alphabet)

def width : ℤ := 3 * C.d + (C.B - 1) * C.S

noncomputable def small (f : ℤ → Alphabet) (z : ℤ) : Option ℤ :=
  EndSearch.search (C.rule.markers f) C.B C.S C.d z

noncomputable def large (f : ℤ → Alphabet) (z : ℤ) : Option ℤ :=
  EndSearch.search (C.rule.markers f) C.B C.S (3 * C.d) z

def Visible (s b z : ℤ) : Prop :=
  s ≤ z - C.width - C.rule.r ∧ z + C.width + C.rule.r ≤ b ∧
    s ≤ z ∧ z + C.K ≤ b

lemma Visible.mono {s b s' b' z : ℤ} (h : C.Visible s b z)
    (hs : s' ≤ s) (hb : b ≤ b') : C.Visible s' b' z := by
  rcases h with ⟨h₁,h₂,h₃,h₄⟩
  exact ⟨hs.trans h₁,h₂.trans hb,hs.trans h₃,h₄.trans hb⟩

lemma width_nonneg : 0 ≤ C.width := by
  have hB : 0 ≤ C.B - 1 := by have := C.B_pos; omega
  have hS := C.S_nonneg
  dsimp [width]
  positivity

lemma small_width_le : (C.d : ℤ) + (C.B - 1) * C.S ≤ C.width := by
  dsimp [width]
  omega

lemma searches_congr {f g : ℤ → Alphabet} {s b z : ℤ}
    (hv : C.Visible s b z) (he : AgreesOn f g s b) :
    C.small f z = C.small g z ∧ C.large f z = C.large g z := by
  have hw := C.small_width_le
  rcases hv with ⟨hv₁,hv₂,hv₃,hv₄⟩
  constructor
  · apply EndSearch.search_local C.rule
    intro x hx hx'
    exact he x (by omega) (by omega)
  · apply EndSearch.search_local C.rule
    intro x hx hx'
    exact he x (by dsimp [width] at hv₁; omega) (by dsimp [width] at hv₂; omega)

lemma seed_pos : 0 < C.K := lt_of_le_of_lt (Nat.zero_le _) C.seed_long

lemma seed_square : (C.d : ℤ) ^ 2 ≤ C.K := by
  have hh := C.seed_long
  have hn : C.d ^ 2 ≤ C.K := by omega
  exact_mod_cast hn

def complete (lag : ℤ) : Language Alphabet :=
  {w | ∃ f : ℤ → Alphabet, Realizes w 0 f ∧
    C.Visible 0 w.length (lag + C.offset) ∧
    EndAt C.d C.K C.tail f (lag + C.offset) (C.small f (lag + C.offset)) w.length}

lemma not_nil (lag : ℤ) : [] ∉ C.complete lag := by
  rintro ⟨f,hf,hv,he⟩
  have hp := C.seed_pos
  have h₁ := hv.2.2.1
  have h₂ := hv.2.2.2
  simp only [List.length_nil, Nat.cast_zero] at h₁ h₂
  omega

lemma prefix_code (lag : ℤ) : EpisodeAlgebra.PrefixCode (C.complete lag) := by
  refine ⟨C.not_nil lag, ?_⟩
  rintro u ⟨f,hf,hvf,hu⟩ v ⟨g,hg,hvg,hv⟩ hp
  have hl := hp.length_le
  have he : AgreesOn f g 0 (u.length : ℤ) := by simpa using hf.agrees hg hp
  have hη := (C.searches_congr hvf he).1
  have hmin : min (u.length : ℤ) (v.length : ℤ) = u.length := min_eq_left (by exact_mod_cast hl)
  have hseed : 0 ≤ (lag + C.offset) ∧ (lag + C.offset) + C.K ≤ min (u.length : ℤ) v.length ∧
      0 ≤ (lag + C.offset) ∧ (lag + C.offset) + C.K ≤ min (u.length : ℤ) v.length := by
    rw [hmin]
    exact ⟨hvf.2.2.1,hvf.2.2.2,hvf.2.2.1,hvf.2.2.2⟩
  have heq := shared_end C.tail_pos (by simpa using C.seed_square)
    (by simpa using C.seed_pos) hseed (by simpa [hmin] using he) hu (hη ▸ hv)
  exact hp.eq_of_length (by exact_mod_cast heq)

def Guard (O : Finset ℤ) (reference s b : ℤ) (f : ℤ → Alphabet) : Prop :=
  reference ∈ O ∧ (∀ t ∈ O, C.Visible s b (t + C.offset)) ∧
    (∀ t ∈ O, C.small f (t + C.offset) = C.small f (reference + C.offset) ∧
      C.large f (t + C.offset) = C.large f (reference + C.offset)) ∧
    EndAt C.d C.K C.tail f (reference + C.offset)
      (C.small f (reference + C.offset)) b

lemma guard_shared_end {O : Finset ℤ} {reference t s b b' : ℤ}
    {f g : ℤ → Alphabet}
    (ht : t ∈ O) (hguard : C.Guard O reference s b' g)
    (hvis : ∀ t' ∈ O, C.Visible s b (t' + C.offset))
    (he : AgreesOn f g s (min b b'))
    (hover : (C.d : ℤ)^2 ≤ (C.K : ℤ) - |t - reference|)
    (hover' : |t - reference| < C.K)
    (hend : EndAt C.d C.K C.tail f (t + C.offset) (C.small f (t + C.offset)) b) :
    b = b' ∧ clockAnchor (C.large f (t + C.offset)) b C.tail =
      clockAnchor (C.large g (reference + C.offset)) b' C.tail := by
  have hvt := hvis t ht
  have hvt' := hguard.2.1 t ht
  have hvr := hvis reference hguard.1
  have hvr' := hguard.2.1 reference hguard.1
  have hvtmin : C.Visible s (min b b') (t + C.offset) := by
    exact ⟨hvt.1, le_min hvt.2.1 hvt'.2.1, hvt.2.2.1, le_min hvt.2.2.2 hvt'.2.2.2⟩
  have hsearch := C.searches_congr hvtmin he
  have hη := hsearch.1.trans (hguard.2.2.1 t ht).1
  have hζ := hsearch.2.trans (hguard.2.2.1 t ht).2
  have hseed : s ≤ t + C.offset ∧ t + C.offset + C.K ≤ min b b' ∧
      s ≤ reference + C.offset ∧ reference + C.offset + C.K ≤ min b b' :=
    ⟨hvt.2.2.1, le_min hvt.2.2.2 hvt'.2.2.2,
      hvr.2.2.1, le_min hvr.2.2.2 hvr'.2.2.2⟩
  have hh : (t + C.offset) - (reference + C.offset) = t - reference := by ring
  have hb := shared_end C.tail_pos (by simpa only [hh] using hover)
    (by simpa only [hh] using hover') hseed he hend (hη ▸ hguard.2.2.2)
  exact ⟨hb, by rw [hb,hζ]⟩

lemma guard_available {O : Finset ℤ} {reference t s b : ℤ} {f : ℤ → Alphabet}
    (hr : reference ∈ O)
    (hvis : ∀ t' ∈ O, C.Visible s b (t' + C.offset))
    (hstable : ∀ t' ∈ O, C.small f (t' + C.offset) = C.small f (t + C.offset) ∧
      C.large f (t' + C.offset) = C.large f (t + C.offset))
    (hover : (C.d : ℤ)^2 ≤ (C.K : ℤ) - |t - reference|)
    (hover' : |t - reference| < C.K)
    (hend : EndAt C.d C.K C.tail f (t + C.offset) (C.small f (t + C.offset)) b) :
    C.Guard O reference s b f := by
  have href := hstable reference hr
  refine ⟨hr,hvis,fun t' ht' => ⟨(hstable t' ht').1.trans href.1.symm,
    (hstable t' ht').2.trans href.2.symm⟩, ?_⟩
  rw [href.1]
  have hh : (t + C.offset) - (reference + C.offset) = t - reference := by ring
  apply transfer_end (by simpa only [hh] using hover) (by simpa only [hh] using hover')
    (h := hend)
  intro hn
  apply EndSearch.absent_continuation C.rule (by nlinarith [C.seed_long]) C.B_pos C.S_nonneg
  exact href.1.trans hn

end Parameters

end CanonicalEpisodes

end GeneralizedStarHeight

end OAI
