import OAI.GroupTheory.RightAngledArtin.TraceWords

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
namespace TraceWords
variable {V : Type*} (L : SimpleGraph V)
/-! Right descents and the cubes in the actual Artin Cayley graph. -/

section CubeDescents
open Classical
variable {L}

theorem Equivalent.extract {x : Letter V} {w w' v : Word V}
    (hs : Equivalent L w w') (he : Extract L x w v) :
    ∃ v', Extract L x w' v' ∧ Equivalent L v v' := by
  have hh : Relation.ReflTransGen (Swap L) w w' := by
    rwa [← Relation.EqvGen.eqvGen_eq_reflTransGen]
  clear hs
  induction hh with
  | refl => exact ⟨_,he,.refl _⟩
  | tail _ hs ih =>
      obtain ⟨v',he',hv'⟩ := ih
      obtain ⟨v'',he'',hv''⟩ := he'.swap hs
      exact ⟨_,he'',hv'.trans hv''⟩

theorem Swap.reverse {w v : Word V} (h : Swap L w v) :
    Equivalent L w.reverse v.reverse := by
  induction h with
  | @head x y w h =>
      simpa only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]
        using Equivalent.append_left (Relation.EqvGen.rel _ _ (Swap.head (w := []) h.symm)) w.reverse
  | cons x _ ih =>
      simpa only [List.reverse_cons] using ih.append_right [x]

theorem Equivalent.reverse {w v : Word V} (h : Equivalent L w v) :
    Equivalent L w.reverse v.reverse := by
  induction h with
  | rel _ _ h => exact h.reverse
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- Distinct accessible occurrences commute. In particular two opposite signs
of the same vertex can never both be accessible. -/
theorem Extract.eq_or_independent {x y : Letter V} {w u v : Word V}
    (hx : Extract L x w u) (hy : Extract L y w v) :
    x = y ∨ Independent L x y := by
  induction hx generalizing v with
  | head w =>
      cases hy with
      | head => exact Or.inl rfl
      | cons h _ => exact Or.inr h.symm
  | @cons a w u ha hx ih =>
      cases hy with
      | head => exact Or.inr ha
      | cons _ hy => exact ih hy

variable (L)
def RightExtract (x : Letter V) (w v : Word V) : Prop :=
  Extract L x w.reverse v.reverse

variable {L}
theorem RightExtract.equivalent {x : Letter V} {w v : Word V}
    (h : RightExtract L x w v) : Equivalent L w (v ++ [x]) := by
  simpa only [List.reverse_reverse,List.reverse_cons] using (Extract.equivalent h).reverse

theorem RightExtract.of_equivalent {x : Letter V} {w v : Word V}
    (h : Equivalent L w (v ++ [x])) : ∃ u, RightExtract L x w u ∧ Equivalent L u v := by
  obtain ⟨u,hu,hue⟩ := h.reverse.symm.extract (by
    simpa only [List.reverse_append,List.reverse_singleton,List.singleton_append]
      using (Extract.head (L := L) (x := x) v.reverse))
  exact ⟨u.reverse,by simpa [RightExtract] using hu,by simpa using hue.symm.reverse⟩

theorem RightExtract.length {x : Letter V} {w v : Word V}
    (h : RightExtract L x w v) : v.length + 1 = w.length := by
  simpa [RightExtract] using Extract.length h

theorem RightExtract.eq_or_independent {x y : Letter V} {w u v : Word V}
    (hx : RightExtract L x w u) (hy : RightExtract L y w v) :
    x = y ∨ Independent L x y := Extract.eq_or_independent hx hy

theorem RightExtract.diamond {x y : Letter V} {w u v : Word V}
    (hxy : Independent L x y) (hx : RightExtract L x w u) (hy : RightExtract L y w v) :
    ∃ t, RightExtract L y u t ∧ RightExtract L x v t := by
  obtain ⟨t,ht,h't⟩ := Extract.diamond hxy hx hy
  exact ⟨t.reverse,by simpa [RightExtract] using ht,by simpa [RightExtract] using h't⟩


variable (L)
/-- A maximal occurrence of a trace, retaining its sign. -/
def EndsWith (t : Trace L) (x : Letter V) : Prop :=
  ∃ u, t = appendTrace L u (ofWord L [x])

def artinLength (g : ArtinGroup L) : ℕ := traceLength L (artinNormalTrace L g)

def rightDescents (g : ArtinGroup L) : Set (Letter V) :=
  {x | EndsWith L (artinNormalTrace L g) x}

variable {L}
theorem endsWith_ofWord_iff (w : Word V) (x : Letter V) :
    EndsWith L (ofWord L w) x ↔ ∃ v, RightExtract L x w v := by
  constructor
  · rintro ⟨t,ht⟩
    induction t using Quotient.inductionOn with
    | h v =>
        obtain ⟨u,hu,_⟩ := RightExtract.of_equivalent ((ofWord_eq L).mp ht)
        exact ⟨u,hu⟩
  · rintro ⟨v,hv⟩
    exact ⟨ofWord L v,(ofWord_eq L).mpr hv.equivalent⟩

theorem endsWith_append_independent (t : Trace L) {x y : Letter V}
    (hxy : Independent L x y) :
    EndsWith L (appendTrace L t (ofWord L [x])) y ↔ EndsWith L t y := by
  induction t using Quotient.inductionOn with
  | h w =>
      change EndsWith L (ofWord L (w ++ [x])) y ↔ EndsWith L (ofWord L w) y
      rw [endsWith_ofWord_iff,endsWith_ofWord_iff]
      constructor
      · rintro ⟨v,hv⟩
        have hv' : Extract L y (x :: w.reverse) v.reverse := by
          simpa [RightExtract] using hv
        generalize hvv : v.reverse = u at hv'
        cases hv' with
        | head => exact False.elim (independent_self L x hxy)
        | @cons _ _ u _ hu =>
            exact ⟨u.reverse,by simpa [RightExtract] using hu⟩
      · rintro ⟨v,hv⟩
        refine ⟨v ++ [x],?_⟩
        simpa [RightExtract] using Extract.cons hxy.symm hv

variable (L)
theorem artinLength_word {w : Word V} (h : Reduced L (ofWord L w)) :
    artinLength L (wordEval (artinGenerator L) w) = w.length := by
  simp only [artinLength,artinNormalTrace_word,h.normalTrace_eq,traceLength_ofWord]

theorem rightDescents_word {w : Word V} (h : Reduced L (ofWord L w)) (x : Letter V) :
    x ∈ rightDescents L (wordEval (artinGenerator L) w) ↔ ∃ v, RightExtract L x w v := by
  change EndsWith L (artinNormalTrace L _) x ↔ _
  rw [artinNormalTrace_word,h.normalTrace_eq,endsWith_ofWord_iff]

/-- The whole descending link is a clique, not just its pairwise choices. -/
theorem rightDescents_pairwise (g : ArtinGroup L) :
    (rightDescents L g).Pairwise (Independent L) := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  intro x hx y hy hne
  obtain ⟨u,hu⟩ := (rightDescents_word L hw x).mp hx
  obtain ⟨v,hv⟩ := (rightDescents_word L hw y).mp hy
  exact (hu.eq_or_independent hv).resolve_left hne

theorem rightDescents_length (g : ArtinGroup L) (x : Letter V) :
    x ∈ rightDescents L g ↔
      artinLength L (g * letterValue (artinGenerator L) (invLetter x)) + 1 = artinLength L g := by
  constructor
  · obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
    intro hx
    obtain ⟨v,hv⟩ := (rightDescents_word L hw x).mp hx
    have he := hv.equivalent
    have hvred := (hw.of_equivalent he).of_append_right
    have heval := he.wordEval (fun _ _ h => adjacent_generators_commute L h)
    rw [wordEval_append,wordEval_singleton] at heval
    rw [heval,letterValue_inverse,mul_inv_cancel_right,artinLength_word L hvred]
    rw [← heval,artinLength_word L hw]
    exact hv.length
  · intro hl
    rcases artinNormalTrace_right_step L g (invLetter x) with ht | ht
    · have := congrArg (traceLength L) ht
      rw [traceLength_append_singleton] at this
      change artinLength L _ = artinLength L _ + 1 at this
      omega
    · exact ⟨_,by simpa only [invLetter_invLetter] using ht⟩

/-- Crossing one cube direction does not change the descent status of any
independent direction. This is the no-local-maximum obstruction needed for the
length filtration of the universal cubical complex. -/
theorem descent_independent_step (g : ArtinGroup L) {x y : Letter V}
    (hxy : Independent L x y) :
    y ∈ rightDescents L (g * letterValue (artinGenerator L) x) ↔ y ∈ rightDescents L g := by
  change EndsWith L (artinNormalTrace L _) y ↔ EndsWith L (artinNormalTrace L g) y
  rcases artinNormalTrace_right_step L g x with ht | ht
  · rw [ht,endsWith_append_independent _ hxy]
  · rw [ht,endsWith_append_independent _ (show Independent L (invLetter x) y from hxy)]

theorem artinLength_eq_zero_iff (g : ArtinGroup L) : artinLength L g = 0 ↔ g = 1 := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  rw [artinLength_word L hw]
  constructor
  · intro h
    have : w = [] := by simpa using h
    simp [this]
  · intro h
    have hh := (artin_word_eq_iff L w []).mp (by simpa using h)
    rw [hw.normalTrace_eq] at hh
    have he : ofWord L w = ofWord L [] := hh.trans (by
      apply Reduced.normalTrace_eq
      intro t ht
      have := ht.length
      simp only [traceLength_ofWord,List.length_nil] at this
      omega)
    exact (congrArg (traceLength L) he)

theorem rightDescents_nonempty {g : ArtinGroup L} (hg : g ≠ 1) :
    (rightDescents L g).Nonempty := by
  obtain ⟨w,hw,rfl⟩ := exists_reduced_word L g
  have hwne : w ≠ [] := by intro h; apply hg; simp [h]
  obtain ⟨v,x,rfl⟩ : ∃ (v : Word V) (x : Letter V), w = v ++ [x] := by
    cases he : w.reverse with
    | nil => exact False.elim (hwne (by simpa using congrArg List.reverse he))
    | cons x v => exact ⟨v.reverse,x,by simpa using congrArg List.reverse he⟩
  refine ⟨x,(rightDescents_word L hw x).mpr ⟨v,?_⟩⟩
  simp only [RightExtract,List.reverse_append,List.reverse_singleton,List.singleton_append]
  exact .head _


/-- The exact length increment of one generator, with no chosen normal word. -/
theorem artinLength_step (g : ArtinGroup L) (x : Letter V) :
    (artinLength L (g * letterValue (artinGenerator L) x) : ℤ) =
      artinLength L g + if invLetter x ∈ rightDescents L g then -1 else 1 := by
  by_cases hx : invLetter x ∈ rightDescents L g
  · have hh := (rightDescents_length L g (invLetter x)).mp hx
    simp only [invLetter_invLetter] at hh
    simp only [ite_eq_left hx]
    omega
  · simp only [ite_eq_right hx]
    rcases artinNormalTrace_right_step L g x with ht | ht
    · have hh := congrArg (traceLength L) ht
      rw [traceLength_append_singleton] at hh
      change artinLength L _ = artinLength L _ + 1 at hh
      omega
    · exact False.elim (hx ⟨_,ht⟩)

theorem descent_word_invariant (g : ArtinGroup L) (w : Word V) (y : Letter V)
    (hw : ∀ x ∈ w, Independent L x y) :
    y ∈ rightDescents L (g * wordEval (artinGenerator L) w) ↔ y ∈ rightDescents L g := by
  induction w generalizing g with
  | nil => simp
  | cons x w ih =>
      rw [wordEval_cons,← mul_assoc,ih _ (fun z hz => hw z (by simp [hz]))]
      exact descent_independent_step L g (hw x (by simp))

/-- On a cube, length is affine: every coordinate has increment +1 or -1,
and independent crossings cannot change that increment. -/
theorem artinLength_clique_word (g : ArtinGroup L) (w : Word V)
    (hw : w.Pairwise (Independent L)) :
    (artinLength L (g * wordEval (artinGenerator L) w) : ℤ) = artinLength L g +
      (w.map fun x => if invLetter x ∈ rightDescents L g then (-1 : ℤ) else 1).sum := by
  induction w generalizing g with
  | nil => simp
  | cons x w ih =>
      obtain ⟨hx,hw⟩ := List.pairwise_cons.mp hw
      rw [wordEval_cons,← mul_assoc,ih _ hw,artinLength_step]
      have he : (w.map fun y => if invLetter y ∈ rightDescents L
          (g * letterValue (artinGenerator L) x) then (-1 : ℤ) else 1) =
          w.map fun y => if invLetter y ∈ rightDescents L g then (-1 : ℤ) else 1 := by
        apply List.map_congr_left
        intro y hy
        rw [descent_independent_step L g (show Independent L x (invLetter y) from hx y hy)]
      rw [he]
      simp only [List.map_cons,List.sum_cons]
      omega

/-- Every face of the full descending cube has precisely the expected length.
This proves in particular that its corners are different from its top. -/
theorem artinLength_descending_cube (g : ArtinGroup L) (w : Word V)
    (hw : w.Pairwise (Independent L)) (hd : ∀ x ∈ w, x ∈ rightDescents L g) :
    artinLength L (g * wordEval (artinGenerator L) (w.map invLetter)) + w.length =
      artinLength L g := by
  have hwi : (w.map invLetter).Pairwise (Independent L) := by
    simpa only [List.pairwise_map,independent_inv_left,independent_inv_right] using hw
  have hh := artinLength_clique_word L g (w.map invLetter) hwi
  have hsum : ((w.map invLetter).map fun x =>
      if invLetter x ∈ rightDescents L g then (-1 : ℤ) else 1).sum = -(w.length : ℤ) := by
    rw [List.map_map]
    simp only [Function.comp_def]
    have he : w.map (fun x => if invLetter (invLetter x) ∈ rightDescents L g then (-1 : ℤ) else 1) =
      w.map (fun _ => (-1 : ℤ)) := by
      apply List.map_congr_left
      intro x hx
      simp only [invLetter_invLetter,ite_eq_left (hd x hx)]
    rw [he]
    simp
  rw [hsum] at hh
  omega

end CubeDescents
end TraceWords
end EilenbergGanea

end

end OAI
