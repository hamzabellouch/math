import OAI.Computability.StarHeight.StreamSplicing

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uAlphabet2 uAlphabet3 uJ uC uAlphabet4 uJ2
universe uC2 uP uAlphabet5 uM2

namespace StreamShift

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet}

def shift (f : ℤ → Alphabet) (a : ℤ) : ℤ → Alphabet := fun x => f (x-a)

@[simp] lemma shift_add (f : ℤ → Alphabet) (a x : ℤ) : shift f a (x+a)=f x := by
  simp only [shift,add_sub_cancel_right]

lemma map_injective (a : ℤ) : Function.Injective (Option.map (fun x : ℤ => x+a)) := by
  intro x y h
  cases x <;> cases y <;> simp_all

lemma map_none (a : ℤ) (x : Option ℤ) : x.map (fun x => x+a)=none ↔ x=none := by
  cases x <;> simp

lemma realizes {w : List Alphabet} {f : ℤ → Alphabet} {s : ℤ}
    (hf : Realizes w s f) (a : ℤ) : Realizes w (s+a) (shift f a) := by
  intro i
  simpa only [shift,show s+a+(i.val:ℤ)-a=s+i.val by ring] using hf i

lemma piece (f : ℤ → Alphabet) (s t a : ℤ) :
    WordIntervals.piece (shift f a) (s+a) (t+a)=WordIntervals.piece f s t := by
  unfold WordIntervals.piece WordIntervals.segment
  simp only [add_sub_add_right_eq_sub]
  apply List.ofFn_inj.mpr
  funext i
  simp only [shift,Fin.val_cast,show s+a+(i.val:ℤ)-a=s+i.val by ring]

lemma product {M : Type uM} [Monoid M] (T : FreeMonoid Alphabet →* M)
    (f : ℤ → Alphabet) (s t a : ℤ) :
    WordIntervals.product T (shift f a) (s+a) (t+a)=WordIntervals.product T f s t :=
  congrArg T (piece f s t a)

lemma markers {d K : ℕ} (R : Rule Alphabet d K) (f : ℤ → Alphabet) (a x : ℤ) :
    x∈R.markers (shift f a) ↔ x-a∈R.markers f := by
  change x∈R.markers (fun i => f (i-a)) ↔ x-a∈R.markers f
  simpa only [sub_eq_add_neg] using R.translate f (-a) x

lemma marker_search {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S) (l r : ℤ) :
    MarkerSearch.search S' (l+a) (r+a)=(MarkerSearch.search S l r).map (fun x => x+a) := by
  cases he : MarkerSearch.search S l r with
  | none =>
    simp only [Option.map_none]
    apply MarkerSearch.search_none.mpr
    intro m hm hl hr
    exact MarkerSearch.search_none.mp he (m-a) ((hS m).mp hm) (by omega) (by omega)
  | some q =>
    simp only [Option.map_some]
    obtain ⟨⟨hq,hlo,hmin⟩,hhi⟩ := MarkerSearch.search_some.mp he
    apply MarkerSearch.search_some.mpr
    refine ⟨⟨(hS _).mpr (by simpa only [add_sub_cancel_right] using hq),by omega,?_⟩,by omega⟩
    intro m hm hl
    have hh := hmin (m-a) ((hS m).mp hm) (by omega)
    omega

lemma end_search {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S)
    {B D : ℤ} (hB : 0<B) (hD : 0≤D) (c z : ℤ) :
    EndSearch.search S' B D c (z+a)=(EndSearch.search S B D c z).map (fun x => x+a) := by
  have he (m : ℤ) : EndSearch.Eligible S' B D c (z+a) m ↔
      EndSearch.Eligible S B D c z (m-a) := by
    simp only [EndSearch.Eligible,hS,show m-(z+a)=m-a-z by ring]
  cases hs : EndSearch.search S B D c z with
  | none =>
    simp only [Option.map_none]
    apply (EndSearch.search_none hB hD).mpr
    intro m hm
    exact (EndSearch.search_none hB hD).mp hs (m-a) ((he m).mp hm)
  | some q =>
    simp only [Option.map_some]
    obtain ⟨hq,hmin⟩ := (EndSearch.search_some hB hD).mp hs
    apply (EndSearch.search_some hB hD).mpr
    refine ⟨(he _).mpr (by simpa only [add_sub_cancel_right] using hq),?_⟩
    intro m hm
    have hh := hmin (m-a) ((he m).mp hm)
    omega

lemma agrees {f v : ℤ → Alphabet} {s b : ℤ} (hf : AgreesOn f v s b) (a : ℤ) :
    AgreesOn (shift f a) (shift v a) (s+a) (b+a) := by
  intro x hx hx'
  exact hf (x-a) (by omega) (by omega)

lemma continuation {d K : ℕ} {f v : ℤ → Alphabet} {z : ℤ}
    (hv : ShortContinuation d K f z v) (a : ℤ) :
    ShortContinuation d K (shift f a) (z+a) (shift v a) := by
  obtain ⟨⟨p,hp,hpd,hper⟩,hv⟩ := hv
  refine ⟨⟨p,hp,hpd,?_⟩,?_⟩
  · intro x
    simpa only [shift,show x+(p:ℤ)-a=(x-a)+p by ring] using hper (x-a)
  · simpa only [show z+(K:ℤ)+a=z+a+K by ring] using agrees hv a

lemma mismatch {K : ℕ} {f v : ℤ → Alphabet} {z q : ℤ}
    (hm : EpisodeEnd.FirstMismatch f v z K q) (a : ℤ) :
    EpisodeEnd.FirstMismatch (shift f a) (shift v a) (z+a) K (q+a) := by
  refine ⟨by have := hm.1;omega,?_,agrees hm.2.2 a⟩
  simpa only [shift_add] using hm.2.1

lemma ending {d K : ℕ} {tail z b : ℤ} {f : ℤ → Alphabet} {op : Option ℤ}
    (he : EpisodeEnd.EndAt d K tail f z op b) (a : ℤ) :
    EpisodeEnd.EndAt d K tail (shift f a) (z+a) (op.map (fun x => x+a)) (b+a) := by
  cases op with
  | some q => dsimp [EpisodeEnd.EndAt] at he ⊢;omega
  | none =>
    obtain ⟨v,hv,hm⟩ := he
    refine ⟨shift v a,continuation hv a,?_⟩
    simpa only [show b-tail+a=b+a-tail by ring] using mismatch hm a

lemma inner_failure {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S) (z H w E : ℤ) :
    MarkerSearch.InnerFailure S' (z+a) H w E ↔ MarkerSearch.InnerFailure S z H w E := by
  have hs (v : ℤ) : MarkerSearch.search S' (z+a+v) (z+a+H+v)=
      (MarkerSearch.search S (z+v) (z+H+v)).map (fun x => x+a) := by
    rw [show z+a+v=(z+v)+a by ring,show z+a+H+v=(z+H+v)+a by ring]
    exact marker_search a hS (z+v) (z+H+v)
  have hz : MarkerSearch.search S' (z+a) (z+a+H)=
      (MarkerSearch.search S z (z+H)).map (fun x => x+a) := by
    rw [show z+a+H=(z+H)+a by ring]
    exact marker_search a hS z (z+H)
  unfold MarkerSearch.InnerFailure
  rw [hz]
  apply or_congr
  · apply exists_congr
    intro v
    rw [hs]
    exact and_congr_right (fun _ => not_congr (map_injective a).eq_iff)
  · rw [map_none]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨m,hm,hl,hr⟩
      exact ⟨m-a,(hS m).mp hm,by omega,by omega⟩
    · rintro ⟨m,hm,hl,hr⟩
      exact ⟨m+a,(hS _).mpr (by simpa only [add_sub_cancel_right] using hm),by omega,by omega⟩

lemma unstable {S S' : Set ℤ} (a : ℤ) (hS : ∀ x, x∈S' ↔ x-a∈S)
    {B D : ℤ} (hB : 0<B) (hD : 0≤D) (c z w : ℤ) :
    EndSearch.Unstable S' B D c (z+a) w ↔ EndSearch.Unstable S B D c z w := by
  unfold EndSearch.Unstable
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [end_search a hS hB hD c z]
  have hs := end_search a hS hB hD c (z+v)
  rw [show z+v+a=z+a+v by ring] at hs
  rw [hs]
  exact not_congr (map_injective a).eq_iff

end StreamShift

namespace CanonicalEpisodes.Parameters

open StreamShift EpisodeEnd
variable {Alphabet : Type uAlphabet2} (C : CanonicalEpisodes.Parameters Alphabet)

lemma small_shift (f : ℤ → Alphabet) (a z : ℤ) :
    C.small (shift f a) (z+a)=(C.small f z).map (fun x => x+a) :=
  end_search a (markers C.rule f a) C.B_pos C.S_nonneg C.d z

lemma large_shift (f : ℤ → Alphabet) (a z : ℤ) :
    C.large (shift f a) (z+a)=(C.large f z).map (fun x => x+a) :=
  end_search a (markers C.rule f a) C.B_pos C.S_nonneg (3*C.d) z

lemma visible_shift {s b z : ℤ} (hv : C.Visible s b z) (a : ℤ) :
    C.Visible (s+a) (b+a) (z+a) := by
  rcases hv with ⟨h₁,h₂,h₃,h₄⟩
  exact ⟨by omega,by omega,by omega,by omega⟩

lemma end_shift {f : ℤ → Alphabet} {z b : ℤ}
    (he : EndAt C.d C.K C.tail f z (C.small f z) b) (a : ℤ) :
    EndAt C.d C.K C.tail (shift f a) (z+a) (C.small (shift f a) (z+a)) (b+a) := by
  rw [C.small_shift]
  exact ending he a

lemma guard_shift {O : Finset ℤ} {reference s b : ℤ} {f : ℤ → Alphabet}
    (hg : C.Guard O reference s b f) (a : ℤ) :
    C.Guard (O.image (fun x => x+a)) (reference+a) (s+a) (b+a) (shift f a) := by
  refine ⟨Finset.mem_image.mpr ⟨reference,hg.1,rfl⟩,?_,?_,?_⟩
  · intro t ht
    obtain ⟨t',ht',rfl⟩ := Finset.mem_image.mp ht
    simpa only [show t'+C.offset+a=t'+a+C.offset by ring] using C.visible_shift (hg.2.1 t' ht') a
  · intro t ht
    obtain ⟨t',ht',rfl⟩ := Finset.mem_image.mp ht
    have he := hg.2.2.1 t' ht'
    rw [show t'+a+C.offset=t'+C.offset+a by ring,
      show reference+a+C.offset=reference+C.offset+a by ring,C.small_shift,C.small_shift,
      C.large_shift,C.large_shift,he.1,he.2]
    exact ⟨rfl,rfl⟩
  · simpa only [show reference+C.offset+a=reference+a+C.offset by ring] using C.end_shift hg.2.2.2 a

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

open StreamShift
variable {Alphabet : Type uAlphabet3} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma inner_shift (f : ℤ → Alphabet) (j : J) (u : Fin A.B) (t a : ℤ) :
    A.inner (shift f a) j u (t+a)=(A.inner f j u t).map (fun x => x+a) := by
  unfold inner
  rw [show t+a+A.offset j=(t+A.offset j)+a by ring,
    show t+A.offset j+a+A.H u=(t+A.offset j+A.H u)+a by ring]
  exact marker_search a (markers A.innerRule f a) (t+A.offset j) (t+A.offset j+A.H u)

lemma anchor_shift (f : ℤ → Alphabet) (q t a : ℤ) :
    A.anchor (shift f a) (q+a) (t+a)=A.anchor f q t+a := by
  unfold anchor
  rw [show t+a+A.endRule.offset=t+A.endRule.offset+a by ring,A.endRule.large_shift]
  cases A.endRule.large f (t+A.endRule.offset) <;> rfl

lemma innerVisible_shift {s b t : ℤ} {j : J} {u : Fin A.B}
    (hv : A.InnerVisible s b t j u) (a : ℤ) : A.InnerVisible (s+a) (b+a) (t+a) j u := by
  rcases hv with ⟨hl,hr⟩
  exact ⟨by omega,by omega⟩

lemma visible_shift {s b t Q : ℤ} (hv : A.Visible s b t Q) (a : ℤ) :
    A.Visible (s+a) (b+a) (t+a) (Q+a) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [show t+A.endRule.offset+a=t+a+A.endRule.offset by ring] using A.endRule.visible_shift hv.base a
  · intro v hd hw
    obtain ⟨hl,hr⟩ := hv.ends v hd hw
    exact ⟨by omega,by omega⟩
  · intro j
    obtain ⟨hl,hr⟩ := hv.inner j
    simp only [add_sub_add_right_eq_sub]
    exact ⟨by omega,by omega⟩

lemma failed_shift (f : ℤ → Alphabet) (t Q a : ℤ) :
    A.Failed (shift f a) (t+a) (Q+a) ↔ A.Failed f t Q := by
  have hb : (0:ℤ)<A.B := by exact_mod_cast A.B_pos
  unfold Failed Z Star
  rw [show t+a+A.endRule.offset=t+A.endRule.offset+a by ring,
    unstable a (markers A.endRule.rule f a) hb A.endRule.S_nonneg,
    unstable a (markers A.endRule.rule f a) hb A.endRule.S_nonneg]
  simp only [add_sub_add_right_eq_sub]
  apply or_congr_right
  apply or_congr_right
  apply exists_congr
  intro j
  rw [show t+a+A.offset j=t+A.offset j+a by ring]
  exact inner_failure a (markers A.innerRule f a) _ _ _ _

end ExceptionalOrigins.Parameters

namespace SuffixDecoder

open StreamShift
variable {Alphabet : Type uAlphabet4} {J : Type uJ2} {C : Type uC2} {P : Type uP}
    (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma test_shift {τ : P → ℤ} {reference decoded : P} {k b : ℤ} {f : ℤ → Alphabet}
    (ht : Test A τ reference k b f decoded) (a : ℤ) :
    Test A (fun i => τ i+a) reference (k+a) (b+a) (shift f a) decoded := by
  have ha (i : P) : A.anchor (shift f a) (b+a-A.endRule.tail) (τ i+a)=
      A.anchor f (b-A.endRule.tail) (τ i)+a := by
    rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift]
  have hs (i : P) : A.endRule.small (shift f a) (τ i+a+A.endRule.offset)=
      (A.endRule.small f (τ i+A.endRule.offset)).map (fun x => x+a) := by
    rw [show τ i+a+A.endRule.offset=τ i+A.endRule.offset+a by ring,A.endRule.small_shift]
  have hl (i : P) : A.endRule.large (shift f a) (τ i+a+A.endRule.offset)=
      (A.endRule.large f (τ i+A.endRule.offset)).map (fun x => x+a) := by
    rw [show τ i+a+A.endRule.offset=τ i+A.endRule.offset+a by ring,A.endRule.large_shift]
  have hf (i : P) : A.Failed (shift f a) (τ i+a)
      (A.anchor (shift f a) (b+a-A.endRule.tail) (τ i+a)) ↔
      A.Failed f (τ i) (A.anchor f (b-A.endRule.tail) (τ i)) := by
    rw [ha,A.failed_shift]
  refine ⟨?_,?_,⟨(hf decoded).mpr ht.unique.1,fun i hi => ht.unique.2 i ((hf i).mp hi)⟩,?_⟩
  · intro i
    rw [ha]
    exact A.visible_shift (ht.visible i) a
  · intro he
    obtain ⟨i,hi⟩ := he
    rw [hl,map_none] at hi
    obtain ⟨hn,hend⟩ := ht.reference_guard ⟨i,hi⟩
    refine ⟨fun i => ?_,?_⟩
    · rw [hs,hn,Option.map_none]
    · simpa only [show τ reference+A.endRule.offset+a=τ reference+a+A.endRule.offset by ring] using A.endRule.end_shift hend a
  · simpa only [show τ decoded+A.endRule.offset+a=τ decoded+a+A.endRule.offset by ring] using A.endRule.end_shift ht.final_guard a

end SuffixDecoder

namespace BoundarySnapshot

open StreamShift
variable {Alphabet : Type uAlphabet5} {M : Type uM2} [Monoid M] {g : ℕ}

def translated (search : Fin (g+1) → Option ℤ) (a : ℤ) : Fin (g+1) → Option ℤ :=
  fun i => (search i).map (fun x => x+a)

lemma translated_none (search : Fin (g+1) → Option ℤ) (a : ℤ) (i : Fin (g+1)) :
    translated search a i=none ↔ search i=none := map_none a (search i)

lemma translated_position {search : Fin (g+1) → Option ℤ} {i : Fin (g+1)}
    (hi : search i≠none) (a : ℤ) : positions (translated search a) i=positions search i+a := by
  cases hs : search i with
  | none => exact False.elim (hi hs)
  | some q => simp only [positions,translated,hs,Option.map_some,Option.getD_some]

lemma present_shift {search : Fin (g+1) → Option ℤ} {s b : ℤ}
    (hp : Present search s b) (a : ℤ) : Present (translated search a) (s+a) (b+a) := by
  obtain ⟨p,hp,hm,hs,hb⟩ := hp
  exact ⟨fun i => p i+a,fun i => by simp only [translated,hp,Option.map_some],
    (by intro i j hij; have := hm hij; dsimp; omega),(by dsimp;omega),(by dsimp;omega)⟩

lemma present_shift_iff (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    Present (translated search a) (s+a) (b+a) ↔ Present search s b := by
  refine ⟨?_,fun hp => present_shift hp a⟩
  rintro ⟨p,hp,hm,hs,hb⟩
  refine ⟨fun i => p i-a,?_,(by intro i j hij; have := hm hij; dsimp; omega),(by dsimp;omega),(by dsimp;omega)⟩
  intro i
  have hi := hp i
  cases he : search i with
  | none => simp only [translated,he,Option.map_none] at hi;cases hi
  | some q =>
    simp only [translated,he,Option.map_some,Option.some.injEq] at hi
    congr 1
    dsimp
    omega

lemma factors_shift (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    factors T (shift f a) (s+a) (b+a) (translated search a)=factors T f s b search := by
  classical
  by_cases hp : Present search s b
  · obtain ⟨p,hp,hm,hs,hb⟩ := hp
    have hps (i) : translated search a i=some (p i+a) := by simp only [translated,hp,Option.map_some]
    rw [factors_present T (shift f a) hps (by intro i j h; have := hm h; dsimp; omega)
      (by omega) (by omega),factors_present T f hp hm hs hb]
    simp only [StreamShift.product]
  · have hn := mt (present_shift_iff search s b a).mp hp
    simp only [factors,dite_eq_right hp,dite_eq_right hn]

lemma actual_shift (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    actual T (shift f a) (s+a) (b+a) (translated search a)=actual T f s b search := by
  apply ClockAffine.Snapshot.ext (StreamShift.product T f s b a)
  exact factors_shift T f search s b a

lemma later_shift (T : FreeMonoid Alphabet →* M) (f : ℤ → Alphabet)
    (search : Fin (g+1) → Option ℤ) (s b a : ℤ) :
    later T (shift f a) (s+a) (b+a) (translated search a)=later T f s b search := by
  have hp := StreamShift.product T f s b a
  have hf := factors_shift T f search s b a
  cases hl : later T (shift f a) (s+a) (b+a) (translated search a)
  cases hr : later T f s b search
  congr
  · exact (congrArg ClockAffine.Later.tailProduct hl).symm.trans
      (hp.trans (congrArg ClockAffine.Later.tailProduct hr))
  · exact (congrArg ClockAffine.Later.boundaries hl).symm.trans
      (hf.trans (congrArg ClockAffine.Later.boundaries hr))

end BoundarySnapshot

end GeneralizedStarHeight

end OAI
