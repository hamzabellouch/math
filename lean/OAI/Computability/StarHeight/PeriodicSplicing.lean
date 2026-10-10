import OAI.Computability.StarHeight.RegularLanguages

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uAlphabet2 uAlphabet3 uAlphabet4 uAlphabet5 uAlphabet6 uAlphabet7 uJ
universe uC

namespace StreamSplice

open LocalMarkers WordIntervals PeriodicSummary

variable {Alphabet : Type uAlphabet}

lemma periodic_of_dvd {v : ℤ → Alphabet} {p δ : ℤ} (h : Function.Periodic v p)
    (hd : p∣δ) : Function.Periodic v δ := by
  obtain ⟨k,rfl⟩ := hd
  simpa only [Int.cast_id,mul_comm] using h.int_mul k

lemma periodic_pattern {p : ℕ} [NeZero p] {v : ℤ → Alphabet}
    (h : Function.Periodic v (p:ℤ)) (N : ℤ) (i : ℕ) :
    v (N+(((i:ZMod p).val:ℕ):ℤ))=v (N+i) := by
  have he := ZMod.val_intCast (n := p) (i:ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  exact (periodic_remainder h N (N+i) |>.trans (by rw [add_sub_cancel_left])).symm

lemma fits_realizes {p : ℕ} [NeZero p] {v f : ℤ → Alphabet} {N : ℤ} {w : List Alphabet}
    (hp : Function.Periodic v (p:ℤ)) (hf : Realizes w N f) :
    Fits (fun q : ZMod p => v (N+q.val)) 0 w ↔ AgreesOn f v N (N+w.length) := by
  rw [fits_iff]
  simp only [zero_add]
  constructor
  · intro h z hz hz'
    let i : Fin w.length := ⟨(z-N).toNat,by omega⟩
    have hi : N+(i.val:ℤ)=z := by dsimp [i];omega
    rw [←hi,hf i,h i,periodic_pattern hp]
  · intro h i
    rw [←hf i,periodic_pattern hp]
    exact h _ (by omega) (by omega)

namespace Frame

variable {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet} (H : Frame f f' N x y)

include H

lemma symm : Frame f' f N y x := by
  refine ⟨fun z hz => (H.left z hz).symm,H.newMiddle,H.oldMiddle,?_⟩
  intro z hz
  have he := H.right (z-((x.length:ℤ)-y.length)) (by omega)
  rw [show z-((x.length:ℤ)-y.length)-((y.length:ℤ)-x.length)=z by ring] at he
  exact he.symm

include H

lemma agrees_periodic {p : ℕ} [NeZero p] {v : ℤ → Alphabet}
    (hp : Function.Periodic v (p:ℤ))
    (hd : (p:ℤ) ∣ (y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := p) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y)) {z q : ℤ}
    (hz : z≤N) (hq : N+x.length≤q) (ha : AgreesOn f v z q) :
    AgreesOn f' v z (q+((y.length:ℤ)-x.length)) := by
  have hmidx : AgreesOn f v N (N+x.length) := by
    intro t ht ht'
    exact ha t (hz.trans ht) (ht'.trans_le hq)
  have hmidx' := (fits_realizes hp H.oldMiddle).mpr hmidx
  have hmidy := (fits_realizes hp H.newMiddle).mp ((fits_congr hm _ 0).mp hmidx')
  have hδ := periodic_of_dvd hp hd
  intro t ht ht'
  by_cases htN : t<N
  · rw [H.left t htN]
    exact ha t ht (by omega)
  · by_cases htY : t<N+y.length
    · exact hmidy t (by omega) htY
    · rw [H.right t (by omega)]
      rw [ha _ (by omega) (by omega)]
      have he := hδ (t-((y.length:ℤ)-x.length))
      rw [sub_add_cancel] at he
      exact he.symm

lemma mismatch_periodic {p : ℕ} [NeZero p] {v : ℤ → Alphabet}
    (hp : Function.Periodic v (p:ℤ)) (hd : (p:ℤ) ∣ (y.length:ℤ)-x.length)
    {q : ℤ} (hq : N+x.length≤q) :
    f' (q+((y.length:ℤ)-x.length)) ≠ v (q+((y.length:ℤ)-x.length)) ↔ f q ≠ v q := by
  rw [H.right _ (by omega)]
  rw [add_sub_cancel_right,(periodic_of_dvd hp hd) q]

end Frame
end StreamSplice
namespace StreamSplice.Frame

open LocalMarkers WordIntervals EpisodeEnd

variable {Alphabet : Type uAlphabet2} {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y)

lemma short_period_factorial {d K : ℕ} {v : ℤ → Alphabet} {z : ℤ}
    (hv : ShortContinuation d K f z v) : Function.Periodic v (d.factorial:ℤ) := by
  obtain ⟨p,hp,hpd,hper⟩ := hv.1
  apply periodic_of_dvd hper
  exact_mod_cast Nat.dvd_factorial hp hpd.le

include H

lemma endAt_none {d K : ℕ} {tail z b : ℤ}
    (hseed : z+(K:ℤ)≤N) (hb : N+x.length≤b-tail)
    (hd : (d.factorial:ℤ) ∣ (y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (he : EndAt d K tail f z none b) :
    EndAt d K tail f' z none (b+((y.length:ℤ)-x.length)) := by
  obtain ⟨v,hv,hmis⟩ := he
  have : NeZero d.factorial := ⟨Nat.factorial_ne_zero d⟩
  have hp := short_period_factorial hv
  refine ⟨v,(shortCont_congr (H.agrees_left hseed)).mp hv,?_,?_,?_⟩
  · omega
  · have hh := (H.mismatch_periodic hp hd hb).mpr hmis.2.1
    convert hh using 1 <;> congr 1 <;> ring
  · rw [show b+((y.length:ℤ)-x.length)-tail=(b-tail)+((y.length:ℤ)-x.length) by ring]
    exact H.agrees_periodic hp hd hm (by omega) hb hmis.2.2

lemma endAt {C : CanonicalEpisodes.Parameters Alphabet} {z b : ℤ}
    (hvis : C.Visible (-N) N z) (hstrict : z+(C.d:ℤ)+(C.B-1)*C.S<N)
    (hb : N+x.length≤b-C.tail)
    (hd : (C.d.factorial:ℤ) ∣ (y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := C.d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (he : EndAt C.d C.K C.tail f z (C.small f z) b) :
    EndAt C.d C.K C.tail f' z (C.small f' z) (b+((y.length:ℤ)-x.length)) := by
  have hs := (C.searches_congr hvis (H.agrees_left (le_refl N))).1
  rw [←hs]
  cases hη : C.small f z with
  | some q =>
    have hq := (EndSearch.search_some C.B_pos C.S_nonneg).mp hη
    have hw := (EndSearch.width_bounds (x := q-z) (a := C.d) C.B_pos C.S_nonneg).2
    have hbd := (abs_le.mp (hq.1.2.trans hw)).2
    rw [hη] at he
    change b=q+C.tail at he
    omega
  | none =>
    rw [hη] at he
    exact H.endAt_none hvis.2.2.2 hb hd hm he

end StreamSplice.Frame

namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd StreamSplice

variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma exists_horizon (z : ℤ) : ∃ N : ℕ,
    C.Visible (-(N:ℤ)) N z ∧ z+(C.d:ℤ)+(C.B-1)*C.S<N := by
  obtain ⟨N,hN⟩ := exists_nat_gt (|z|+C.width+|C.rule.r|+C.K+1)
  have hz := abs_le.mp (le_refl |z|)
  have hr := abs_le.mp (le_refl |C.rule.r|)
  have hw := C.width_nonneg
  have hs := C.small_width_le
  refine ⟨N,⟨by omega,by omega,by omega,by omega⟩,by omega⟩

lemma visible_long {z : ℤ} {N : ℕ} (h : C.Visible (-(N:ℤ)) N z)
    {b : ℤ} (hb : (N:ℤ)≤b) (hl : 0≤z-C.width-C.rule.r) (hz : 0≤z) :
    C.Visible 0 b z := ⟨hl,h.2.1.trans hb,hz,h.2.2.2.trans hb⟩

lemma complete_regular [Finite Alphabet] (lag : ℤ) : (C.complete lag).IsRegular := by
  classical
  obtain ⟨N,hN,hs⟩ := C.exists_horizon (lag+C.offset)
  let : NeZero C.d.factorial := ⟨Nat.factorial_ne_zero C.d⟩
  let T := (PeriodicSummary.lengthMod C.d.factorial (Alphabet := Alphabet)).prod
    (PeriodicSummary.transition (p := C.d.factorial))
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  let : Fintype (Function.End (Option (ZMod C.d.factorial)))ᵐᵒᵖ :=
    Fintype.ofEquiv (Option (ZMod C.d.factorial) → Option (ZMod C.d.factorial))
      (Equiv.refl _ |>.trans MulOpposite.opEquiv)
  apply FiniteRecognition.regular_sandwich T N C.tail.toNat
  intro a b x y ha hb he
  have hh : C.tail.toNat=C.tail := Int.toNat_of_nonneg C.tail_pos.le
  have trans : ∀ (x y : List Alphabet), T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y) →
      a++x++b∈C.complete lag → a++y++b∈C.complete lag := by
    intro x y he hw
    obtain ⟨f,hf,hv,hend⟩ := hw
    let f' := splice f N x y
    have H : Frame f f' N x y := by simpa only [ha] using splice_frame hf y
    have hnew := H.endAt hN hs (by simp only [List.length_append,Nat.cast_add,ha,hb];omega)
      (PeriodicSummary.lengthMod_dvd (congrArg Prod.fst he)) (congrArg Prod.snd he) hend
    refine ⟨f',?_,?_,?_⟩
    · simpa only [f',ha] using splice_realizes hf y
    · exact C.visible_long hN (by simp only [List.length_append,Nat.cast_add,ha,hb];omega)
        hv.1 hv.2.2.1
    · convert hnew using 1
      simp only [List.length_append,Nat.cast_add]
      omega
  exact ⟨trans x y he,trans y x he.symm⟩

end CanonicalEpisodes.Parameters
namespace EpisodeAlgebra

variable {Alphabet : Type uAlphabet4}

def remainder (E : Language Alphabet) : Language Alphabet :=
  {w | ∀ e∈E, ¬ e <+: w}

lemma remainder_eq (E : Language Alphabet) : remainder E=(E*⊤)ᶜ := by
  ext w
  constructor
  · intro h hw
    obtain ⟨e,he,v,_,rfl⟩ := hw
    exact h e he ⟨v,rfl⟩
  · intro h e he ⟨v,hv⟩
    exact h ⟨e,he,v,Set.mem_univ _,hv⟩

lemma factor_remainder {E : Language Alphabet} (hnil : []∉E) (w : List Alphabet) :
    ∃ es r, AllIn E es ∧ r∈remainder E ∧ w=es.flatten++r := by
  classical
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases h : w∈remainder E
    · exact ⟨[],w,by simp [AllIn],h,by simp⟩
    · change ¬∀ e∈E, ¬ e <+: w at h
      push Not at h
      obtain ⟨e,he,hp⟩ := h
      obtain ⟨v,rfl⟩ := hp
      have hpos : 0<e.length := by
        by_contra h
        exact hnil ((List.length_eq_zero_iff.mp (by omega : e.length=0)) ▸ he)
      obtain ⟨es,r,hes,hr,hv⟩ := ih v.length (by simp only [List.length_append] at hlen;omega) v rfl
      refine ⟨e::es,r,fun a ha => ?_,hr,?_⟩
      · rcases List.mem_cons.mp ha with rfl|ha
        · exact he
        · exact hes a ha
      · simp only [List.flatten_cons,List.append_assoc,hv]

end EpisodeAlgebra

namespace EpisodeEnd

open LocalMarkers
variable {Alphabet : Type uAlphabet5}

lemma firstMismatch_of_disagrees {d K : ℕ} {f v : ℤ → Alphabet} {z q : ℤ}
    (hv : ShortContinuation d K f z v) (hq : z≤q) (hm : f q≠v q) :
    ∃ q', q'≤q ∧ FirstMismatch f v z K q' := by
  rcases MarkerSearch.search_some_or_none {x | f x≠v x} z q with hn|⟨q',hq',hle⟩
  · exact False.elim (hn q hm hq le_rfl)
  · refine ⟨q',hle,?_,hq'.1,?_⟩
    · by_contra h
      exact hq'.1 (hv.2 q' hq'.2.1 (by omega))
    · intro x hx hx'
      by_contra h
      exact (not_le_of_gt hx') (hq'.2.2 x h hx)

end EpisodeEnd

namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd EpisodeAlgebra

variable {Alphabet : Type uAlphabet6} (C : CanonicalEpisodes.Parameters Alphabet)

lemma complete_prefix {lag b : ℤ} {w : List Alphabet} {f : ℤ → Alphabet}
    (hf : Realizes w 0 f) (hv : C.Visible 0 b (lag+C.offset))
    (he : EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b)
    (hb : b≤w.length) : ∃ e∈C.complete lag, e<+:w := by
  have hb0 : 0≤b := hv.2.2.1.trans (le_trans (by omega) hv.2.2.2)
  let e := w.take b.toNat
  have hl : (e.length:ℤ)=b := by
    simp only [e,List.length_take]
    omega
  refine ⟨e,⟨f,hf.prefix (List.take_prefix _ _),?_,?_⟩,List.take_prefix _ _⟩
  · simpa only [hl] using hv
  · simpa only [hl] using he

lemma remainder_middle [Nonempty Alphabet] (lag : ℤ)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b →
      C.Visible 0 b (lag+C.offset)) :
    ∃ N : ℕ, ∀ w∈remainder (C.complete lag),
      w.length≤N+C.tail.toNat ∨ ∃ (f v : ℤ → Alphabet) (p : ℕ),
        Realizes w 0 f ∧ N+C.tail.toNat≤w.length ∧ 0<p ∧ p≤C.d ∧
          Function.Periodic v (p:ℤ) ∧ AgreesOn f v N (w.length-C.tail.toNat) := by
  obtain ⟨N,hN,hs⟩ := C.exists_horizon (lag+C.offset)
  refine ⟨N,?_⟩
  intro w hw
  by_cases hlen : w.length≤N+C.tail.toNat
  · exact Or.inl hlen
  · right
    obtain ⟨f,hf⟩ := realizes_exists w 0
    have htail : (C.tail.toNat:ℤ)=C.tail := Int.toNat_of_nonneg C.tail_pos.le
    have hnone : C.small f (lag+C.offset)=none := by
      cases hη : C.small f (lag+C.offset) with
      | none => rfl
      | some q =>
        have hq := ((EndSearch.search_some C.B_pos C.S_nonneg).mp hη).1.2
        have hwidth := (EndSearch.width_bounds (x := q-(lag+C.offset)) (a := C.d)
          C.B_pos C.S_nonneg).2
        have hright := (abs_le.mp (hq.trans hwidth)).2
        have he : EndAt C.d C.K C.tail f (lag+C.offset)
            (C.small f (lag+C.offset)) (q+C.tail) := by rw [hη];rfl
        obtain ⟨e,he,hp⟩ := C.complete_prefix hf (hvisible f _ he) he (by omega)
        exact False.elim (hw e he hp)
    obtain ⟨v,hv⟩ := EndSearch.absent_continuation C.rule
      (by nlinarith [C.seed_long]) C.B_pos C.S_nonneg hnone
    obtain ⟨p,hp,hpd,hper⟩ := hv.1
    refine ⟨f,v,p,hf,by omega,hp,hpd.le,hper,?_⟩
    intro q hq hq'
    by_contra hm
    have hzq : lag+C.offset≤q := by have := hN.2.2.2;omega
    obtain ⟨q',hle,hm'⟩ := firstMismatch_of_disagrees hv hzq hm
    have he : EndAt C.d C.K C.tail f (lag+C.offset)
        (C.small f (lag+C.offset)) (q'+C.tail) := by
      rw [hnone]
      exact ⟨v,hv,by simpa only [add_sub_cancel_right] using hm'⟩
    obtain ⟨e,he,hpre⟩ := C.complete_prefix hf (hvisible f _ he) he (by omega)
    exact hw e he hpre

lemma remainder_regular [Finite Alphabet] (lag : ℤ) :
    (remainder (C.complete lag)).IsRegular := by
  rw [remainder_eq]
  apply Language.IsRegular.compl
  apply FiniteRecognition.regular_mul (C.complete_regular lag)
  have ht : (⊤ : Language Alphabet)=(0 : Language Alphabet)ᶜ := by
    ext w
    change True ↔ ¬False
    simp
  rw [ht]
  exact Language.IsRegular.compl (FiniteRecognition.regular_finite Set.finite_empty)

lemma remainder_height [Finite Alphabet] [Nonempty Alphabet] (lag : ℤ)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b →
      C.Visible 0 b (lag+C.offset)) :
    HasHeightAtMost (remainder (C.complete lag)) 1 := by
  obtain ⟨N,hN⟩ := C.remainder_middle lag hvisible
  exact PeriodicTemplates.regular_middle_height _ (C.remainder_regular lag)
    (N+C.tail.toNat) N C.tail.toNat C.d hN

end CanonicalEpisodes.Parameters
namespace ExceptionalOrigins.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet7} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma residue_eq_of_dvd {x y : ℤ} (h : (A.B:ℤ)∣y-x) : A.residue x=A.residue y := by
  apply Fin.ext
  have he : x%A.B=y%A.B := Int.modEq_iff_dvd.mpr h
  exact congrArg Int.toNat he

lemma exists_horizon [Fintype J] (D : ℕ) : ∃ N : ℕ, D<N ∧
    ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ Q, A.Visible (-(N:ℤ)) N t Q := by
  let U : ℤ := (SourceSchedule.absoluteBound A.offset:ℤ)
  let H : ℤ := (SourceSchedule.absoluteBound A.H:ℤ)
  obtain ⟨N,hN⟩ := exists_nat_gt ((D:ℤ)+|A.endRule.offset|+A.endRule.width+
    |A.endRule.rule.r|+A.endRule.K+|A.w|+U+H+|A.w₀|+|A.ext|+|A.innerRule.r|+1)
  have hwidth := A.endRule.width_nonneg
  have hU : 0≤U := by dsimp [U];positivity
  have hH : 0≤H := by dsimp [H];positivity
  have hoff := abs_le.mp (le_refl |A.endRule.offset|)
  have hr := abs_le.mp (le_refl |A.endRule.rule.r|)
  have hir := abs_le.mp (le_refl |A.innerRule.r|)
  have hw := abs_le.mp (le_refl |A.w|)
  have hw₀ := abs_le.mp (le_refl |A.w₀|)
  have hext := abs_le.mp (le_refl |A.ext|)
  refine ⟨N,by omega,?_⟩
  intro t ht Q
  have ht' := abs_le.mp ht
  refine ⟨⟨by omega,by omega,by omega,by omega⟩,?_,?_⟩
  · intro v _ hv
    have hv' := abs_le.mp hv
    constructor <;> omega
  · intro j
    have hj : |A.offset j|≤U := SourceSchedule.abs_le_absoluteBound A.offset j
    have hH' : |A.H (A.residue (Q-t))|≤H := SourceSchedule.abs_le_absoluteBound A.H _
    have hj' := abs_le.mp hj
    have hH'' := abs_le.mp hH'
    have hmax : max A.ext A.w₀≤|A.ext|+|A.w₀| := by apply max_le <;> omega
    constructor <;> omega

lemma Failed_phase_congr {s b t Q Q' : ℤ} {f g : ℤ → Alphabet}
    (hw₀ : 0≤A.w₀) (hv : A.Visible s b t Q) (he : AgreesOn f g s b)
    (hφ : A.φ (Q-t)=A.φ (Q'-t)) (hu : A.residue (Q-t)=A.residue (Q'-t)) :
    A.Failed f t Q ↔ A.Failed g t Q' := by
  rw [A.Failed_congr hw₀ hv he]
  simp only [Failed,Star,hφ,hu]

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
