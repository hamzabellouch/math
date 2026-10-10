import OAI.Computability.StarHeight.Translation

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uS uK uAlphabet2 uM2 uV uK2
universe uP uC uAlphabet3 uM3 uV2 uK3 uP2 uC2
universe uAlphabet4

namespace ObservedMain

open StreamShift BoundarySnapshot
variable {Alphabet : Type uAlphabet} {M : Type uM} {S : Type uS} {K : Type uK} [Monoid M] [Field K] [AddCommGroup S] [Module K S]
    {g B : ℕ} (T : FreeMonoid Alphabet →* M) (ρ : M → (S →ₗ[K] S))
    (β : M → M → (Fin g → M) → S)

lemma prefix_shift {tag : SplitMetadata.MainTag M S g B} {f : ℤ → Alphabet} {s k : ℤ}
    {search : Fin (g+1) → Option ℤ} (hp : PrefixRead T ρ β tag f s k search) (a : ℤ) :
    PrefixRead T ρ β tag (shift f a) (s+a) (k+a) (translated search a) := by
  have hpos (i : Fin (g+1)) (hi : i.val≤tag.j.val) := translated_position (hp.present i hi) a
  have hz : (0 : Fin (g+1)).val≤tag.j.val := Nat.zero_le _
  refine ⟨⟨fun i hi h => hp.present i hi ((translated_none search a i).mp h),?_,?_,hp.certificate⟩,?_,?_⟩
  · rw [hpos 0 hz,StreamShift.product]
    exact hp.initial
  · intro i hi
    rw [hpos i.val.castSucc (by exact hi.le),hpos i.val.succ (by exact hi),StreamShift.product]
    exact hp.earlier i hi
  · intro i hi
    rw [hpos i hi]
    have := hp.bounds i hi
    constructor <;> omega
  · intro i hi
    rw [hpos i.castSucc (by exact hi.le),hpos i.succ (by exact hi)]
    have := hp.ordered i hi
    omega

omit [Field K] [AddCommGroup S] [Module K S] in
lemma suffix_shift {tag : SplitMetadata.MainTag M S g B} {f : ℤ → Alphabet} {k b : ℤ}
    {search : Fin (g+1) → Option ℤ} (hq : SuffixRead T tag f k b search) (a : ℤ) :
    SuffixRead T tag (shift f a) (k+a) (b+a) (translated search a) := by
  have hpos (i : Fin (g+1)) (hi : tag.j.val < i.val) := translated_position (hq.present i hi) a
  have hg : tag.j.val < (Fin.last g).val := tag.j.isLt
  refine ⟨⟨fun i hi h => hq.present i hi ((translated_none search a i).mp h),?_,?_⟩,?_,?_⟩
  · rw [hpos _ hg,StreamShift.product]
    exact hq.final
  · intro i hi
    rw [hpos i.val.castSucc hi,hpos i.val.succ (by exact Nat.lt_succ_of_lt hi),StreamShift.product]
    exact hq.later i hi
  · intro i hi
    rw [hpos i hi]
    have := hq.bounds i hi
    constructor <;> omega
  · intro i hi
    rw [hpos i.castSucc hi,hpos i.succ (by exact Nat.lt_succ_of_lt hi)]
    have := hq.ordered i hi
    omega

end ObservedMain

namespace OuterStream

open StreamShift BoundarySnapshot SplitMetadata
variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV} {K : Type uK2} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

omit [Fintype C] in
lemma search_shift (f : ℤ → Alphabet) (u : Fin A.B) (t a : ℤ) :
    search A (shift f a) u (t+a)=translated (search A f u t) a := by
  funext i
  exact A.inner_shift f i u t a

omit [Fintype M] [Fintype C] in
lemma snapshot_shift (f : ℤ → Alphabet) (s b t a : ℤ) :
    snapshot A T (shift f a) (s+a) (b+a) (t+a)=snapshot A T f s b t := by
  unfold snapshot
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift,
    add_sub_add_right_eq_sub,search_shift,actual_shift]

lemma update_shift (f : ℤ → Alphabet) (s b t a : ℤ) (x : V) :
    update A clock T ρ β (shift f a) (s+a) (b+a) (t+a) x=update A clock T ρ β f s b t x := by
  unfold update
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift,
    add_sub_add_right_eq_sub,snapshot_shift]

lemma prefix_shift {tag : Tag M V g A.B} {f : ℤ → Alphabet} {s t k : ℤ}
    (hp : Prefix A H clock T ρ β tag f s t k) (a : ℤ) :
    Prefix A H clock T ρ β tag (shift f a) (s+a) (t+a) (k+a) := by
  refine ⟨by have := hp.positive;omega,?_,?_,?_⟩
  · obtain ⟨i,hi,hcut⟩ := hp.cut
    exact ⟨i,hi,by omega⟩
  · simpa only [add_sub_add_right_eq_sub] using hp.clock_mem
  · cases tag with
    | inl tag =>
      have hm : PrefixMain A T ρ β tag f s t k := hp.letter_test
      refine ⟨fun i hi => A.innerVisible_shift (hm.visible i hi) a,?_⟩
      rw [search_shift]
      exact ObservedMain.prefix_shift T ρ β hm.observed a
    | inr tag =>
      have hm : PrefixPeriodic A T tag f s t k := hp.letter_test
      refine ⟨A.innerVisible_shift hm.visible a,?_,?_⟩
      · rw [A.inner_shift,hm.absent,Option.map_none]
      · rw [StreamShift.product]
        exact hm.product_eq

omit [Monoid M] [Field K] [AddCommGroup V] [Module K V] [Fintype M] [Fintype V]
  [Fintype P] [Fintype C] in
lemma origins_shift (k a : ℤ) : H.origins (k+a)=(H.origins k).image (fun x => x+a) := by
  simp only [Cuts.origins,Finset.image_image]
  congr 1
  funext h
  dsimp
  ring

omit [Fintype C] in
lemma suffixAnchor_shift (f : ℤ → Alphabet) (reference k b a : ℤ) :
    suffixAnchor A reference (k+a) (b+a) (shift f a)=suffixAnchor A reference k b f+a := by
  unfold suffixAnchor
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,
    show k+a-reference=(k-reference)+a by ring,A.anchor_shift]

lemma suffix_shift {tag : Tag M V g A.B} {f : ℤ → Alphabet} {reference k b : ℤ}
    (hq : Suffix A H clock T ρ reference tag f k b) (a : ℤ) :
    Suffix A H clock T ρ reference tag (shift f a) (k+a) (b+a) := by
  refine ⟨by have := hq.ordered;omega,?_,?_,?_,?_⟩
  · rw [origins_shift,show k+a-reference=(k-reference)+a by ring]
    exact A.endRule.guard_shift hq.guard a
  · rw [suffixAnchor_shift,add_sub_add_right_eq_sub]
    exact hq.clock_mem
  · rw [suffixAnchor_shift,add_sub_add_right_eq_sub]
    exact hq.residue_eq
  · cases tag with
    | inr tag =>
      change tag.output=ρ (tag.prefixProduct*WordIntervals.product T (shift f a) (k+a) (b+a)) tag.input
      rw [StreamShift.product]
      exact hq.letter_test
    | inl tag =>
      have hm : SuffixMain A H T tag f k b := hq.letter_test
      refine ⟨?_,?_,?_⟩
      · intro i hi j hj
        simpa only [show k-H.main tag.j-(i:ℤ)*A.B+a=k+a-H.main tag.j-i*A.B by ring]
          using A.innerVisible_shift (hm.visible i hi j hj) a
      · intro i hi j hj
        rw [show k+a-H.main tag.j-(i:ℤ)*A.B=(k-H.main tag.j-i*A.B)+a by ring,
          show k+a-H.main tag.j=(k-H.main tag.j)+a by ring,A.inner_shift,A.inner_shift,hm.stable i hi j hj]
      · rw [show k+a-H.main tag.j=(k-H.main tag.j)+a by ring,search_shift]
        exact ObservedMain.suffix_shift T hm.observed a

end OuterStream

namespace InnerStream

open StreamShift BoundarySnapshot SplitMetadata
variable {Alphabet : Type uAlphabet3} {M : Type uM3} {V : Type uV2} {K : Type uK3} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

lemma hypothetical_shift (f : ℤ → Alphabet) (s b t a : ℤ) :
    hypothetical A clock T ρ β early (shift f a) (s+a) (b+a) (t+a)=
      hypothetical A clock T ρ β early f s b t := by
  unfold hypothetical
  rw [show b+a-A.endRule.tail=(b-A.endRule.tail)+a by ring,A.anchor_shift]
  dsimp only
  rw [add_sub_add_right_eq_sub,OuterStream.search_shift,
    show s+a+early (Fin.last g')=(s+early (Fin.last g'))+a by ring,later_shift]

lemma update_shift (f : ℤ → Alphabet) (s b t a : ℤ) (x : V × K) :
    update A clock T ρ β early γ (shift f a) (s+a) (b+a) (t+a) x=
      update A clock T ρ β early γ f s b t x := by
  have hd (i : Fin g') :
      WordIntervals.product T (shift f a) (s+a+early i.castSucc) (s+a+early i.succ)=
      WordIntervals.product T f (s+early i.castSucc) (s+early i.succ) := by
    rw [show s+a+early i.castSucc=(s+early i.castSucc)+a by ring,
      show s+a+early i.succ=(s+early i.succ)+a by ring,StreamShift.product]
  simp only [update,hypothetical_shift,hd]

omit [Fintype M] [Fintype V] in
lemma prefix_shift {slot : Roster M (V × K) K g' μ} {f : ℤ → Alphabet} {s k : ℤ}
    (hp : Prefix T early γ p slot f s k) (a : ℤ) :
    Prefix T early γ p slot (shift f a) (s+a) (k+a) := by
  refine ⟨by have := hp.cut;omega,⟨?_,hp.observed.certificate⟩⟩
  intro i hi
  rw [show s+a+early i.val.castSucc=(s+early i.val.castSucc)+a by ring,
    show s+a+early i.val.succ=(s+early i.val.succ)+a by ring,StreamShift.product]
  exact hp.observed.earlier i hi

lemma suffix_shift {reference slot : Roster M (V × K) K g' μ} {f : ℤ → Alphabet} {k b : ℤ}
    (hq : Suffix A clock T ρ β early p lag reference slot f k b) (a : ℤ) :
    Suffix A clock T ρ β early p lag reference slot (shift f a) (k+a) (b+a) := by
  refine ⟨?_,⟨?_,?_⟩⟩
  · have he : SuffixDecoder.origin p lag (k+a)=fun i => SuffixDecoder.origin p lag k i+a := by
      funext i
      dsimp [SuffixDecoder.origin]
      ring
    rw [he]
    exact SuffixDecoder.test_shift A hq.decoder a
  · intro i hi
    rw [show k+a-p slot+early i.val.castSucc=(k-p slot+early i.val.castSucc)+a by ring,
      show k+a-p slot+early i.val.succ=(k-p slot+early i.val.succ)+a by ring,StreamShift.product]
    exact hq.observed.later i hi
  · rw [show k+a-p slot+lag=(k-p slot+lag)+a by ring,
      show k+a-p slot=(k-p slot)+a by ring,hypothetical_shift]
    exact hq.observed.hypothetical_eq

end InnerStream

namespace WordIntervals

variable {Alphabet : Type uAlphabet4}

noncomputable def stream [Nonempty Alphabet] (w : List Alphabet) : ℤ → Alphabet :=
  Classical.choose (realizes_exists w 0)

lemma stream_realizes [Nonempty Alphabet] (w : List Alphabet) : Realizes w 0 (stream w) :=
  Classical.choose_spec (realizes_exists w 0)

lemma Realizes.same {w : List Alphabet} {f g : ℤ → Alphabet} {s : ℤ}
    (hf : Realizes w s f) (hg : Realizes w s g) : LocalMarkers.AgreesOn f g s (s+w.length) :=
  hf.agrees hg List.prefix_rfl

lemma Realizes.pair_prefix {u v w : List Alphabet} {f : ℤ → Alphabet}
    (hf : Realizes w 0 f) (hpair : u++v <+: w) : Realizes u 0 f :=
  (hf.prefix hpair).append_left

end WordIntervals

end GeneralizedStarHeight

end OAI
