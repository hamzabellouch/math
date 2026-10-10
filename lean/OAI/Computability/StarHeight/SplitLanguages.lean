import OAI.Computability.StarHeight.WordStreams

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uV uK uP uC uAlphabet2 uM2
universe uV2 uK2 uP2 uC2 uAlphabet3 uS uU uAlphabet4
universe uM3 uV3 uK3 uP3 uC3 uAlphabet5 uM4 uV4
universe uK4 uP4 uC4

namespace OuterStream

open WordIntervals LocalMarkers StreamShift StreamSplice SplitMetadata EpisodeAlgebra
variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma word_pair {tag : Tag M V g A.B} {f : ℤ → Alphabet} {lag reference k : ℤ}
    {w : List Alphabet} (hf : Realizes w 0 f)
    (hp : Prefix A H clock T ρ β tag f 0 lag k)
    (hq : Suffix A H clock T ρ reference tag f k w.length) :
    w∈prefixLanguage A H clock T ρ β lag tag.input * suffixLanguage A H clock T ρ reference tag.output := by
  obtain ⟨u,v,hw,hu,huf,hvf⟩ := realizes_cut hf hp.positive.le hq.ordered
  have hvlen : (v.length:ℤ)=(w.length:ℤ)-k := by rw [hw,List.length_append,Nat.cast_add];omega
  apply Language.mem_mul.mpr
  refine ⟨u,?_,v,?_,hw.symm⟩
  · exact Language.mem_iSup.mpr ⟨⟨tag,rfl⟩,f,huf,by simpa only [hu] using hp⟩
  · refine Language.mem_iSup.mpr ⟨⟨tag,rfl⟩,shift f (-k),?_,?_⟩
    · simpa only [add_neg_cancel] using StreamShift.realizes hvf (-k)
    · simpa only [add_neg_cancel,←sub_eq_add_neg,←hvlen] using suffix_shift A H clock T ρ hq (-k)

lemma word_sound [Nonempty Alphabet] (G : Geometry A H) (lag reference : ℤ) (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag)) :
    SplitSound (A.endRule.complete lag) (wordUpdate A clock T ρ β lag)
      (prefixLanguage A H clock T ρ β lag) (suffixLanguage A H clock T ρ reference) := by
  intro x y es u v hes hu hv hpair
  obtain ⟨a,fp,hfp,hp⟩ := Language.mem_iSup.mp hu
  obtain ⟨btag,fq,hfq,hq⟩ := Language.mem_iSup.mp hv
  cases es with
  | nil =>
    have hu0 : u.length=0 := by have := hpair.length_le;simp only [List.flatten_nil,List.length_nil,List.length_append] at this;omega
    have hh := hp.positive
    simp only [hu0,Nat.cast_zero,lt_self_iff_false] at hh
  | cons e fs =>
    have he : e∈A.endRule.complete lag := hes e (by simp)
    let f := stream ((e::fs).flatten)
    have hf : Realizes ((e::fs).flatten) 0 f := stream_realizes _
    have hep : e<+:(e::fs).flatten := by exact ⟨fs.flatten,rfl⟩
    have hef := hf.prefix hep
    have hend := (A.endRule.complete_realizes he hef).2
    have hvis := hvisible f e.length hend
    have hpairf := hf.prefix hpair
    have hpre : AgreesOn fp f 0 u.length := by simpa only [zero_add] using hfp.same hpairf.append_left
    have hfv : Realizes v (u.length:ℤ) f := by simpa only [zero_add] using hpairf.append_right
    have hqs : Suffix A H clock T ρ reference btag.val (shift fq u.length) u.length
        ((u.length:ℤ)+v.length) := by
      simpa only [zero_add,add_comm (v.length:ℤ)] using suffix_shift A H clock T ρ hq u.length
    have hqfs : Realizes v (u.length:ℤ) (shift fq u.length) := by
      simpa only [zero_add] using StreamShift.realizes hfq u.length
    have hsuf : AgreesOn (shift fq u.length) f u.length
        (min (e.length:ℤ) ((u.length:ℤ)+v.length)) := by
      intro z hz hz'
      exact hqfs.same hfv z hz (hz'.trans_le (min_le_right _ _))
    obtain ⟨hb,hup⟩ := pair_sound clock T ρ β G hp hqs hend hpre hsuf
    have huv : u++v=e := prefix_eq_of_length hpair hep (by simp only [List.length_append];exact_mod_cast hb.symm)
    refine ⟨e,fs,rfl,huv,?_⟩
    rw [wordUpdate_eq A clock T ρ β hef hw₀ hvis]
    simpa only [a.property,btag.property] using hup

lemma word_available [Nonempty Alphabet] (lag reference : ℤ) (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag))
    (havail : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      ¬A.Failed f lag (A.anchor f (b-A.endRule.tail) lag) → ∀ x,
      ∃ tag k, tag.input=x ∧ Prefix A H clock T ρ β tag f 0 lag k ∧
        Suffix A H clock T ρ reference tag f k b ∧
        tag.output=update A clock T ρ β f 0 b lag x) :
    SplitAvailable (A.endRule.complete lag) (A.failedDomain lag) (wordUpdate A clock T ρ β lag)
      (prefixLanguage A H clock T ρ β lag) (suffixLanguage A H clock T ρ reference) := by
  intro e he hn x
  let f := stream e
  have hf : Realizes e 0 f := stream_realizes e
  have hend := (A.endRule.complete_realizes he hf).2
  have hvis := hvisible f e.length hend
  have hfail : ¬A.Failed f lag (A.anchor f (e.length-A.endRule.tail) lag) := by
    intro h
    exact hn ⟨he,(A.failedLanguage_iff hw₀ hvis hf).mpr h⟩
  obtain ⟨tag,k,hx,hp,hq,hy⟩ := havail f e.length hend hfail x
  have hh := word_pair A H clock T ρ β hf hp hq
  rw [hx,hy] at hh
  exact hh

end OuterStream

namespace InnerStream

open WordIntervals LocalMarkers StreamShift StreamSplice SplitMetadata EpisodeAlgebra
variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

omit [Fintype K] in
lemma word_pair {slot reference : Roster M (V × K) K g' μ} {f : ℤ → Alphabet} {k : ℤ}
    {w : List Alphabet} (hf : Realizes w 0 f) (hk : 0≤k) (hkb : k≤w.length)
    (hp : Prefix T early γ p slot f 0 k)
    (hq : Suffix A clock T ρ β early p lag reference slot f k w.length) :
    w∈prefixLanguage T early γ p slot.1.input * suffixLanguage A clock T ρ β early p lag reference slot.1.output := by
  obtain ⟨u,v,hw,hu,huf,hvf⟩ := realizes_cut hf hk hkb
  have hvlen : (v.length:ℤ)=(w.length:ℤ)-k := by rw [hw,List.length_append,Nat.cast_add];omega
  apply Language.mem_mul.mpr
  refine ⟨u,?_,v,?_,hw.symm⟩
  · exact Language.mem_iSup.mpr ⟨⟨slot,rfl⟩,f,huf,by simpa only [hu] using hp⟩
  · refine Language.mem_iSup.mpr ⟨⟨slot,rfl⟩,shift f (-k),?_,?_⟩
    · simpa only [add_neg_cancel] using StreamShift.realizes hvf (-k)
    · simpa only [add_neg_cancel,←sub_eq_add_neg,←hvlen] using suffix_shift A clock T ρ β early p lag hq (-k)

omit [Monoid M] [Fintype M] [Fintype V] [Fintype K] in
lemma block_bounds (hearly : Monotone early) (h₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (slot : Roster M (V × K) K g' μ) : 0<p slot ∧ p slot<early (Fin.last g') := by
  have hlo := hearly (Fin.zero_le slot.1.j.castSucc)
  have hhi := hearly (Fin.le_last slot.1.j.succ)
  have hslot := hblock slot
  rw [h₀] at hlo
  exact ⟨hlo.trans_lt hslot.1,hslot.2.trans_le hhi⟩

omit [Fintype K] in
lemma word_sound [Nonempty Alphabet] (reference : Roster M (V × K) K g' μ)
    (hearly : StrictMono early) (h₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag))
    (hroster : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b → ∀ a i,
      A.Visible (p a) b (SuffixDecoder.origin p lag (p a) i)
        (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag (p a) i)))
    (hover : ∀ a, (A.endRule.d:ℤ)^2≤A.endRule.K-|p a-p reference|)
    (hover' : ∀ a, |p a-p reference|<A.endRule.K)
    (hendlast : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b → early (Fin.last g')≤b) :
    SplitSound (A.failedDomain lag) (wordUpdate A clock T ρ β early γ lag)
      (prefixLanguage T early γ p) (suffixLanguage A clock T ρ β early p lag reference) := by
  intro x y es u v hes hu hv hpair
  obtain ⟨a,fp,hfp,hp⟩ := Language.mem_iSup.mp hu
  obtain ⟨btag,fq,hfq,hq⟩ := Language.mem_iSup.mp hv
  have hcut : (u.length:ℤ)=p a.val := by simpa only [zero_add] using hp.cut
  cases es with
  | nil =>
    have hu0 : u.length=0 := by have := hpair.length_le;simp only [List.flatten_nil,List.length_nil,List.length_append] at this;omega
    have hpos := (block_bounds early p hearly.monotone h₀ hblock a.val).1
    simp only [hu0,Nat.cast_zero] at hcut
    omega
  | cons e fs =>
    have he : e∈A.failedDomain lag := hes e (by simp)
    let f := stream ((e::fs).flatten)
    have hf : Realizes ((e::fs).flatten) 0 f := stream_realizes _
    have hep : e<+:(e::fs).flatten := ⟨fs.flatten,rfl⟩
    have hef := hf.prefix hep
    have hend := (A.endRule.complete_realizes he.1 hef).2
    have hvis := hvisible f e.length hend
    have hfailed := (A.failedLanguage_iff hw₀ hvis hef).mp he.2
    have hlast := hendlast f e.length hend
    have hpairf := hf.prefix hpair
    have hpre : AgreesOn fp f 0 u.length := by simpa only [zero_add] using hfp.same hpairf.append_left
    have hfv : Realizes v (u.length:ℤ) f := by simpa only [zero_add] using hpairf.append_right
    have hqs : Suffix A clock T ρ β early p lag reference btag.val (shift fq u.length) u.length
        ((u.length:ℤ)+v.length) := by
      simpa only [zero_add,add_comm (v.length:ℤ)] using suffix_shift A clock T ρ β early p lag hq u.length
    have hqfs : Realizes v (u.length:ℤ) (shift fq u.length) := by
      simpa only [zero_add] using StreamShift.realizes hfq u.length
    have hsuf : AgreesOn f (shift fq u.length) u.length
        (min (e.length:ℤ) ((u.length:ℤ)+v.length)) := by
      intro z hz hz'
      exact hfv.same hqfs z hz (hz'.trans_le (min_le_right _ _))
    have hrv : ∀ i, A.Visible (u.length:ℤ) e.length (SuffixDecoder.origin p lag u.length i)
        (A.anchor f (e.length-A.endRule.tail) (SuffixDecoder.origin p lag u.length i)) := by
      rw [hcut]
      exact hroster f e.length hend a.val
    obtain ⟨_,hb,hup⟩ := pair_sound A clock T ρ β early γ p lag hearly h₀ hblock hw₀ hp hqs hrv
      (hover a.val) (hover' a.val) (by simpa only [zero_add] using hlast)
      (by simpa only [zero_add] using hend) (by simpa only [zero_add] using hfailed) hpre hsuf
    have huv : u++v=e := prefix_eq_of_length hpair hep (by simp only [List.length_append];exact_mod_cast hb)
    refine ⟨e,fs,rfl,huv,?_⟩
    rw [wordUpdate_eq A clock T ρ β early γ hearly.monotone h₀ hlast hef hw₀ hvis]
    simpa only [zero_add,a.property,btag.property] using hup

omit [Fintype K] in
lemma word_available [Nonempty Alphabet] (reference : Roster M (V × K) K g' μ)
    (hearly : Monotone early) (h₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw₀ : 0≤A.w₀)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Visible 0 b lag (A.anchor f (b-A.endRule.tail) lag))
    (hendlast : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b → early (Fin.last g')≤b)
    (havail : ∀ (f : ℤ → Alphabet) b,
      EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (lag+A.endRule.offset)
        (A.endRule.small f (lag+A.endRule.offset)) b →
      A.Failed f lag (A.anchor f (b-A.endRule.tail) lag) → ∀ x,
      ∃ slot k, slot.1.input=x ∧ Prefix T early γ p slot f 0 k ∧
        Suffix A clock T ρ β early p lag reference slot f k b ∧
        slot.1.output=update A clock T ρ β early γ f 0 b lag x) :
    SplitAvailable (A.failedDomain lag) 0 (wordUpdate A clock T ρ β early γ lag)
      (prefixLanguage T early γ p) (suffixLanguage A clock T ρ β early p lag reference) := by
  intro e he _ x
  let f := stream e
  have hf : Realizes e 0 f := stream_realizes e
  have hend := (A.endRule.complete_realizes he.1 hf).2
  have hvis := hvisible f e.length hend
  have hfail := (A.failedLanguage_iff hw₀ hvis hf).mp he.2
  obtain ⟨slot,k,hx,hp,hq,hy⟩ := havail f e.length hend hfail x
  have hc : k=p slot := by simpa only [zero_add] using hp.cut
  have hbounds := block_bounds early p hearly h₀ hblock slot
  have hh := word_pair A clock T ρ β early γ p lag hf (by omega)
    (by have := hendlast f e.length hend;omega) hp hq
  rw [hx,hy] at hh
  exact hh

end InnerStream
namespace EpisodeAlgebra

variable {Alphabet : Type uAlphabet3} {S : Type uS} {U : Type uU}

lemma updateWord_congr {D : Language Alphabet} {G G' : List Alphabet → S → S}
    (heq : ∀ e∈D, ∀ x, G e x=G' e x) {es : List (List Alphabet)} (he : AllIn D es) (x : S) :
    updateWord G x es=updateWord G' x es := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    rw [updateWord_cons,updateWord_cons,heq e (he e (by simp))]
    exact ih (fun a ha => he a (by simp [ha])) _

lemma graph_congr {D : Language Alphabet} {G G' : List Alphabet → S → S}
    (heq : ∀ e∈D, ∀ x, G e x=G' e x) (x y : S) : graph D G x y=graph D G' x y := by
  ext w
  constructor <;> rintro ⟨es,he,hw,hxy⟩
  · exact ⟨es,he,hw,(updateWord_congr heq he x).symm.trans hxy⟩
  · exact ⟨es,he,hw,(updateWord_congr heq he x).trans hxy⟩

lemma updateWord_embed {D : Language Alphabet} {G : List Alphabet → S → S}
    {J : List Alphabet → U → U} (ι : S → U)
    (heq : ∀ e∈D, ∀ x, J e (ι x)=ι (G e x)) {es : List (List Alphabet)}
    (he : AllIn D es) (x : S) : updateWord J (ι x) es=ι (updateWord G x es) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    rw [updateWord_cons,updateWord_cons,heq e (he e (by simp))]
    exact ih (fun a ha => he a (by simp [ha])) _

lemma graph_embed {D : Language Alphabet} {G : List Alphabet → S → S}
    {J : List Alphabet → U → U} (ι : S → U) (hi : Function.Injective ι)
    (heq : ∀ e∈D, ∀ x, J e (ι x)=ι (G e x)) (x y : S) :
    graph D G x y=graph D J (ι x) (ι y) := by
  ext w
  constructor <;> rintro ⟨es,he,hw,hxy⟩
  · exact ⟨es,he,hw,(updateWord_embed ι heq he x).trans (congrArg ι hxy)⟩
  · exact ⟨es,he,hw,hi ((updateWord_embed ι heq he x).symm.trans hxy)⟩

end EpisodeAlgebra

namespace OuterStream

open WordIntervals SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet4} {M : Type uM3} {V : Type uV3} {K : Type uK3} {P : Type uP3} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def wordShift [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) : V :=
  ClockAffine.shift clock ρ β Tag.input Tag.output
    (A.φ (A.anchor (stream w) (w.length-A.endRule.tail) lag-lag))
    (snapshot A T (stream w) 0 w.length lag)

lemma wordUpdate_affine [Nonempty Alphabet] (lag : ℤ) :
    wordUpdate A clock T ρ β lag=
      AffineRecovery.affine (fun w => (ρ (T w)).toAddMonoidHom) (wordShift A clock T ρ β lag) := by
  funext w x
  have hp : product T (stream w) 0 w.length=T w := by
    unfold product
    rw [show (w.length:ℤ)=0+(w.length:ℤ) by omega,realizes_piece (stream_realizes w)]
  change ρ (product T (stream w) 0 w.length) x+_=ρ (T w) x+_
  rw [hp]
  rfl

end OuterStream

namespace InnerStream

open WordIntervals SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet5} {M : Type uM4} {V : Type uV4} {K : Type uK4} {P : Type uP4} {C : Type uC4} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

noncomputable def wordLinear [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) : V × K →ₗ[K] V × K :=
  ObservedInner.table (hypothetical A clock T ρ β early (stream w) 0 w.length lag)
    (fun i : Fin g' => product T (stream w) (early i.castSucc) (early i.succ))

noncomputable def wordShift [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) : V × K :=
  γ (hypothetical A clock T ρ β early (stream w) 0 w.length lag)
    (fun i : Fin g' => product T (stream w) (early i.castSucc) (early i.succ))

lemma wordUpdate_affine [Nonempty Alphabet] (lag : ℤ) :
    wordUpdate A clock T ρ β early γ lag=
      AffineRecovery.affine (fun w => (wordLinear A clock T ρ β early lag w).toAddMonoidHom)
        (wordShift A clock T ρ β early γ lag) := by
  funext w x
  simp only [wordUpdate,update,wordLinear,wordShift,zero_add,AffineRecovery.affine]
  rfl

lemma wordLinear_lift [Nonempty Alphabet] (hm : Monotone early) (h₀ : early 0=0)
    {lag : ℤ} {w : List Alphabet} (hb : early (Fin.last g')≤w.length)
    (hstart : ∀ i q, A.inner (stream w) i
      (A.residue (A.anchor (stream w) (w.length-A.endRule.tail) lag-lag)) lag=some q →
      early (Fin.last g')≤q) :
    wordLinear A clock T ρ β early lag w=
      Homogenization.lift (ρ (T w)) (OuterStream.wordShift A clock T ρ β lag w) := by
  have hprod := product_chain T (stream w) early hm
  rw [h₀] at hprod
  have hlast : 0≤early (Fin.last g') := by rw [←h₀];exact hm (Fin.zero_le _)
  have hh := hypothetical_actual A clock T ρ β early (f := stream w) (s := 0) (b := w.length)
    (t := lag) (by simpa only [zero_add] using hlast) (by simpa only [zero_add] using hb)
    (by simpa only [zero_add] using hstart)
  have hp : product T (stream w) 0 w.length=T w := by
    unfold product
    rw [show (w.length:ℤ)=0+(w.length:ℤ) by omega,realizes_piece (stream_realizes w)]
  simpa only [wordLinear,ObservedInner.table,hprod,zero_add,hp,OuterStream.wordShift] using hh

lemma linear_graph_recovery [Nonempty Alphabet] (hm : Monotone early) (h₀ : early 0=0)
    (lag : ℤ) (H : ℕ)
    (hb : ∀ w∈A.failedDomain lag, early (Fin.last g')≤w.length)
    (hstart : ∀ w∈A.failedDomain lag, ∀ i q, A.inner (stream w) i
      (A.residue (A.anchor (stream w) (w.length-A.endRule.tail) lag-lag)) lag=some q →
      early (Fin.last g')≤q)
    (hgraph : ∀ x y, HasHeightAtMost (EpisodeAlgebra.graph (A.failedDomain lag)
      (fun w => wordLinear A clock T ρ β early lag w) x y) H) (x y : V) :
    HasHeightAtMost (EpisodeAlgebra.graph (A.failedDomain lag)
      (OuterStream.wordUpdate A clock T ρ β lag) x y) H := by
  rw [EpisodeAlgebra.graph_embed (fun v : V => (v,(1:K))) (by intro a b h;exact congrArg Prod.fst h)
    (J := fun w => wordLinear A clock T ρ β early lag w)]
  · exact hgraph (x,1) (y,1)
  · intro w hw z
    rw [wordLinear_lift A clock T ρ β early hm h₀ (hb w hw) (hstart w hw),
      Homogenization.lift_apply_one,OuterStream.wordUpdate_affine]
    rfl

end InnerStream

end GeneralizedStarHeight

end OAI
