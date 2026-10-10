import OAI.Computability.StarHeight.ObservedLanguages

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uV uK uP uC uAlphabet2 uM2
universe uAlphabet3 uJ uC2 uAlphabet4 uM3 uV2 uK2 uP2
universe uC3

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

structure Geometry : Prop where
  multiple : ∀ role : H.Role, (A.B : ℤ) ∣ H.base role
  boundary_order : ∀ (u : Fin A.B) (i j : Fin (g+1)), i < j →
    A.offset i + A.H u ≤ A.offset j
  end_left : ∀ h ∈ H.offsets, h + A.endRule.width + A.endRule.rule.r ≤ A.endRule.offset
  end_right : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets,
    h-h'+A.endRule.width+A.endRule.rule.r+
      ((A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S) ≤ A.endRule.tail
  seed_right : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets,
    h-h'+A.endRule.K+((A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S) ≤ A.endRule.tail
  overlap : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets,
    (A.endRule.d : ℤ)^2 + |h-h'| ≤ A.endRule.K

variable {A H}

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Geometry.actual_visibility (G : Geometry A H) {f : ℤ → Alphabet} {t k b : ℤ}
    {tag : Tag M V g A.B}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b) :
    ∀ o ∈ H.origins k, A.endRule.Visible k b (o+A.endRule.offset) := by
  obtain ⟨a,ha,hk⟩ := hc
  have hmem := H.offset_mem (H.tagRole tag) a ha
  have hb := A.endRule.end_lower he
  have hw := A.endRule.width_nonneg
  have hr := A.endRule.rule.radius_ge
  intro o ho
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ho
  have hleft := G.end_left h hh
  have hright := G.end_right _ hmem h hh
  have hseed := G.seed_right _ hmem h hh
  refine ⟨by omega,by omega,by omega,by omega⟩

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Geometry.origin_overlap (G : Geometry A H) {t k r : ℤ} {tag : Tag M V g A.B}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B)
    (hr : r ∈ H.origins k) :
    (A.endRule.d : ℤ)^2 ≤ (A.endRule.K : ℤ)-|t-r| ∧ |t-r| < A.endRule.K := by
  obtain ⟨a,ha,hk⟩ := hc
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hr
  have hmem := H.offset_mem (H.tagRole tag) a ha
  have hov := G.overlap _ hmem h hh
  have heq : t-(k-h) = -(H.base (H.tagRole tag)+(a:ℤ)*A.B-h) := by omega
  have hd := A.endRule.d_ge
  have hd' : (2:ℤ) ≤ A.endRule.d := by exact_mod_cast hd
  rw [heq,abs_neg]
  constructor <;> nlinarith

omit [Fintype C] in
lemma Geometry.present (G : Geometry A H) {f : ℤ → Alphabet} {u : Fin A.B} {s b t : ℤ}
    (hv : ∀ j, A.InnerVisible s b t j u) (hp : ∀ j, A.inner f j u t ≠ none) :
    Present (search A f u t) s b := by
  apply present_of_bounds hp
  · intro i p he
    have hb := A.inner_bounds he
    have hh := (hv i).1
    have hr := A.innerRule.radius_ge
    omega
  · intro i p he
    have hb := A.inner_bounds he
    have hh := (hv i).2
    have hr := A.innerRule.radius_ge
    omega
  · intro i j p q hij hi hj
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_of_eq (Option.some.inj (hi.symm.trans hj))
    · have hp' := A.inner_bounds hi
      have hq' := A.inner_bounds hj
      have ho := G.boundary_order u i j hij
      omega

lemma consumes (G : Geometry A H) {reference s t k b b' : ℤ}
    {f fp fq : ℤ → Alphabet} {a btag : Tag M V g A.B}
    (hp : Prefix A H clock T ρ β a fp s t k)
    (hq : Suffix A H clock T ρ reference btag fq k b')
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hag : AgreesOn f fq k (min b b')) :
    b=b' ∧ A.anchor f (b-A.endRule.tail) t = suffixAnchor A reference k b' fq := by
  have hover := G.origin_overlap hp.cut hq.guard.1
  exact A.endRule.guard_shared_end (H.true_origin a hp.cut) hq.guard
    (G.actual_visibility hp.cut he) hag hover.1 hover.2 he

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Geometry.cut_multiple (G : Geometry A H) {tag : Tag M V g A.B} {t k : ℤ}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B) :
    (A.B : ℤ) ∣ k-t := by
  obtain ⟨a,ha,rfl⟩ := hc
  rw [show t+H.base (H.tagRole tag)+(a:ℤ)*A.B-t = H.base (H.tagRole tag)+(a:ℤ)*A.B by ring]
  exact dvd_add (G.multiple (H.tagRole tag)) (dvd_mul_left (A.B:ℤ) (a:ℤ))

omit [Fintype C] in
lemma residue_shift {q t k : ℤ} (hm : (A.B:ℤ) ∣ k-t) :
    A.residue (q-t) = A.residue (q-k) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [A.residue_val,A.residue_val]
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  apply Int.emod_eq_zero_of_dvd
  convert hm using 1
  ring

lemma pair_sound (G : Geometry A H) {reference s t k b b' : ℤ}
    {f fp fq : ℤ → Alphabet} {a btag : Tag M V g A.B}
    (hp : Prefix A H clock T ρ β a fp s t k)
    (hq : Suffix A H clock T ρ reference btag fq k b')
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hprefix : AgreesOn fp f s k) (hsuffix : AgreesOn fq f k (min b b')) :
    b=b' ∧ update A clock T ρ β f s b t a.input = btag.output := by
  have hconsume := consumes clock T ρ β G hp hq he (fun z hz hz' => (hsuffix z hz hz').symm)
  obtain rfl := hconsume.1
  have hsuffix' : AgreesOn fq f k b := by simpa using hsuffix
  have hclock : A.φ (A.anchor f (b-A.endRule.tail) t-k) ∈ clock.J btag := by
    rw [hconsume.2]
    exact hq.clock_mem
  have hedge := ClockAffine.edge_add clock A.φ hp.clock_mem hclock
  refine ⟨rfl,?_⟩
  apply ClockAffine.independent_pair clock ρ β Tag.input Tag.output _ hedge
  intro hab _
  subst btag
  have hu : A.residue (A.anchor f (b-A.endRule.tail) t-t) = a.residue := by
    rw [residue_shift (G.cut_multiple hp.cut),hconsume.2]
    exact hq.residue_eq
  cases a with
  | inl tag =>
    have hp' := hp.letter_test
    have hq' := hq.letter_test
    change PrefixMain A T ρ β tag fp s t k at hp'
    change SuffixMain A H T tag fq k b at hq'
    have hpre : ObservedMain.PrefixRead T ρ β tag f s k (search A f tag.u t) :=
      hp'.observed.transfer T ρ β hprefix (fun i hi => A.inner_congr (hp'.visible i hi) hprefix)
    obtain ⟨a,ha,hk⟩ := hp.cut
    have ht : k-H.main tag.j-a*A.B=t := by simpa [Cuts.base,Cuts.tagRole] using (show k-H.main tag.j-a*A.B=t by change k=t+H.main tag.j+a*A.B at hk;omega)
    have hpost : ObservedMain.SuffixRead T tag f k b (search A f tag.u t) := by
      apply hq'.observed.transfer T hsuffix'
      intro i hi
      have hst := hq'.stable a ha i hi
      have hver := hq'.visible a ha i hi
      rw [ht] at hst hver
      exact hst.symm.trans (A.inner_congr hver hsuffix')
    have hv : ∀ i, A.InnerVisible s b t i tag.u := by
      intro i
      by_cases hi : i.val ≤ tag.j.val
      · have hh := hp'.visible i hi
        exact ⟨hh.1,hh.2.trans hq.ordered⟩
      · have hh := hq'.visible a ha i (by omega)
        rw [ht] at hh
        exact ⟨hp.positive.le.trans hh.1,hh.2⟩
    have hm := G.present hv (ObservedMain.pair_present T ρ β hpre.toPrefix hpost.toSuffix)
    have hh := ObservedMain.pair_sound T ρ β hpre.toPrefix hpost.toSuffix hm
    simp only [snapshot,hu,Tag.residue,Tag.input,Tag.output]
    cases hboundaries : (actual T f s b (search A f tag.u t)).boundaries <;>
      simpa only [hboundaries] using hh
  | inr tag =>
    have hp' := hp.letter_test
    change PrefixPeriodic A T tag fp s t k at hp'
    have hn : A.inner f tag.j tag.u t = none :=
      (A.inner_congr hp'.visible hprefix).symm.trans hp'.absent
    have hprod := product_congr T hp.positive.le hprefix
    have hsprod := product_congr T hq.ordered hsuffix'
    have happ := product_append T f hp.positive.le hq.ordered
    have hnone := factors_absent T f (s := s) (b := b) (search := search A f tag.u t)
      (i := tag.j) hn
    have hout := hq.letter_test
    change tag.output = ρ (tag.prefixProduct * product T fq k b) tag.input at hout
    rw [←hp'.product_eq,hprod,hsprod,←happ] at hout
    simpa only [snapshot,hu,Tag.residue,Tag.input,Tag.output,actual,hnone,add_zero] using hout.symm

end OuterStream

namespace BoundarySnapshot

open WordIntervals LocalMarkers
variable {Alphabet : Type uAlphabet2} {M : Type uM2} [Monoid M] {g : ℕ}

lemma factors_congr (T : FreeMonoid Alphabet →* M) {f f' : ℤ → Alphabet}
    {a b : ℤ} {search : Fin (g+1) → Option ℤ} (he : AgreesOn f f' a b) :
    factors T f a b search = factors T f' a b search := by
  classical
  by_cases hp : Present search a b
  · rw [factors_positions T f hp,factors_positions T f' hp]
    obtain ⟨p,hp,hm,ha,hb⟩ := hp
    have hpos : positions search = p := by funext i;simp [positions,hp]
    simp only [hpos]
    congr 2
    · apply product_congr T ha
      intro z hz hz'
      exact he z hz (hz'.trans_le ((hm (Fin.zero_le _)).trans hb))
    · funext i
      apply product_congr T (hm (Fin.castSucc_le_succ i))
      intro z hz hz'
      exact he z ((ha.trans (hm (Fin.zero_le _))).trans hz)
        (hz'.trans_le ((hm (Fin.le_last _)).trans hb))
    · apply product_congr T hb
      intro z hz hz'
      exact he z ((ha.trans (hm (Fin.zero_le _))).trans hz) hz'
  · simp only [factors,dite_eq_right hp]

@[ext] lemma later_ext {D E : ClockAffine.Later M g}
    (hp : D.tailProduct=E.tailProduct) (hb : D.boundaries=E.boundaries) : D=E := by
  cases D;cases E;cases hp;cases hb;rfl

lemma later_congr (T : FreeMonoid Alphabet →* M) {f f' : ℤ → Alphabet}
    {a b : ℤ} (hab : a ≤ b) {search search' : Fin (g+1) → Option ℤ}
    (hs : search=search') (he : AgreesOn f f' a b) :
    later T f a b search = later T f' a b search' := by
  subst search'
  apply later_ext
  · exact product_congr T hab he
  · exact factors_congr T he

end BoundarySnapshot

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet3} {J : Type uJ} {C : Type uC2} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma Visible.innerVisible {s b t Q : ℤ} (hv : A.Visible s b t Q)
    (hw : 0 ≤ A.w₀) (j : J) : A.InnerVisible s b t j (A.residue (Q-t)) := by
  have hi := hv.inner j
  have hm := le_max_right A.ext A.w₀
  exact ⟨by omega,by omega⟩

end ExceptionalOrigins.Parameters

namespace InnerStream

open WordIntervals LocalMarkers SplitMetadata BoundarySnapshot

variable {Alphabet : Type uAlphabet4} {M : Type uM3} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)
    (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

noncomputable def hypothetical (f : ℤ → Alphabet) (s b t : ℤ) :
    M → (V × K →ₗ[K] V × K) :=
  let q := A.anchor f (b-A.endRule.tail) t
  ClockAffine.hypothetical clock ρ β Tag.input Tag.output (A.φ (q-t))
    (later T f (s+early (Fin.last g')) b (OuterStream.search A f (A.residue (q-t)) t))

noncomputable def update (f : ℤ → Alphabet) (s b t : ℤ) (x : V × K) : V × K :=
  let ψ := hypothetical A clock T ρ β early f s b t
  let d := fun i : Fin g' => product T f (s+early i.castSucc) (s+early i.succ)
  ObservedInner.table ψ d x + γ ψ d

lemma hypothetical_congr {f f' : ℤ → Alphabet} {s b t k : ℤ}
    (hk : k ≤ s+early (Fin.last g')) (hb : s+early (Fin.last g') ≤ b)
    (he : AgreesOn f f' k b)
    (hq : A.anchor f (b-A.endRule.tail) t = A.anchor f' (b-A.endRule.tail) t)
    (hv : ∀ j, A.InnerVisible k b t j (A.residue (A.anchor f (b-A.endRule.tail) t-t))) :
    hypothetical A clock T ρ β early f s b t = hypothetical A clock T ρ β early f' s b t := by
  have hs : OuterStream.search A f (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t =
      OuterStream.search A f' (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t := by
    funext j
    exact A.inner_congr (hv j) he
  have hl := later_congr T hb hs (fun z hz hz' => he z (hk.trans hz) hz')
  dsimp only [hypothetical]
  rw [←hq,hl]

variable (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

structure Prefix (slot : Roster M (V × K) K g' μ) (f : ℤ → Alphabet) (s k : ℤ) : Prop where
  cut : k=s+p slot
  observed : ObservedInner.Prefix T γ slot.1 f (fun i => s+early i)

structure Suffix (reference slot : Roster M (V × K) K g' μ) (f : ℤ → Alphabet)
    (k b : ℤ) : Prop where
  decoder : SuffixDecoder.Test A (SuffixDecoder.origin p lag k) reference k b f slot
  observed : ObservedInner.Suffix T slot.1 f (fun i => k-p slot+early i)
    (hypothetical A clock T ρ β early f (k-p slot) b (k-p slot+lag))

omit [Fintype M] [Fintype V] in
lemma prefix_actual (hearly : StrictMono early) (hearly₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    {s k : ℤ} {f fp : ℤ → Alphabet} {actual : Roster M (V × K) K g' μ}
    (hp : Prefix T early γ p actual fp s k) (hprefix : AgreesOn fp f s k) :
    ObservedInner.Prefix T γ actual.1 f (fun i => s+early i) := by
  have hbound : Monotone (fun i => s+early i) := fun _ _ h => add_le_add_right (hearly.monotone h) s
  apply ObservedInner.prefix_congr T γ hbound
    (show s+early actual.1.j.castSucc ≤ k by rw [hp.cut];exact (add_lt_add_right (hblock actual).1 s).le)
    _ hp.observed
  simpa only [hearly₀,add_zero] using hprefix

lemma suffix_actual (hearly : StrictMono early)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw : 0 ≤ A.w₀) {s k b : ℤ} {f fq : ℤ → Alphabet}
    {reference actual : Roster M (V × K) K g' μ}
    (hcut : k=s+p actual)
    (hq : Suffix A clock T ρ β early p lag reference actual fq k b)
    (hvis : ∀ i, A.Visible k b (SuffixDecoder.origin p lag k i)
      (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag k i)))
    (hb : s+early (Fin.last g') ≤ b) (hsuffix : AgreesOn f fq k b) :
    ObservedInner.Suffix T actual.1 f (fun i => s+early i)
      (hypothetical A clock T ρ β early f s b (s+lag)) := by
  have ht : SuffixDecoder.origin p lag k actual=s+lag := by dsimp [SuffixDecoder.origin];rw [hcut];ring
  have hk : k ≤ s+early (Fin.last g') := by
    rw [hcut]
    exact add_le_add_right ((hblock actual).2.le.trans (hearly.monotone (Fin.le_last _))) s
  have hqeq : A.anchor f (b-A.endRule.tail) (s+lag) = A.anchor fq (b-A.endRule.tail) (s+lag) := by
    have hh := (SuffixDecoder.searches_agree A hq.decoder hvis (by simpa using hsuffix) actual).2
    rw [ht] at hh
    simp only [ExceptionalOrigins.Parameters.anchor,hh]
  have hψ := hypothetical_congr A clock T ρ β early hk hb hsuffix hqeq (by
    intro j
    have hh := ExceptionalOrigins.Parameters.Visible.innerVisible A (hvis actual) hw j
    simpa only [ht] using hh)
  have hx : k-p actual=s := by rw [hcut];ring
  have hh := hq.observed
  rw [hx,←hψ] at hh
  have hbound : Monotone (fun i => s+early i) := fun _ _ h => add_le_add_right (hearly.monotone h) s
  apply ObservedInner.suffix_congr T hbound
    (show k ≤ s+early actual.1.j.succ by rw [hcut];exact (add_lt_add_right (hblock actual).2 s).le)
    _ hh
  intro z hz hz'
  exact (hsuffix z hz (hz'.trans_le hb)).symm

lemma same_slot_sound (hearly : StrictMono early) (hearly₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw : 0 ≤ A.w₀) {s k b : ℤ} {f fp fq : ℤ → Alphabet}
    {reference actual : Roster M (V × K) K g' μ}
    (hp : Prefix T early γ p actual fp s k)
    (hq : Suffix A clock T ρ β early p lag reference actual fq k b)
    (hvis : ∀ i, A.Visible k b (SuffixDecoder.origin p lag k i)
      (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag k i)))
    (hb : s+early (Fin.last g') ≤ b)
    (hprefix : AgreesOn fp f s k) (hsuffix : AgreesOn f fq k b) :
    update A clock T ρ β early γ f s b (s+lag) actual.1.input = actual.1.output := by
  have hpre := prefix_actual T early γ p hearly hearly₀ hblock hp hprefix
  have hpost := suffix_actual A clock T ρ β early p lag hearly hblock hw hp.cut hq hvis hb hsuffix
  dsimp only [update]
  exact ObservedInner.pair_sound (K := K) (U := V × K) (g := g') T γ
    (kind := actual.1) (boundary := fun i => s+early i)
    (ψ := hypothetical A clock T ρ β early f s b (s+lag)) hpre hpost

lemma pair_sound (hearly : StrictMono early) (hearly₀ : early 0=0)
    (hblock : ∀ slot, early slot.1.j.castSucc < p slot ∧ p slot < early slot.1.j.succ)
    (hw : 0 ≤ A.w₀) {s k b b' : ℤ} {f fp fq : ℤ → Alphabet}
    {reference actual decoded : Roster M (V × K) K g' μ}
    (hp : Prefix T early γ p actual fp s k)
    (hq : Suffix A clock T ρ β early p lag reference decoded fq k b')
    (hvis : ∀ i, A.Visible k b (SuffixDecoder.origin p lag k i)
      (A.anchor f (b-A.endRule.tail) (SuffixDecoder.origin p lag k i)))
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K-|p actual-p reference|)
    (hover' : |p actual-p reference| < A.endRule.K)
    (hb : s+early (Fin.last g') ≤ b)
    (hend : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (s+lag+A.endRule.offset) (A.endRule.small f (s+lag+A.endRule.offset)) b)
    (hfailed : A.Failed f (s+lag) (A.anchor f (b-A.endRule.tail) (s+lag)))
    (hprefix : AgreesOn fp f s k) (hsuffix : AgreesOn f fq k (min b b')) :
    decoded=actual ∧ b'=b ∧ update A clock T ρ β early γ f s b (s+lag) actual.1.input = decoded.1.output := by
  have ht : SuffixDecoder.origin p lag k actual=s+lag := by dsimp [SuffixDecoder.origin];rw [hp.cut];ring
  have hdiff : SuffixDecoder.origin p lag k actual-SuffixDecoder.origin p lag k reference =
      p reference-p actual := by dsimp [SuffixDecoder.origin];ring
  have hdec := SuffixDecoder.sound A hw hq.decoder hvis hsuffix
    (by simpa only [hdiff,abs_sub_comm] using hover)
    (by simpa only [hdiff,abs_sub_comm] using hover') (ht ▸ hend) (ht ▸ hfailed)
  have hnew : Suffix A clock T ρ β early p lag reference actual fq k b := by
    simpa only [hdec.1,hdec.2] using hq
  have hsuffix' : AgreesOn f fq k b := by simpa only [hdec.2,min_self] using hsuffix
  refine ⟨hdec.1,hdec.2,?_⟩
  rw [hdec.1]
  exact same_slot_sound A clock T ρ β early γ p lag hearly hearly₀ hblock hw hp hnew hvis hb hprefix hsuffix'

lemma hypothetical_actual {f : ℤ → Alphabet} {s b t : ℤ}
    (hsa : s ≤ s+early (Fin.last g')) (hab : s+early (Fin.last g') ≤ b)
    (hstart : ∀ i q, A.inner f i (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t=some q →
      s+early (Fin.last g') ≤ q) :
    hypothetical A clock T ρ β early f s b t (product T f s (s+early (Fin.last g'))) =
      Homogenization.lift (ρ (product T f s b))
        (ClockAffine.shift clock ρ β Tag.input Tag.output (A.φ (A.anchor f (b-A.endRule.tail) t-t))
          (OuterStream.snapshot A T f s b t)) := by
  have hh := actual_eq_substitute T f hsa hab hstart
  change ClockAffine.hypothetical clock ρ β Tag.input Tag.output _ _ _ = _
  rw [ClockAffine.hypothetical_actual]
  unfold OuterStream.search
  rw [←hh]
  rfl

end InnerStream

end GeneralizedStarHeight

end OAI
