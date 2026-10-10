import OAI.Computability.StarHeight.StreamTranslation

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uAlphabet2 uJ uC uAlphabet3 uM uV uK
universe uP uC2 uAlphabet4 uM2 uV2 uK2 uP2 uC3
universe uAlphabet5 uAlphabet6 uJ2 uC4 uAlphabet7

namespace CanonicalEpisodes.Parameters

open WordIntervals LocalMarkers EpisodeEnd
variable {Alphabet : Type uAlphabet} (C : CanonicalEpisodes.Parameters Alphabet)

lemma end_congr {f g : ℤ → Alphabet} {s b z : ℤ}
    (hv : C.Visible s b z) (he : AgreesOn f g s b)
    (hf : EndAt C.d C.K C.tail f z (C.small f z) b) :
    EndAt C.d C.K C.tail g z (C.small g z) b := by
  rw [←(C.searches_congr hv he).1]
  cases hη : C.small f z with
  | some q => simpa only [hη,EndAt] using hf
  | none =>
    rw [hη] at hf
    obtain ⟨v,hv',hm⟩ := hf
    refine ⟨v,(shortCont_congr (fun x hx hx' => he x (hv.2.2.1.trans hx)
      (hx'.trans_le hv.2.2.2))).mp hv',hm.1,?_,?_⟩
    · intro h
      apply hm.2.1
      exact (he _ (by have := hm.1; have := hv.2.2.1;omega) (by have := C.tail_pos;omega)).trans h
    · intro x hx hx'
      exact (he x (hv.2.2.1.trans hx) (by have := C.tail_pos;omega)).symm.trans (hm.2.2 x hx hx')

lemma complete_realizes {lag : ℤ} {w : List Alphabet} (hw : w∈C.complete lag)
    {f : ℤ → Alphabet} (hf : Realizes w 0 f) :
    C.Visible 0 w.length (lag+C.offset) ∧
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) w.length := by
  obtain ⟨g,hg,hv,he⟩ := hw
  refine ⟨hv,C.end_congr hv ?_ he⟩
  simpa only [zero_add] using hg.same hf

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

open WordIntervals LocalMarkers
variable {Alphabet : Type uAlphabet2} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma anchor_congr {f g : ℤ → Alphabet} {s b t Q : ℤ}
    (hv : A.Visible s b t Q) (he : AgreesOn f g s b) :
    A.anchor f (b-A.endRule.tail) t=A.anchor g (b-A.endRule.tail) t := by
  unfold anchor
  rw [(A.endRule.searches_congr hv.base he).2]

lemma failedLanguage_iff {f : ℤ → Alphabet} {w : List Alphabet} {t : ℤ}
    (hw₀ : 0≤A.w₀) (hv : A.Visible 0 w.length t (A.anchor f (w.length-A.endRule.tail) t)) (hf : Realizes w 0 f) :
    w∈A.failedLanguage t ↔ A.Failed f t (A.anchor f (w.length-A.endRule.tail) t) := by
  constructor
  · rintro ⟨g,hg,hg'⟩
    have he : AgreesOn g f 0 w.length := by simpa only [zero_add] using hg.same hf
    have hq := A.anchor_congr hv he
    rw [hq] at hg'
    exact (A.Failed_congr hw₀ hv he).mp hg'
  · exact fun hh => ⟨f,hf,hh⟩

end ExceptionalOrigins.Parameters

namespace OuterStream

open WordIntervals LocalMarkers BoundarySnapshot SplitMetadata
variable {Alphabet : Type uAlphabet3} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

omit [Fintype M] [Fintype C] in
lemma snapshot_congr {f f' : ℤ → Alphabet} {s b t : ℤ} (hs : s≤b)
    (he : AgreesOn f f' s b) (hw₀ : 0≤A.w₀)
    (hv : A.Visible s b t (A.anchor f (b-A.endRule.tail) t)) :
    snapshot A T f s b t=snapshot A T f' s b t := by
  have hq := A.anchor_congr hv he
  have hsearch : search A f (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t=
      search A f' (A.residue (A.anchor f' (b-A.endRule.tail) t-t)) t := by
    rw [←hq]
    funext j
    exact A.inner_congr (hv.innerVisible A hw₀ j) he
  apply ClockAffine.Snapshot.ext (product_congr T hs he)
  change factors T f s b _=factors T f' s b _
  rw [←hsearch]
  exact factors_congr T he

lemma update_congr {f f' : ℤ → Alphabet} {s b t : ℤ} (hs : s≤b)
    (he : AgreesOn f f' s b) (hw₀ : 0≤A.w₀)
    (hv : A.Visible s b t (A.anchor f (b-A.endRule.tail) t)) (x : V) :
    update A clock T ρ β f s b t x=update A clock T ρ β f' s b t x := by
  unfold update
  rw [A.anchor_congr hv he,snapshot_congr A T hs he hw₀ hv]

noncomputable def wordUpdate [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) (x : V) : V :=
  update A clock T ρ β (stream w) 0 w.length lag x

lemma wordUpdate_eq [Nonempty Alphabet] {lag : ℤ} {w : List Alphabet} {f : ℤ → Alphabet}
    (hf : Realizes w 0 f) (hw₀ : 0≤A.w₀)
    (hv : A.Visible 0 w.length lag (A.anchor f (w.length-A.endRule.tail) lag)) (x : V) :
    wordUpdate A clock T ρ β lag w x=update A clock T ρ β f 0 w.length lag x := by
  symm
  apply update_congr A clock T ρ β (Int.natCast_nonneg _) _ hw₀ hv
  simpa only [zero_add] using hf.same (stream_realizes w)

end OuterStream

namespace InnerStream

open WordIntervals LocalMarkers SplitMetadata
variable {Alphabet : Type uAlphabet4} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

lemma update_congr (hm : Monotone early) (h₀ : early 0=0)
    {f f' : ℤ → Alphabet} {s b t : ℤ} (hb : s+early (Fin.last g')≤b)
    (he : AgreesOn f f' s b) (hw₀ : 0≤A.w₀)
    (hv : A.Visible s b t (A.anchor f (b-A.endRule.tail) t)) (x : V × K) :
    update A clock T ρ β early γ f s b t x=update A clock T ρ β early γ f' s b t x := by
  have hmin (i : Fin (g'+1)) : 0≤early i := by rw [←h₀];exact hm (Fin.zero_le i)
  have hψ := hypothetical_congr A clock T ρ β early (by have := hmin (Fin.last g');omega)
    hb he (A.anchor_congr hv he) (fun j => hv.innerVisible A hw₀ j)
  have hd : (fun i : Fin g' => product T f (s+early i.castSucc) (s+early i.succ))=
      fun i : Fin g' => product T f' (s+early i.castSucc) (s+early i.succ) := by
    funext i
    apply product_congr T (by have := hm (Fin.castSucc_le_succ i);omega)
    intro z hz hz'
    exact he z (by have := hmin i.castSucc;omega) (by have := hm (Fin.le_last i.succ);omega)
  unfold update
  rw [hψ,hd]

noncomputable def wordUpdate [Nonempty Alphabet] (lag : ℤ) (w : List Alphabet) (x : V × K) : V × K :=
  update A clock T ρ β early γ (stream w) 0 w.length lag x

lemma wordUpdate_eq [Nonempty Alphabet] (hm : Monotone early) (h₀ : early 0=0)
    {lag : ℤ} {w : List Alphabet} {f : ℤ → Alphabet} (hb : early (Fin.last g')≤w.length)
    (hf : Realizes w 0 f) (hw₀ : 0≤A.w₀)
    (hv : A.Visible 0 w.length lag (A.anchor f (w.length-A.endRule.tail) lag)) (x : V × K) :
    wordUpdate A clock T ρ β early γ lag w x=update A clock T ρ β early γ f 0 w.length lag x := by
  symm
  apply update_congr A clock T ρ β early γ hm h₀ (by simpa only [zero_add] using hb) _ hw₀ hv
  simpa only [zero_add] using hf.same (stream_realizes w)

end InnerStream

namespace CanonicalEpisodes.Parameters

open WordIntervals
variable {Alphabet : Type uAlphabet5} (C : CanonicalEpisodes.Parameters Alphabet)

lemma subset_height [Finite Alphabet] {L : Language Alphabet} (lag : ℤ)
    (hreg : L.IsRegular) (hL : L≤C.complete lag) : HasHeightAtMost L 1 := by
  apply C.ending_height L hreg lag.natAbs
  intro w hw
  obtain ⟨f,hf,_,he⟩ := hL hw
  exact ⟨f,lag,hf,by simp only [Int.natCast_natAbs];exact le_rfl,he⟩

lemma complete_height [Finite Alphabet] (lag : ℤ) : HasHeightAtMost (C.complete lag) 1 :=
  C.subset_height lag (C.complete_regular lag) le_rfl

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet6} {J : Type uJ2} {C : Type uC4} (A : ExceptionalOrigins.Parameters Alphabet J C)

def failedDomain (lag : ℤ) : Language Alphabet := A.endRule.complete lag ⊓ A.failedLanguage lag

lemma failedDomain_subset (lag : ℤ) : A.failedDomain lag≤A.endRule.complete lag := inf_le_left

lemma failedDomain_height [Finite Alphabet] [Fintype J] (n : ℕ) (hn : 0<n)
    (hφ : A.φ (n:ℤ)=0) (hw₀ : 0≤A.w₀) (lag : ℤ) : HasHeightAtMost (A.failedDomain lag) 1 :=
  A.endRule.subset_height lag ((A.endRule.complete_regular lag).inf (A.failed_regular n hn hφ hw₀ lag))
    (A.failedDomain_subset lag)

end ExceptionalOrigins.Parameters

namespace WordIntervals

variable {Alphabet : Type uAlphabet7}

lemma realizes_cut {w : List Alphabet} {f : ℤ → Alphabet} (hf : Realizes w 0 f)
    {k : ℤ} (hk : 0≤k) (hkb : k≤w.length) :
    ∃ u v : List Alphabet, w=u++v ∧ (u.length:ℤ)=k ∧ Realizes u 0 f ∧ Realizes v k f := by
  let u := w.take k.toNat
  let v := w.drop k.toNat
  have hw : w=u++v := (List.take_append_drop k.toNat w).symm
  have hu : (u.length:ℤ)=k := by simp only [u,List.length_take];omega
  have hh : Realizes (u++v) 0 f := hw ▸ hf
  refine ⟨u,v,hw,hu,hh.append_left,?_⟩
  simpa only [zero_add,hu] using hh.append_right

lemma prefix_eq_of_length {u v w : List Alphabet} (hu : u<+:w) (hv : v<+:w)
    (hl : u.length=v.length) : u=v := by
  rcases List.prefix_or_prefix_of_prefix hu hv with h|h
  · exact h.eq_of_length hl
  · exact (h.eq_of_length hl.symm).symm

end WordIntervals

end GeneralizedStarHeight

end OAI
