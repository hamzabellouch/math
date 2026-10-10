import OAI.Computability.StarHeight.LateSchedule

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uV uK uP uC uAlphabet2 uM2
universe uV2 uK2 uP2 uC2 uAlphabet3 uM3 uV3 uK3
universe uP3 uC3 uAlphabet4 uJ uC4 uAlphabet5 uT uP4
universe uC5

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma Cuts.multiple (G : Geometry A H) {h : ℤ} (hh : h ∈ H.offsets) : (A.B:ℤ) ∣ h := by
  obtain ⟨role,_,hh⟩ := Finset.mem_biUnion.mp hh
  obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hh
  exact dvd_add (G.multiple role) (dvd_mul_left _ _)

omit [Monoid M] [AddCommGroup V] [Fintype M] [Fintype V] [Fintype C] in
lemma available_guard (G : Geometry A H)
    (hwidth : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets, |h-h'| ≤ A.w)
    {t k b Q reference : ℤ} {f : ℤ → Alphabet} {tag : Tag M V g A.B}
    (hc : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B)
    (hr : reference ∈ H.offsets) (hn : ¬A.Failed f t Q)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b) :
    A.endRule.Guard (H.origins k) (k-reference) k b f ∧
      suffixAnchor A reference k b f = A.anchor f (b-A.endRule.tail) t := by
  have hm : k-reference ∈ H.origins k := Finset.mem_image.mpr ⟨reference,hr,rfl⟩
  have hstable : ∀ o ∈ H.origins k,
      A.endRule.small f (o+A.endRule.offset) = A.endRule.small f (t+A.endRule.offset) ∧
      A.endRule.large f (o+A.endRule.offset) = A.endRule.large f (t+A.endRule.offset) := by
    intro o ho
    obtain ⟨a,ha,hk⟩ := hc
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ho
    have hmem := H.offset_mem (H.tagRole tag) a ha
    have heq : k-h = t+(H.base (H.tagRole tag)+a*A.B-h) := by omega
    rw [heq]
    exact A.not_failed_end hn (hwidth _ hmem h hh)
      (dvd_sub (H.multiple A G hmem) (H.multiple A G hh))
  have hover := G.origin_overlap hc hm
  refine ⟨A.endRule.guard_available hm (G.actual_visibility hc he) hstable hover.1 hover.2 he,?_⟩
  simp only [suffixAnchor,ExceptionalOrigins.Parameters.anchor,(hstable _ hm).2]

end OuterStream

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma net_displacement {B R a a' : ℕ} (ha : a<R) (ha' : a'<R) :
    |(a:ℤ)*B-a'*B| ≤ (B*R:ℕ) := by
  have haB := Nat.mul_le_mul_right B ha.le
  have haB' := Nat.mul_le_mul_right B ha'.le
  have h₁ : (a:ℤ)*B ≤ (R:ℤ)*B := by exact_mod_cast haB
  have h₂ : (a':ℤ)*B ≤ (R:ℤ)*B := by exact_mod_cast haB'
  have hp : 0 ≤ (a:ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hp' : 0 ≤ (a':ℤ)*B := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  rw [abs_le,Nat.cast_mul,mul_comm (B:ℤ)]
  omega

lemma available_main (G : Geometry A H) (hW : A.W=clock.W)
    (hnet : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a<H.R ∧ dist (A.φ (a*A.B)) v < clock.ρ)
    (hw₀ : (A.B*H.R:ℕ) ≤ A.w₀)
    (hwidth : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets, |h-h'| ≤ A.w)
    (hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c))
    {s t b reference : ℤ} {f : ℤ → Alphabet}
    (hr : reference ∈ H.offsets)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hn : ¬A.Failed f t (A.anchor f (b-A.endRule.tail) t))
    (hpos : ∀ (j : Fin g) (a : ℕ), a<H.R → s<t+H.main j+a*A.B ∧ t+H.main j+a*A.B≤b)
    (hpre : ∀ (j : Fin g) (a : ℕ), a<H.R → ∀ (i : Fin (g+1)), i.val≤j.val →
      A.InnerVisible s (t+H.main j+a*A.B) t i (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (hpost : ∀ (j : Fin g) (a : ℕ), a<H.R → ∀ a', a'<H.R → ∀ (i : Fin (g+1)), j.val < i.val →
      A.InnerVisible (t+H.main j+a*A.B) b (t+(a*A.B-a'*A.B)) i
        (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (hv : ∀ i, A.InnerVisible s b t i (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (hp : ∀ i, A.inner f i (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t ≠ none)
    (x : V) :
    ∃ (tag : MainTag M V g A.B) (k : ℤ), tag.input=x ∧
      Prefix A H clock T ρ β (.inl tag) f s t k ∧
      Suffix A H clock T ρ reference (.inl tag) f k b ∧
      tag.output=update A clock T ρ β f s b t x := by
  let q := A.anchor f (b-A.endRule.tail) t
  let u := A.residue (q-t)
  have hz : A.φ (q-t) ∉ clock.W := by rw [←hW]; exact A.not_failed_clock hn
  have hpres := G.present hv hp
  obtain ⟨tag,hu,hx,hp',hq',hout⟩ := ObservedMain.available T ρ β f s b (search A f u t) hpres u x hβ
  obtain ⟨a,ha,hi,hj⟩ := ClockAffine.net_cut clock A.φ A.B hnet hz (.inl tag) (H.main tag.j)
  let k := t+H.main tag.j+a*A.B
  have hc : ∃ a : ℕ, a<H.count (H.tagRole (.inl tag)) ∧ k=t+H.base (H.tagRole (.inl tag))+a*A.B :=
    ⟨a,ha,rfl⟩
  have hst : ∀ a', a'<H.R → ∀ i,
      A.inner f i u (t+(a*A.B-a'*A.B)) = A.inner f i u t := by
    intro a' ha' i
    exact A.not_failed_inner hn ((net_displacement ha ha').trans hw₀) i
  have hsref : ∀ i, A.inner f i u (k-H.main tag.j) = A.inner f i u t := by
    intro i
    convert hst 0 H.R_pos i using 1; dsimp [k]; congr 1; ring
  have hmpos : Monotone (positions (search A f u t)) := by
    obtain ⟨pos,hpos,hm,_,_⟩ := hpres
    change ∀ i, search A f u t i=some (pos i) at hpos
    have heq : positions (search A f u t)=pos := by
      funext i
      simp only [positions,hpos,Option.getD_some]
    rw [heq]
    exact hm
  have hprefix : Prefix A H clock T ρ β (.inl tag) f s t k := by
    refine ⟨(hpos tag.j a ha).1,hc,?_,?_⟩
    · convert hi using 1; dsimp [k]; congr 1; ring
    · change PrefixMain A T ρ β tag f s t k
      refine ⟨?_,?_⟩
      · simpa only [hu] using hpre tag.j a ha
      · rw [hu]
        refine ⟨hp',?_,?_⟩
        · intro i hii
          exact A.inner_position_bounds (hpre tag.j a ha i hii) (hp i)
        · intro i _
          exact hmpos (Fin.castSucc_le_succ i)
  obtain ⟨hguard,hanchor⟩ := available_guard A H G hwidth hc hr hn he
  have hsuffix : Suffix A H clock T ρ reference (.inl tag) f k b := by
    refine ⟨(hpos tag.j a ha).2,hguard,?_,?_,?_⟩
    · rw [hanchor]
      convert hj using 1
      rw [←map_sub]
      congr 1
      dsimp [q,k]
      ring
    · rw [hanchor]
      change A.residue (q-k)=tag.u
      exact (residue_shift (A := A) (G.cut_multiple hc)).symm.trans hu.symm
    · change SuffixMain A H T tag f k b
      refine ⟨?_,?_,?_⟩
      · rw [hu]
        intro a' ha' i hii
        convert hpost tag.j a ha a' ha' i hii using 1; dsimp [k]; ring
      · rw [hu]
        intro a' ha' i _
        rw [hsref]
        convert hst a' ha' i using 1; dsimp [k]; congr 1; ring
      · rw [hu]
        have hread : ObservedMain.SuffixRead T tag f k b (search A f u t) := by
          refine ⟨hq',?_,?_⟩
          · intro i hii
            have hvis := hpost tag.j a ha a ha i hii
            rw [sub_self,add_zero] at hvis
            exact A.inner_position_bounds hvis (hp i)
          · intro i _; exact hmpos (Fin.castSucc_le_succ i)
        apply hread.transfer T (fun _ _ _ => rfl)
        intro i _
        exact (hsref i).symm
  refine ⟨tag,k,hx,hprefix,hsuffix,?_⟩
  change tag.output = ClockAffine.update clock ρ β Tag.input Tag.output
    (A.φ (q-t)) (actual T f s b (search A f u t)) x
  simp only [ClockAffine.update,ClockAffine.shift,ClockAffine.no_off_outside clock hz]
  cases hboundaries : (actual T f s b (search A f u t)).boundaries <;>
    simpa only [hboundaries] using hout

end OuterStream

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

variable {Alphabet : Type uAlphabet3} {M : Type uM3} {V : Type uV3} {K : Type uK3} {P : Type uP3} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma available_periodic (G : Geometry A H) (hW : A.W=clock.W)
    (hnet : ∀ v : C → RobustClock.Circle, ∃ a : ℕ, a<H.R ∧ dist (A.φ (a*A.B)) v < clock.ρ)
    (hwidth : ∀ h ∈ H.offsets, ∀ h' ∈ H.offsets, |h-h'| ≤ A.w)
    {s t b reference : ℤ} {f : ℤ → Alphabet}
    (hr : reference ∈ H.offsets)
    (he : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f (t+A.endRule.offset)
      (A.endRule.small f (t+A.endRule.offset)) b)
    (hn : ¬A.Failed f t (A.anchor f (b-A.endRule.tail) t))
    (hpos : ∀ (j : Fin (g+1)) (u : Fin A.B) (a : ℕ), a<H.N →
      s<t+H.periodic j u+a*A.B ∧ t+H.periodic j u+a*A.B≤b)
    (hpre : ∀ (j : Fin (g+1)) (a : ℕ), a<H.N →
      A.InnerVisible s (t+H.periodic j (A.residue (A.anchor f (b-A.endRule.tail) t-t))+a*A.B)
        t j (A.residue (A.anchor f (b-A.endRule.tail) t-t)))
    (j : Fin (g+1))
    (hp : A.inner f j (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t = none)
    {n step : ℕ} (hnpos : 0<n) (hnperiod : A.φ n=0)
    (hcop : Nat.Coprime (step*A.B) n)
    (hprog : ∀ a : ℕ, a<n → a*step<H.N ∧
      product T f s (t+H.periodic j (A.residue (A.anchor f (b-A.endRule.tail) t-t))+a*step*A.B) =
        product T f s (t+H.periodic j (A.residue (A.anchor f (b-A.endRule.tail) t-t))))
    (x : V) :
    ∃ (tag : PeriodicTag M V g A.B) (k : ℤ), tag.input=x ∧
      Prefix A H clock T ρ β (.inr tag) f s t k ∧
      Suffix A H clock T ρ reference (.inr tag) f k b ∧
      tag.output=update A clock T ρ β f s b t x := by
  let q := A.anchor f (b-A.endRule.tail) t
  let u := A.residue (q-t)
  let tag : PeriodicTag M V g A.B := ⟨j,u,product T f s (t+H.periodic j u),x,ρ (product T f s b) x⟩
  have hz : A.φ (q-t) ∉ clock.W := by rw [←hW]; exact A.not_failed_clock hn
  obtain ⟨a₀,_,hi,hj⟩ := ClockAffine.net_cut clock A.φ A.B hnet hz (.inr tag) (H.periodic j u)
  obtain ⟨a,ha,hclock⟩ := PeriodicClock.sweep A.φ hnpos hnperiod hcop (H.periodic j u) (a₀*A.B)
  have hindex := (hprog a ha).1
  let k := t+H.periodic j u+(a*step:ℕ)*A.B
  have hkeq : k-t=H.periodic j u+(a:ℤ)*(step*A.B:ℕ) := by
    dsimp [k]
    ring
  have hpreclock : A.φ (k-t) ∈ clock.I (.inr tag) := by rw [hkeq,hclock];exact hi
  have hpostclock : A.φ (q-k) ∈ clock.J (.inr tag) := by
    rw [show q-k=(q-t)-(k-t) by ring,map_sub,hkeq,hclock]
    exact hj
  have hc : ∃ a' : ℕ, a'<H.count (H.tagRole (.inr tag)) ∧
      k=t+H.base (H.tagRole (.inr tag))+a'*A.B := ⟨a*step,hindex,rfl⟩
  have hprod : product T f s k=tag.prefixProduct := by
    simpa only [k, Nat.cast_mul] using (hprog a ha).2
  have hk := hpos j u (a*step) hindex
  have hprefix : Prefix A H clock T ρ β (.inr tag) f s t k :=
    ⟨hk.1,hc,hpreclock,⟨hpre j (a*step) hindex,hp,hprod⟩⟩
  obtain ⟨hguard,hanchor⟩ := available_guard A H G hwidth hc hr hn he
  have hsuffix : Suffix A H clock T ρ reference (.inr tag) f k b := by
    refine ⟨hk.2,hguard,?_,?_,?_⟩
    · rw [hanchor];exact hpostclock
    · rw [hanchor]
      exact (residue_shift (A := A) (G.cut_multiple hc)).symm
    · change ρ (product T f s b) x = ρ (tag.prefixProduct*product T f k b) x
      rw [←hprod,←product_append T f hk.1.le hk.2]
  refine ⟨tag,k,rfl,hprefix,hsuffix,?_⟩
  have hnone := factors_absent T f (s := s) (b := b) (search := search A f u t) (i := j) hp
  change ρ (product T f s b) x = ClockAffine.update clock ρ β Tag.input Tag.output
    (A.φ (q-t)) (actual T f s b (search A f u t)) x
  rw [ClockAffine.update_periodic clock ρ β Tag.input Tag.output _
    (ClockAffine.no_off_outside clock hz) hnone]
  rfl

end OuterStream

namespace ExceptionalOrigins.Parameters

variable {Alphabet : Type uAlphabet4} {J : Type uJ} {C : Type uC4} (A : Parameters Alphabet J C)

lemma residue_cast (u : Fin A.B) : A.residue u=u := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [residue_val,Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast u.isLt)]

end ExceptionalOrigins.Parameters

namespace SourceSchedule.Early

open WordIntervals LocalMarkers SplitMetadata BoundarySnapshot
open scoped Classical BigOperators

variable {Alphabet : Type uAlphabet5} {T : Type uT} {P : Type uP4} {C : Type uC5} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)
    (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))

lemma earlyLast_nonneg : 0 ≤ S.β (Fin.last g') := by
  rw [←S.β_zero]
  exact S.β_strict.monotone (Fin.zero_le _)

lemma offset_envelope {a : ℤ} (ha : a ∈ (S.cuts g).offsets) : |a| ≤ S.envelope g := by
  have hh := abs_le_finiteBound ha
  have hw' := S.sweepWidth_pos g
  have hrest : 0 ≤ 2*|((B*S.R:ℕ):ℤ)|+|S.rule.r|+
      (absoluteBound (fun j : Fin (g+1) => S.inner.boundary j.val):ℤ)+
      (absoluteBound S.inner.H:ℤ)+|S.inner.extension|+
      (3*(innerD S.p (B*S.R))^2+1:ℕ)+(size*innerD S.p (B*S.R):ℕ) := by positivity
  dsimp only [envelope]
  omega

lemma cut_bounds {f : ℤ → Alphabet} {s b a : ℤ} (ha : a ∈ (S.cuts g).offsets)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b) :
    s<s+L.lag+a ∧ s+L.lag+a<b := by
  have hbound := abs_le.mp (S.offset_envelope g ha)
  have hlag := L.lag_margin
  have hlast := S.earlyLast_nonneg
  have hoff := L.offset_margin
  have hb := L.complete_lower he
  have hw := (S.sweepWidth_pos g).le
  have hwidth := L.endRule.width_nonneg
  have hr := L.radius_nonneg
  have hK : (0:ℤ) ≤ L.endRule.K := Int.natCast_nonneg _
  constructor <;> omega

lemma shifted_inner_visible (hB : 0<B) {f : ℤ → Alphabet} {s b δ : ℤ}
    (hδ : |δ| ≤ S.sweepWidth g)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin (g+1)) (u : Fin B) :
    (S.parameters g L hB).InnerVisible (s+S.β (Fin.last g')) b (s+L.lag+δ) j u := by
  let A := S.parameters g L hB
  have hh := S.actual_visible g L hB (Q := s+L.lag+δ+u) hδ he
  have hw : 0 ≤ A.w₀ := Int.natCast_nonneg _
  have hv := ExceptionalOrigins.Parameters.Visible.innerVisible A hh hw j
  rw [show s+L.lag+δ+(u:ℤ)-(s+L.lag+δ)=(u:ℤ) by ring] at hv
  have hres : A.residue (u:ℤ)=u := A.residue_cast u
  rw [hres] at hv
  exact hv

lemma main_prefix_visible (hB : 0<B) {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin g) (a : ℕ) (i : Fin (g+1)) (hi : i.val≤j.val) (u : Fin B) :
    (S.parameters g L hB).InnerVisible s (s+L.lag+(S.cuts g).main j+a*B) (s+L.lag) i u := by
  have hw : |(0:ℤ)|≤S.sweepWidth g := by simpa using (S.sweepWidth_pos g).le
  have hv := S.shifted_inner_visible g L hB hw he i u
  have hm := S.inner.main_before hB (by have := S.rule.radius_ge;omega) i.val j.val a u hi
  have hlast := S.earlyLast_nonneg
  constructor
  · have hh := hv.1
    change s + S.β (Fin.last g') ≤ s + L.lag + 0 + S.inner.boundary i.val - S.rule.r at hh
    change s ≤ s + L.lag + S.inner.boundary i.val - S.rule.r
    omega
  · change s+L.lag+S.inner.boundary i.val+S.inner.H u+S.rule.r ≤
      s+L.lag+S.inner.mainBase j.val+a*B
    change S.inner.boundary i.val+S.inner.H u+S.rule.r < S.inner.mainBase j.val+a*B at hm
    omega

lemma main_suffix_visible (hB : 0<B) {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin g) (a a' : ℕ) (ha : a<S.R) (ha' : a'<S.R)
    (i : Fin (g+1)) (hi : j.val < i.val) (u : Fin B) :
    (S.parameters g L hB).InnerVisible (s+L.lag+(S.cuts g).main j+a*B) b
      (s+L.lag+(a*B-a'*B)) i u := by
  have hδ : |(a:ℤ)*B-a'*B|≤S.sweepWidth g := by
    have hh := S.offsets_difference g ((S.cuts g).offset_mem (.inl j) a ha)
      ((S.cuts g).offset_mem (.inl j) a' ha')
    change |(S.cuts g).main j+a*B-((S.cuts g).main j+a'*B)|<S.sweepWidth g at hh
    rw [show (S.cuts g).main j+(a:ℤ)*B-((S.cuts g).main j+a'*B)=a*B-a'*B by ring] at hh
    exact hh.le
  have hv := S.shifted_inner_visible g L hB hδ he i u
  have hm := S.inner.main_after hB (by have := S.rule.radius_ge;omega)
    i.val j.val a' (s+L.lag+S.inner.mainBase j.val+a*B) hi ha'
  constructor
  · change s+L.lag+S.inner.mainBase j.val+a*B ≤
      s+L.lag+(a*B-a'*B)+S.inner.boundary i.val-S.rule.r
    omega
  · exact hv.2

lemma periodic_prefix_visible (hB : 0<B) {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (j : Fin (g+1)) (u : Fin B) (a : ℕ) :
    (S.parameters g L hB).InnerVisible s (s+L.lag+(S.cuts g).periodic j u+a*B) (s+L.lag) j u := by
  have hw : |(0:ℤ)|≤S.sweepWidth g := by simpa using (S.sweepWidth_pos g).le
  have hv := S.shifted_inner_visible g L hB hw he j u
  have hm := S.inner.periodic_before j.val a u
  have hlast := S.earlyLast_nonneg
  constructor
  · have hh := hv.1
    change s + S.β (Fin.last g') ≤ s + L.lag + 0 + S.inner.boundary j.val - S.rule.r at hh
    change s ≤ s + L.lag + S.inner.boundary j.val - S.rule.r
    omega
  · change s+L.lag+S.inner.boundary j.val+S.inner.H u+S.rule.r ≤
      s+L.lag+(S.inner.boundary j.val+S.inner.H u+S.inner.lag+0*B)+a*B
    change S.inner.boundary j.val+S.inner.H u+S.rule.r <
      S.inner.boundary j.val+S.inner.H u+S.inner.lag+a*B at hm
    omega

end SourceSchedule.Early

end GeneralizedStarHeight

end OAI
