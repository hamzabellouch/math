import OAI.Computability.StarHeight.PeriodicSplicing

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uJ uC uAlphabet2 uJ2 uC2 uAlphabet3 uAlphabet4
universe uJ3 uC3 uAlphabet5 uM uAlphabet6 uJ4 uC4 uP
universe uAlphabet7 uM2 uJ5 uC5 uAlphabet8 uAlphabet9 uJ6 uC6

namespace StreamSplice.Frame

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet} {J : Type uJ} {C : Type uC} {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y) (A : ExceptionalOrigins.Parameters Alphabet J C)

include H

lemma anchor_phase {t b : ℤ} (hv : A.endRule.Visible (-N) N (t+A.endRule.offset))
    (hd : (A.B:ℤ) ∣ (y.length:ℤ)-x.length)
    (hφ : A.φ ((y.length:ℤ)-x.length)=0) :
    A.residue (A.anchor f (b-A.endRule.tail) t-t)=
      A.residue (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-t) ∧
    A.φ (A.anchor f (b-A.endRule.tail) t-t)=
      A.φ (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-t) := by
  have hs := (A.endRule.searches_congr hv (H.agrees_left (le_refl N))).2
  unfold ExceptionalOrigins.Parameters.anchor
  rw [←hs]
  cases hζ : A.endRule.large f (t+A.endRule.offset) with
  | some q => simp only [Option.getD_some,and_self]
  | none =>
    simp only [Option.getD_none]
    constructor
    · apply A.residue_eq_of_dvd
      convert hd using 1
      ring
    · rw [show b+((y.length:ℤ)-x.length)-A.endRule.tail-t=
        (b-A.endRule.tail-t)+((y.length:ℤ)-x.length) by ring,map_add,hφ,add_zero]

lemma failed {t b : ℤ} (hw₀ : 0≤A.w₀)
    (hv : A.Visible (-N) N t (A.anchor f (b-A.endRule.tail) t))
    (hd : (A.B:ℤ) ∣ (y.length:ℤ)-x.length)
    (hφ : A.φ ((y.length:ℤ)-x.length)=0) :
    A.Failed f t (A.anchor f (b-A.endRule.tail) t) ↔
      A.Failed f' t (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t) := by
  have hphase := H.anchor_phase A (b := b) hv.base hd hφ
  exact A.Failed_phase_congr hw₀ hv (H.agrees_left (le_refl N)) hphase.2 hphase.1

end StreamSplice.Frame

namespace ExceptionalOrigins.Parameters

open LocalMarkers WordIntervals StreamSplice
variable {Alphabet : Type uAlphabet2} {J : Type uJ2} {C : Type uC2} (A : ExceptionalOrigins.Parameters Alphabet J C)

def failedLanguage (t : ℤ) : Language Alphabet := {w | ∃ f : ℤ → Alphabet,
  Realizes w 0 f ∧ A.Failed f t (A.anchor f (w.length-A.endRule.tail) t)}

lemma failed_regular [Finite Alphabet] [Fintype J] (n : ℕ) (hn : 0<n)
    (hφ : A.φ (n:ℤ)=0) (hw₀ : 0≤A.w₀) (t : ℤ) : (A.failedLanguage t).IsRegular := by
  classical
  obtain ⟨N,_,hN⟩ := A.exists_horizon t.natAbs
  have ht : |t|≤(t.natAbs:ℤ) := by rw [Int.natCast_natAbs]
  let : NeZero (A.B*n) := ⟨Nat.ne_of_gt (Nat.mul_pos A.B_pos hn)⟩
  let T := PeriodicSummary.lengthMod (Alphabet := Alphabet) (A.B*n)
  apply FiniteRecognition.regular_sandwich T N 0
  intro a b x y ha hb he
  have hbnil : b=[] := List.length_eq_zero_iff.mp hb
  subst b
  have trans : ∀ x y : List Alphabet, T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y) →
      a++x++[]∈A.failedLanguage t → a++y++[]∈A.failedLanguage t := by
    intro x y he ⟨f,hf,hfail⟩
    let f' := splice f N x y
    have H : Frame f f' N x y := by simpa only [ha] using splice_frame hf y
    have hdiv := PeriodicSummary.lengthMod_dvd he
    have hB : (A.B:ℤ)∣(y.length:ℤ)-x.length :=
      (show (A.B:ℤ)∣(A.B*n:ℕ) by exact_mod_cast dvd_mul_right A.B n).trans hdiv
    have hn' : (n:ℤ)∣(y.length:ℤ)-x.length :=
      (show (n:ℤ)∣(A.B*n:ℕ) by exact_mod_cast dvd_mul_left n A.B).trans hdiv
    have hδ : A.φ ((y.length:ℤ)-x.length)=0 := by
      obtain ⟨k,hk⟩ := hn'
      rw [hk,mul_comm,←Int.zsmul_eq_mul,map_zsmul,hφ,smul_zero]
    have hh := (H.failed A hw₀ (hN t ht _) hB hδ).mp hfail
    refine ⟨f',by simpa only [ha] using splice_realizes hf y,?_⟩
    have hl : ((a++y++[]).length:ℤ)=((a++x++[]).length:ℤ)+((y.length:ℤ)-x.length) := by
      simp only [List.length_append,List.length_nil,Nat.cast_add,Nat.cast_zero]
      omega
    rw [hl]
    exact hh
  exact ⟨trans x y he,trans y x he.symm⟩

end ExceptionalOrigins.Parameters
namespace CanonicalEpisodes.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma exists_uniform_horizon (D : ℕ) : ∃ N : ℕ, D<N ∧ ∀ (t : ℤ), |t|≤(D:ℤ) →
    C.Visible (-(N:ℤ)) N (t+C.offset) ∧
      t+C.offset+(C.d:ℤ)+(C.B-1)*C.S<N := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((D:ℤ)+|C.offset|+C.width+|C.rule.r|+C.K+1)
  have ho := abs_le.mp (le_refl |C.offset|)
  have hr := abs_le.mp (le_refl |C.rule.r|)
  have hw := C.width_nonneg
  have hs := C.small_width_le
  refine ⟨N,by omega,?_⟩
  intro t ht
  have ht' := abs_le.mp ht
  exact ⟨⟨by omega,by omega,by omega,by omega⟩,by omega⟩

end CanonicalEpisodes.Parameters

namespace ExceptionalOrigins.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet4} {J : Type uJ3} {C : Type uC3} (A : ExceptionalOrigins.Parameters Alphabet J C)

lemma exists_inner_horizon [Fintype J] (D : ℕ) : ∃ N : ℕ, D<N ∧
    ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ j u, A.InnerVisible (-(N:ℤ)) N t j u := by
  let U : ℤ := (SourceSchedule.absoluteBound A.offset:ℤ)
  let H : ℤ := (SourceSchedule.absoluteBound A.H:ℤ)
  obtain ⟨N,hN⟩ := exists_nat_gt ((D:ℤ)+U+H+|A.innerRule.r|+1)
  have hU : 0≤U := by dsimp [U];positivity
  have hH : 0≤H := by dsimp [H];positivity
  have hr := abs_le.mp (le_refl |A.innerRule.r|)
  refine ⟨N,by omega,?_⟩
  intro t ht j u
  have ht' := abs_le.mp ht
  have hj' := abs_le.mp (SourceSchedule.abs_le_absoluteBound A.offset j)
  have hu' := abs_le.mp (SourceSchedule.abs_le_absoluteBound A.H u)
  change -↑N≤t+A.offset j-A.innerRule.r ∧ t+A.offset j+A.H u+A.innerRule.r≤N
  dsimp [U,H] at hN
  constructor <;> omega

lemma InnerVisible.mono {s b s' b' t : ℤ} {j : J} {u : Fin A.B}
    (hv : A.InnerVisible s b t j u) (hs : s' ≤ s) (hb : b ≤ b') :
    A.InnerVisible s' b' t j u := ⟨hs.trans hv.1,hv.2.trans hb⟩

lemma Visible.from_bounds {s b s' N b' t Q Q' : ℤ}
    (hv : A.Visible s b t Q) (hN : A.Visible s' N t Q')
    (hb : N ≤ b') : A.Visible s b' t Q' := by
  refine ⟨⟨hv.base.1,hN.base.2.1.trans hb,hv.base.2.2.1,hN.base.2.2.2.trans hb⟩,?_,?_⟩
  · intro v hv' hw
    exact ⟨(hv.ends v hv' hw).1,(hN.ends v hv' hw).2.trans hb⟩
  · intro j
    exact ⟨(hv.inner j).1,(hN.inner j).2.trans hb⟩

end ExceptionalOrigins.Parameters

namespace StreamSplice.Frame

open LocalMarkers WordIntervals BoundarySnapshot
variable {Alphabet : Type uAlphabet5} {M : Type uM} [Monoid M] {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y) (T : FreeMonoid Alphabet →* M)

include H

lemma factors {g : ℕ} {s b : ℤ} (hb : N+x.length≤b)
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y))
    (search : Fin (g+1) → Option ℤ) (hsearch : ∀ i q, search i=some q → q≤N) :
    BoundarySnapshot.factors T f' s (b+((y.length:ℤ)-x.length)) search=
      BoundarySnapshot.factors T f s b search := by
  classical
  have hbN : N≤b := by omega
  have hbN' : N≤b+((y.length:ℤ)-x.length) := by omega
  have hp : Present search s b ↔ Present search s (b+((y.length:ℤ)-x.length)) := by
    constructor
    · rintro ⟨p,hp,hm,hs,_⟩
      exact ⟨p,hp,hm,hs,(hsearch _ _ (hp _)).trans hbN'⟩
    · rintro ⟨p,hp,hm,hs,_⟩
      exact ⟨p,hp,hm,hs,(hsearch _ _ (hp _)).trans hbN⟩
  by_cases hpres : Present search s b
  · obtain ⟨p,hp',hm,hs',hb'⟩ := hpres
    rw [factors_present T f hp' hm hs' hb',
      factors_present T f' hp' hm hs' ((hsearch _ _ (hp' _)).trans hbN')]
    congr 2
    · exact (product_congr T hs' (H.agrees_left (hsearch _ _ (hp' _)))).symm
    · funext i
      exact (product_congr T (hm (Fin.castSucc_le_succ i))
        (H.agrees_left (hsearch _ _ (hp' _)))).symm
    · exact H.product T hT (hsearch _ _ (hp' _)) hb
  · simp only [BoundarySnapshot.factors,dite_eq_right hpres,dite_eq_right (mt hp.mpr hpres)]

lemma later {g : ℕ} {s b : ℤ} (hs : s≤N) (hb : N+x.length≤b)
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y))
    (search : Fin (g+1) → Option ℤ) (hsearch : ∀ i q, search i=some q → q≤N) :
    BoundarySnapshot.later T f' s (b+((y.length:ℤ)-x.length)) search=
      BoundarySnapshot.later T f s b search := by
  apply BoundarySnapshot.later_ext
  · exact H.product T hT hs hb
  · exact H.factors T hb hT search hsearch

end StreamSplice.Frame

namespace StreamSplice.Frame

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet6} {J : Type uJ4} {C : Type uC4} {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y)

include H

lemma guard (E : CanonicalEpisodes.Parameters Alphabet) {O : Finset ℤ} {r k b : ℤ}
    (hN : ∀ t∈O, E.Visible (-N) N (t+E.offset) ∧
      t+E.offset+(E.d:ℤ)+(E.B-1)*E.S<N)
    (hb : N+x.length≤b-E.tail)
    (hd : (E.d.factorial:ℤ)∣(y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := E.d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (hg : E.Guard O r k b f) : E.Guard O r k (b+((y.length:ℤ)-x.length)) f' := by
  have hbN : N≤b+((y.length:ℤ)-x.length) := by have := E.tail_pos;omega
  have hs := fun t ht => E.searches_congr (hN t ht).1 (H.agrees_left (le_refl N))
  refine ⟨hg.1,?_,?_,H.endAt (hN r hg.1).1 (hN r hg.1).2 hb hd hm hg.2.2.2⟩
  · intro t ht
    have hv := hg.2.1 t ht
    have hv' := (hN t ht).1
    exact ⟨hv.1,hv'.2.1.trans hbN,hv.2.2.1,hv'.2.2.2.trans hbN⟩
  · intro t ht
    rw [←(hs t ht).1,←(hs r hg.1).1,←(hs t ht).2,←(hs r hg.1).2]
    exact hg.2.2.1 t ht

lemma anchor_relative_phase (A : ExceptionalOrigins.Parameters Alphabet J C) {t b r : ℤ}
    (hv : A.endRule.Visible (-N) N (t+A.endRule.offset))
    (hd : (A.B:ℤ)∣(y.length:ℤ)-x.length)
    (hφ : A.φ ((y.length:ℤ)-x.length)=0) :
    A.residue (A.anchor f (b-A.endRule.tail) t-r)=
      A.residue (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-r) ∧
    A.φ (A.anchor f (b-A.endRule.tail) t-r)=
      A.φ (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) t-r) := by
  have hs := (A.endRule.searches_congr hv (H.agrees_left (le_refl N))).2
  unfold ExceptionalOrigins.Parameters.anchor
  rw [←hs]
  cases A.endRule.large f (t+A.endRule.offset) with
  | some q => simp only [Option.getD_some,and_self]
  | none =>
    simp only [Option.getD_none]
    constructor
    · apply A.residue_eq_of_dvd
      convert hd using 1
      ring
    · rw [show b+((y.length:ℤ)-x.length)-A.endRule.tail-r=
        (b-A.endRule.tail-r)+((y.length:ℤ)-x.length) by ring,map_add,hφ,add_zero]

lemma decoder (A : ExceptionalOrigins.Parameters Alphabet J C) {P : Type uP}
    {τ : P → ℤ} {reference decoded : P} {k b : ℤ} (hw₀ : 0≤A.w₀)
    (hN : ∀ t, A.Visible (-N) N (τ t) (A.anchor f (b-A.endRule.tail) (τ t)))
    (hN' : ∀ t Q, A.Visible (-N) N (τ t) Q)
    (hstrict : ∀ t, τ t+A.endRule.offset+(A.endRule.d:ℤ)+
      (A.endRule.B-1)*A.endRule.S<N)
    (hb : N+x.length≤b-A.endRule.tail)
    (hd : (A.endRule.d.factorial:ℤ)∣(y.length:ℤ)-x.length)
    (hm : PeriodicSummary.transition (p := A.endRule.d.factorial) (FreeMonoid.ofList x)=
      PeriodicSummary.transition (FreeMonoid.ofList y))
    (hB : (A.B:ℤ)∣(y.length:ℤ)-x.length) (hφ : A.φ ((y.length:ℤ)-x.length)=0)
    (ht : SuffixDecoder.Test A τ reference k b f decoded) :
    SuffixDecoder.Test A τ reference k (b+((y.length:ℤ)-x.length)) f' decoded := by
  have hbN : N≤b+((y.length:ℤ)-x.length) := by have := A.endRule.tail_pos;omega
  have hs := fun t => A.endRule.searches_congr (hN t).base (H.agrees_left (le_refl N))
  have hfail := fun t => H.failed A hw₀ (hN t) hB hφ
  refine ⟨?_,?_,⟨(hfail decoded).mp ht.unique.1,?_⟩,?_⟩
  · intro t
    exact ExceptionalOrigins.Parameters.Visible.from_bounds A (ht.visible t) (hN' t _) hbN
  · intro habsent
    have ha : ∃ i, A.endRule.large f (τ i+A.endRule.offset)=none := by
      obtain ⟨i,hi⟩ := habsent
      exact ⟨i,(hs i).2.trans hi⟩
    have hg := ht.reference_guard ha
    refine ⟨fun i => (hs i).1.symm.trans (hg.1 i),?_⟩
    exact H.endAt (hN reference).base (hstrict reference) hb hd hm hg.2
  · intro i hi
    exact ht.unique.2 i ((hfail i).mpr hi)
  · exact H.endAt (hN decoded).base (hstrict decoded) hb hd hm ht.final_guard

end StreamSplice.Frame
namespace StreamSplice

open LocalMarkers WordIntervals
variable {Alphabet : Type uAlphabet7} {M : Type uM2} {J : Type uJ5} {C : Type uC5} [Monoid M]

def wordTest (R : (ℤ → Alphabet) → ℤ → Prop) : Language Alphabet :=
  {w | ∃ f, Realizes w 0 f ∧ R f w.length}

structure SummaryEq (A : ExceptionalOrigins.Parameters Alphabet J C)
    (T : FreeMonoid Alphabet →* M) (x y : List Alphabet) : Prop where
  monoid_eq : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y)
  residue_dvd : (A.B:ℤ)∣(y.length:ℤ)-x.length
  period_dvd : (A.endRule.d.factorial:ℤ)∣(y.length:ℤ)-x.length
  matcher_eq : PeriodicSummary.transition (p := A.endRule.d.factorial) (FreeMonoid.ofList x)=
    PeriodicSummary.transition (FreeMonoid.ofList y)
  clock_eq : A.φ ((y.length:ℤ)-x.length)=0

lemma clock_eq_of_dvd (φ : ℤ →+ (C → RobustClock.Circle)) {n : ℕ}
    (hφ : φ (n:ℤ)=0) {δ : ℤ} (hδ : (n:ℤ)∣δ) : φ δ=0 := by
  obtain ⟨k,rfl⟩ := hδ
  rw [mul_comm,←Int.zsmul_eq_mul,map_zsmul,hφ,smul_zero]

lemma wordTest_regular [Finite Alphabet] [Finite M]
    (A : ExceptionalOrigins.Parameters Alphabet J C) (T : FreeMonoid Alphabet →* M)
    (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0) (N : ℕ)
    (R : (ℤ → Alphabet) → ℤ → Prop)
    (hc : ∀ (f f' : ℤ → Alphabet) (b : ℤ) (x y : List Alphabet),
      Frame f f' N x y → (N:ℤ)+x.length≤b-A.endRule.tail →
      SummaryEq A T x y → R f b → R f' (b+((y.length:ℤ)-x.length))) :
    (wordTest R).IsRegular := by
  classical
  let p := A.endRule.d.factorial
  let m := A.B*n*p
  have hp : 0<p := Nat.factorial_pos _
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos A.B_pos hn) hp
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  let : Fintype M := Fintype.ofFinite M
  let : Fintype ((Function.End (Option (ZMod p)))ᵐᵒᵖ) :=
    Fintype.ofEquiv (Option (ZMod p) → Option (ZMod p))
      (Equiv.refl _ |>.trans MulOpposite.opEquiv)
  let U := (T.prod (PeriodicSummary.lengthMod m)).prod (PeriodicSummary.transition (p := p))
  apply FiniteRecognition.regular_sandwich U N A.endRule.tail.toNat
  intro a b x y ha hb he
  have ht : (A.endRule.tail.toNat:ℤ)=A.endRule.tail := Int.toNat_of_nonneg A.endRule.tail_pos.le
  have trans : ∀ (x y : List Alphabet), U (FreeMonoid.ofList x)=U (FreeMonoid.ofList y) →
      a++x++b∈wordTest R → a++y++b∈wordTest R := by
    intro x y he ⟨f,hf,hw⟩
    let f' := splice f N x y
    have H : Frame f f' N x y := by simpa only [ha] using splice_frame hf y
    have hdiv := PeriodicSummary.lengthMod_dvd (congrArg (Prod.snd ∘ Prod.fst) he)
    have hB : (A.B:ℤ)∣(y.length:ℤ)-x.length :=
      (show (A.B:ℤ)∣(m:ℤ) by exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_right A.B n) p).trans hdiv
    have hn' : (n:ℤ)∣(y.length:ℤ)-x.length :=
      (show (n:ℤ)∣(m:ℤ) by exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_left n A.B) p).trans hdiv
    have hp' : (p:ℤ)∣(y.length:ℤ)-x.length :=
      (show (p:ℤ)∣(m:ℤ) by exact_mod_cast dvd_mul_left p (A.B*n)).trans hdiv
    have hh := hc f f' _ x y H (by simp only [List.length_append,Nat.cast_add,ha,hb];omega)
      ⟨congrArg (Prod.fst ∘ Prod.fst) he,hB,hp',congrArg Prod.snd he,clock_eq_of_dvd A.φ hφ hn'⟩ hw
    refine ⟨f',by simpa only [ha] using splice_realizes hf y,?_⟩
    have hl : ((a++y++b).length:ℤ)=((a++x++b).length:ℤ)+((y.length:ℤ)-x.length) := by
      simp only [List.length_append,Nat.cast_add]
      omega
    rw [hl]
    exact hh
  exact ⟨trans x y he,trans y x he.symm⟩

end StreamSplice

namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd
variable {Alphabet : Type uAlphabet8} (C : CanonicalEpisodes.Parameters Alphabet)

lemma ending_middle (L : Language Alphabet) (D : ℕ)
    (hL : ∀ w∈L, ∃ f t, Realizes w 0 f ∧ |t|≤(D:ℤ) ∧
      EndAt C.d C.K C.tail f (t+C.offset) (C.small f (t+C.offset)) w.length) :
    ∃ N : ℕ, ∀ w∈L, w.length≤N+C.tail.toNat ∨ ∃ (f v : ℤ → Alphabet) (p : ℕ),
      Realizes w 0 f ∧ N+C.tail.toNat≤w.length ∧ 0<p ∧ p≤C.d ∧
        Function.Periodic v (p:ℤ) ∧ AgreesOn f v N (w.length-C.tail.toNat) := by
  obtain ⟨N,_,hN⟩ := C.exists_uniform_horizon D
  refine ⟨N,?_⟩
  intro w hw
  by_cases hl : w.length≤N+C.tail.toNat
  · exact Or.inl hl
  · right
    obtain ⟨f,t,hf,ht,he⟩ := hL w hw
    have htail : (C.tail.toNat:ℤ)=C.tail := Int.toNat_of_nonneg C.tail_pos.le
    cases hη : C.small f (t+C.offset) with
    | some q =>
      have hq := ((EndSearch.search_some C.B_pos C.S_nonneg).mp hη).1.2
      have hwidth := (EndSearch.width_bounds (x := q-(t+C.offset)) (a := C.d)
        C.B_pos C.S_nonneg).2
      have hright := (abs_le.mp (hq.trans hwidth)).2
      rw [hη] at he
      change (w.length:ℤ)=q+C.tail at he
      have hs := (hN t ht).2
      omega
    | none =>
      rw [hη] at he
      obtain ⟨v,hv,hmis⟩ := he
      obtain ⟨p,hp,hpd,hper⟩ := hv.1
      refine ⟨f,v,p,hf,by omega,hp,hpd.le,hper,?_⟩
      intro z hz hz'
      have hseed := (hN t ht).1.2.2.2
      exact hmis.2.2 z (by omega) (by omega)

lemma ending_height [Finite Alphabet] (L : Language Alphabet) (hreg : L.IsRegular) (D : ℕ)
    (hL : ∀ w∈L, ∃ f t, Realizes w 0 f ∧ |t|≤(D:ℤ) ∧
      EndAt C.d C.K C.tail f (t+C.offset) (C.small f (t+C.offset)) w.length) :
    HasHeightAtMost L 1 := by
  obtain ⟨N,hN⟩ := C.ending_middle L D hL
  exact PeriodicTemplates.regular_middle_height L hreg
    (N+C.tail.toNat) N C.tail.toNat C.d hN

end CanonicalEpisodes.Parameters
namespace ExceptionalOrigins.Parameters

open LocalMarkers
variable {Alphabet : Type uAlphabet9} {J : Type uJ6} {C : Type uC6} (A : ExceptionalOrigins.Parameters Alphabet J C)

structure Inspection (D N : ℕ) : Prop where
  contains : D<N
  full : ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ Q, A.Visible (-(N:ℤ)) N t Q
  inner : ∀ (t : ℤ), |t|≤(D:ℤ) → ∀ j u, A.InnerVisible (-(N:ℤ)) N t j u
  strict : ∀ (t : ℤ), |t|≤(D:ℤ) →
    t+A.endRule.offset+(A.endRule.d:ℤ)+(A.endRule.B-1)*A.endRule.S<N

lemma exists_inspection [Fintype J] (D : ℕ) : ∃ N : ℕ, A.Inspection D N := by
  obtain ⟨N₁,h₁,V₁⟩ := A.exists_horizon D
  obtain ⟨N₂,h₂,V₂⟩ := A.exists_inner_horizon D
  obtain ⟨N₃,h₃,V₃⟩ := A.endRule.exists_uniform_horizon D
  let N := max N₁ (max N₂ N₃)
  have n₁ : N₁≤N := le_max_left _ _
  have n₂ : N₂≤N := (le_max_left _ _).trans (le_max_right _ _)
  have n₃ : N₃≤N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N,⟨h₁.trans_le n₁,?_,?_,?_⟩⟩
  · intro t ht Q
    exact Visible.mono A (V₁ t ht Q) (by omega) (by omega)
  · intro t ht j u
    exact InnerVisible.mono A (V₂ t ht j u) (by omega) (by omega)
  · intro t ht
    exact (V₃ t ht).2.trans_le (by exact_mod_cast n₃)

end ExceptionalOrigins.Parameters

end GeneralizedStarHeight

end OAI
