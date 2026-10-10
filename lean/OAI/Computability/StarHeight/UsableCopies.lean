import OAI.Computability.StarHeight.OriginBounds

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uV uK uP uC uAlphabet2 uM2
universe uV2 uK2 uP2 uC2 uAlphabet3 uAlphabet4 uT uP3
universe uC3 uAlphabet5 uM3 uV3 uK3 uC4 uP4

namespace SourceSchedule.Early

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical BigOperators

variable {Alphabet : Type uAlphabet} {M : Type uM} {V : Type uV} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C]
    {g g' B : ℕ} {clock : RobustClock.Specification (Tag M V g B) P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B (Fintype.card M) label reserved)
    (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B) (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

lemma outer_available
    (hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c))
    {f : ℤ → Alphabet} {s b reference : ℤ}
    (hr : reference ∈ (S.cuts g).offsets)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (hn : ¬(S.parameters g L hB).Failed f (s+L.lag)
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) (s+L.lag))) (x : V) :
    ∃ (tag : Tag M V g B) (k : ℤ), tag.input=x ∧
      OuterStream.Prefix (S.parameters g L hB) (S.cuts g) clock T ρ β tag f s (s+L.lag) k ∧
      OuterStream.Suffix (S.parameters g L hB) (S.cuts g) clock T ρ reference tag f k b ∧
      tag.output=OuterStream.update (S.parameters g L hB) clock T ρ β f s b (s+L.lag) x := by
  let A := S.parameters g L hB
  let H := S.cuts g
  let t := s+L.lag
  let q := A.anchor f (b-A.endRule.tail) t
  let u := A.residue (q-t)
  have hpos : ∀ (role : H.Role) (a : ℕ), a<H.count role →
      s<t+H.base role+a*B ∧ t+H.base role+a*B ≤ b := by
    intro role a ha
    have hh := S.cut_bounds g L (H.offset_mem role a ha) he
    dsimp only [t]
    exact ⟨by omega,by omega⟩
  have hvis : ∀ i, A.InnerVisible s b t i u := by
    intro i
    have hh := S.shifted_inner_visible g L hB
      (δ := 0) (by simpa using (S.sweepWidth_pos g).le) he i u
    simp only [add_zero] at hh
    have hlast := S.earlyLast_nonneg
    exact ⟨by have := hh.1;dsimp only [A,t] at *;omega,hh.2⟩
  have hwidth : ∀ a ∈ H.offsets, ∀ a' ∈ H.offsets, |a-a'| ≤ A.w := by
    intro a ha a' ha'
    exact (S.offsets_difference g ha ha').le
  by_cases hp : ∀ i, A.inner f i u t ≠ none
  · obtain ⟨tag,k,hx,hpre,hsuf,hout⟩ := OuterStream.available_main A H clock T ρ β
      (S.geometry g L hB) rfl S.net (le_refl _) hwidth hβ hr he hn
      (fun j a ha => hpos (.inl j) a ha)
      (fun j a _ i hi => S.main_prefix_visible g L hB he j a i hi u)
      (fun j a ha a' ha' i hi => S.main_suffix_visible g L hB he j a a' ha ha' i hi u)
      hvis hp x
    exact ⟨.inl tag,k,hx,hpre,hsuf,hout⟩
  · push Not at hp
    obtain ⟨j,hj⟩ := hp
    let z := t+S.inner.boundary j.val
    have hboundary : 0 ≤ S.inner.boundary j.val := by
      exact mul_nonneg (Int.natCast_nonneg _) (by have := S.inner.gap_pos;omega)
    have hs : s ≤ z+innerD S.p (B*S.R) := by
      have hl := L.lag_pos
      have hd : (0:ℤ) ≤ innerD S.p (B*S.R) := Int.natCast_nonneg _
      dsimp [z,t]
      omega
    have hnomarker : ∀ y, z ≤ y → y ≤ z+S.inner.H u+S.inner.extension → y∉S.rule.markers f :=
      A.not_failed_absent hn j hj
    obtain ⟨p,hp,hpd,hprogress⟩ := PeriodicCuts.progression S.inner S.rule
      (innerD_ge S.p (B*S.R)) (by omega) (by have := S.rule.radius_ge;omega)
      hB S.period_pos T f s z u hs hnomarker
    have hcop : Nat.Coprime (p*(Fintype.card M).factorial*B) S.period := by
      apply PeriodicClock.progression_coprime S.denominator S.prime hp hpd
        (Nat.factorial_pos _) hB
      intro c
      have hh := S.den_large c
      exact ⟨(le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hh),
        (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hh),
        (le_max_left _ _).trans_lt hh⟩
    have hprog : ∀ a : ℕ, a<S.period → a*(p*(Fintype.card M).factorial)<H.N ∧
        product T f s (t+H.periodic j u+(a:ℤ)*(p*(Fintype.card M).factorial:ℕ)*B) =
          product T f s (t+H.periodic j u) := by
      intro a ha
      obtain ⟨ha',hprod⟩ := hprogress a ha
      refine ⟨by simpa only [H,cuts,period,Nat.mul_assoc] using ha',?_⟩
      have h₁ : t+H.periodic j u+(a:ℤ)*(p*(Fintype.card M).factorial:ℕ)*B =
          z+S.inner.H u+S.inner.lag+(a*p*(Fintype.card M).factorial*B:ℕ) := by
        dsimp only [H,cuts,IntegerSchedules.Inner.periodicOffset,z]
        push_cast
        ring
      have h₂ : t+H.periodic j u=z+S.inner.H u+S.inner.lag := by
        dsimp only [H,cuts,IntegerSchedules.Inner.periodicOffset,z]
        ring
      rw [h₁,h₂]
      exact hprod
    obtain ⟨tag,k,hx,hpre,hsuf,hout⟩ := OuterStream.available_periodic A H clock T ρ β
      (S.geometry g L hB) rfl S.net hwidth hr he hn
      (fun j u a ha => hpos (.inr (j,u)) a ha)
      (fun j a _ => S.periodic_prefix_visible g L hB he j u a) j hj S.period_pos
      (PeriodicClock.period S.denominator S.numerator (fun c => (S.prime c).pos)) hcop hprog x
    exact ⟨.inr tag,k,hx,hpre,hsuf,hout⟩

end SourceSchedule.Early

namespace InnerStream

open WordIntervals SplitMetadata LocalMarkers

variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype P] [Fintype C] {g g' μ : ℕ}
    (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

lemma available
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    {s b H : ℤ} {f : ℤ → Alphabet} (reference : Roster M (V × K) K g' μ)
    (hbad : (A.bad p f (s+lag) (b-A.endRule.tail)).card < μ)
    (hvis : ∀ a i, A.Visible (s+p a) b (s+lag+(p a-p i))
      (A.anchor f (b-A.endRule.tail) (s+lag+(p a-p i))))
    (hnear : ∀ i j, |p i-p j| ≤ H)
    (hnest : (A.endRule.d : ℤ)+(A.endRule.B-1)*A.endRule.S+H ≤ 3*A.endRule.d)
    (hover : (A.endRule.d : ℤ)^2 ≤ A.endRule.K-H) (hover' : H<A.endRule.K)
    (hend : EpisodeEnd.EndAt A.endRule.d A.endRule.K A.endRule.tail f
      (s+lag+A.endRule.offset) (A.endRule.small f (s+lag+A.endRule.offset)) b)
    (hfailed : A.Failed f (s+lag) (A.anchor f (b-A.endRule.tail) (s+lag))) (x : V × K) :
    ∃ (slot : Roster M (V × K) K g' μ) (k : ℤ), slot.1.input=x ∧
      Prefix T early γ p slot f s k ∧
      Suffix A clock T ρ β early p lag reference slot f k b ∧
      slot.1.output=update A clock T ρ β early γ f s b (s+lag) x := by
  let ψ := hypothetical A clock T ρ β early f s b (s+lag)
  obtain ⟨kind,hx,hp,hq,hout⟩ := ObservedInner.available T γ f (fun i => s+early i) ψ x (hγ ψ)
  obtain ⟨copy,hcopy⟩ := SuffixDecoder.available_copy A p lag s b H f reference kind
    hbad hvis hnear hnest hover hover' hend hfailed
  let slot : Roster M (V × K) K g' μ := (kind,copy)
  have hs : s+p slot-p slot=s := by ring
  refine ⟨slot,s+p slot,hx,⟨rfl,hp⟩,⟨hcopy,?_⟩,hout⟩
  simpa only [hs] using hq

end InnerStream

namespace SourceSchedule.Late

variable {Alphabet : Type uAlphabet3} {B : ℕ} {h w E earlyLast : ℤ}
    (L : Late Alphabet B h w E earlyLast)

lemma count_margins (hB : 0<B) (hh : 0 ≤ h) (hw : 0 ≤ w) :
    2*h+2*w<L.endRule.S ∧
    2*h+((B:ℤ)-1)*L.endRule.S+2*w<L.endRule.d ∧
    2*h+2*((B:ℤ)-1)*L.endRule.S<L.endRule.d := by
  have hS := L.endRule.S_nonneg
  have hBi : (1:ℤ) ≤ B := by exact_mod_cast hB
  have hBS : 0 ≤ (B:ℤ)*L.endRule.S := mul_nonneg (by omega) hS
  have hs := L.spacing
  have hd := L.separation
  constructor
  · omega
  constructor <;> nlinarith

lemma decoder_margins (hB : 0<B) (hh : 0 ≤ h) (hw : 0 ≤ w) :
    (L.endRule.d:ℤ)+(L.endRule.B-1)*L.endRule.S+h ≤ 3*L.endRule.d ∧
    (L.endRule.d:ℤ)^2 ≤ L.endRule.K-h ∧ h<L.endRule.K := by
  have hBi : (1:ℤ) ≤ B := by exact_mod_cast hB
  have hS := L.endRule.S_nonneg
  have hBS : 0 ≤ (B:ℤ)*L.endRule.S := mul_nonneg (by omega) hS
  have hd := L.separation
  have hd₂ : (2:ℤ) ≤ L.endRule.d := by exact_mod_cast L.endRule.d_ge
  have hK := L.endRule.seed_long
  have hK' : 3*(L.endRule.d:ℤ)^2<L.endRule.K := by exact_mod_cast hK
  rw [L.modulus]
  have hh' : h<L.endRule.d := by nlinarith
  refine ⟨?_,?_,?_⟩ <;> nlinarith [sq_nonneg (L.endRule.d:ℤ)]

end SourceSchedule.Late

namespace SourceSchedule.Early

open scoped Classical

variable {Alphabet : Type uAlphabet4} {T : Type uT} {P : Type uP3} {C : Type uC3} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)
    (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B)

lemma full_bad_card
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (μ : ℕ) (hμ : 20*(10000000*Real.log (2*Fintype.card T)+4*(g+1))+10<μ)
    (f : ℤ → Alphabet) (t q₀ : ℤ) :
    ((S.parameters g L hB).bad S.p f t q₀).card<μ := by
  have hm : ∀ i j, (S.p i-S.p j)%B=(reserved i-reserved j)%B := by
    intro i j
    rw [Int.sub_emod,S.reserved_eq,S.reserved_eq,←Int.sub_emod]
  have hmar := L.count_margins hB S.diameter_pos.le (S.sweepWidth_pos g).le
  have hmod' : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (S.p i-S.p j)%(S.parameters g L hB).B ≠
        (S.p i'-S.p j')%(S.parameters g L hB).B := by
    intro i j i' j' hij hij' hn
    change (S.p i-S.p j)%B ≠ (S.p i'-S.p j')%B
    rw [hm,hm]
    exact hmod i j i' j' hij hij' hn
  have hgap₀ : 2*(S.parameters g L hB).w₀ ≤ 2*(B*S.R:ℕ)+2 := by
    change 2*((B*S.R:ℕ):ℤ) ≤ 2*((B*S.R:ℕ):ℤ)+2
    omega
  have hinner : 2*S.diameter+2*(S.parameters g L hB).w₀ < (S.parameters g L hB).d := by
    have hh := innerD_bound S.p (B*S.R)
    change 2*S.diameter+2*(B*S.R:ℕ)<(innerD S.p (B*S.R):ℤ)
    have hpos := S.diameter_pos
    have hBR : (0:ℤ) ≤ (B*S.R:ℕ) := Int.natCast_nonneg _
    change 10*(2*S.diameter+2*(B*S.R:ℕ)+5)<(innerD S.p (B*S.R):ℤ) at hh
    omega
  have hwidth : ∀ u v, u ≠ v → 2*S.diameter+
      2*max (S.parameters g L hB).ext (S.parameters g L hB).w₀ <
        |(S.parameters g L hB).H u-(S.parameters g L hB).H v| := by
    intro u v huv
    have hh := S.inner.H_separated u v huv
    change 2*S.diameter+2*max S.inner.extension (B*S.R:ℕ) < |S.inner.H u-S.inner.H v|
    change 2*S.diameter+2*max S.inner.extension (B*S.R:ℕ)+2 < |S.inner.H u-S.inner.H v| at hh
    omega
  exact ExceptionalOrigins.Parameters.bad_card (S.parameters g L hB) clock S.p S.diameter
    (2*(B*S.R)+2) rfl S.approximate
    (fun i j => difference_bound S.p i j) hmod' S.separated (Int.natCast_nonneg _)
    hgap₀ hinner hwidth hmar.1 hmar.2.1 hmar.2.2 μ
    (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hμ) f t q₀

end SourceSchedule.Early

namespace SourceSchedule.Early

open WordIntervals SplitMetadata LocalMarkers

variable {Alphabet : Type uAlphabet5} {M : Type uM3} {V : Type uV3} {K : Type uK3} {C : Type uC4} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype C]
    {g g' μ B : ℕ}
    {clock : RobustClock.Specification (Tag M V g B) (Roster M (V × K) K g' μ) C}
    {reserved : Roster M (V × K) K g' μ → ℤ}
    (S : Early (Alphabet := Alphabet) clock B (Fintype.card M) (fun i => i.1.j) reserved)
    (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B) (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

omit [Monoid M] in
lemma roster_visible {f : ℤ → Alphabet} {s b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (a i : Roster M (V × K) K g' μ) :
    (S.parameters g L hB).Visible (s+S.p a) b (s+L.lag+(S.p a-S.p i))
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) (s+L.lag+(S.p a-S.p i))) := by
  apply ExceptionalOrigins.Parameters.Visible.mono _
    (S.actual_visible g L hB (S.stencil_difference g a i).le he) _ (le_refl _)
  have hb := (S.block a).2.trans_le (S.β_strict.monotone (Fin.le_last _))
  omega

lemma inner_available
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    {f : ℤ → Alphabet} {s b : ℤ} (reference : Roster M (V × K) K g' μ)
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (s+L.lag+L.endRule.offset) (L.endRule.small f (s+L.lag+L.endRule.offset)) b)
    (hf : (S.parameters g L hB).Failed f (s+L.lag)
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) (s+L.lag))) (x : V × K) :
    ∃ (slot : Roster M (V × K) K g' μ) (k : ℤ), slot.1.input=x ∧
      InnerStream.Prefix T S.β γ S.p slot f s k ∧
      InnerStream.Suffix (S.parameters g L hB) clock T ρ β S.β S.p L.lag reference slot f k b ∧
      slot.1.output=InnerStream.update (S.parameters g L hB) clock T ρ β S.β γ f s b (s+L.lag) x := by
  have hm := L.decoder_margins hB S.diameter_pos.le (S.sweepWidth_pos g).le
  exact InnerStream.available (S.parameters g L hB) clock T ρ β S.β γ S.p L.lag hγ reference
    (S.full_bad_card g L hB hmod μ hμ f (s+L.lag) (b-L.endRule.tail))
    (S.roster_visible L hB he) (difference_bound S.p) hm.1 hm.2.1 hm.2.2 he hf x

end SourceSchedule.Early

namespace SlotResidues

variable (P : Type uP4) [Fintype P]

noncomputable def slotIndex (p : P) : ℤ := ((Fintype.equivFin P) p).val+1
noncomputable def reserved (p : P) : ℤ := representative (Fintype.card P) (slotIndex P p)
noncomputable def slotModulus : ℕ := 20*(Fintype.card P+1)^3

lemma slotIndex_bounds (p : P) : 1 ≤ slotIndex P p ∧ slotIndex P p ≤ Fintype.card P := by
  have hh := ((Fintype.equivFin P) p).isLt
  dsimp [slotIndex]
  omega

lemma slotIndex_injective : Function.Injective (slotIndex P) := by
  intro a b hh
  apply (Fintype.equivFin P).injective
  apply Fin.ext
  dsimp [slotIndex] at hh
  omega

lemma reserved_distinct (i j i' j' : P) (hij : i ≠ j) (hij' : i' ≠ j')
    (hn : (i,j) ≠ (i',j')) :
    (reserved P i-reserved P j)%slotModulus P ≠
      (reserved P i'-reserved P j')%slotModulus P := by
  have hi := slotIndex_bounds P i
  have hj := slotIndex_bounds P j
  have hi' := slotIndex_bounds P i'
  have hj' := slotIndex_bounds P j'
  have hN : (0:ℤ)<Fintype.card P := by omega
  intro hh
  have hB : (slotModulus P:ℤ)=modulus (Fintype.card P) := by
    simp only [slotModulus,modulus,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rw [hB] at hh
  obtain ⟨h₁,h₂⟩ := distinct_differences hN hi.1 hi.2 hj.1 hj.2 hi'.1 hi'.2 hj'.1 hj'.2
    ((slotIndex_injective P).ne hij) ((slotIndex_injective P).ne hij') hh
  exact hn (Prod.ext ((slotIndex_injective P) h₁) ((slotIndex_injective P) h₂))

lemma slotModulus_pos : 0<slotModulus P := by dsimp [slotModulus];positivity

end SlotResidues

end GeneralizedStarHeight

end OAI
