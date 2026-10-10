import OAI.Computability.StarHeight.SplitLanguages

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uT uP uC uAlphabet2 uM uV uK
universe uC2 uAlphabet3 uM2 uAlphabet4 uM3 uV2 uK2

namespace SourceSchedule.Early

open WordIntervals SplitMetadata LocalMarkers
variable {Alphabet : Type uAlphabet} {T : Type uT} {P : Type uP} {C : Type uC} [Fintype T] [Fintype P] [Fintype C]
    {g' B size : ℕ} {clock : RobustClock.Specification T P C}
    {label : P → Fin g'} {reserved : P → ℤ}
    (S : Early (Alphabet := Alphabet) clock B size label reserved)
    (g : ℕ) (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B)

lemma clock_period : (S.parameters g L hB).φ (S.period:ℤ)=0 :=
  PeriodicClock.period S.denominator S.numerator (fun c => (S.prime c).pos)

lemma episode_last {f : ℤ → Alphabet} {b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (L.lag+L.endRule.offset) (L.endRule.small f (L.lag+L.endRule.offset)) b) :
    S.β (Fin.last g')≤b := by
  have hb := L.complete_lower (s := 0) (by simpa only [zero_add] using he)
  have hlag := L.lag_margin
  have hoff := L.offset_margin
  have hE := (S.envelope_pos g).le
  have hw := (S.sweepWidth_pos g).le
  have hr := L.radius_nonneg
  have hwidth := L.endRule.width_nonneg
  have hK : (0:ℤ)≤L.endRule.K := Int.natCast_nonneg _
  omega

lemma episode_visible {f : ℤ → Alphabet} {b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (L.lag+L.endRule.offset) (L.endRule.small f (L.lag+L.endRule.offset)) b) :
    (S.parameters g L hB).Visible 0 b L.lag
      ((S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag) := by
  have hh := S.actual_visible g L hB (s := 0) (δ := 0)
    (Q := (S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag)
    (by simpa only [abs_zero] using (S.sweepWidth_pos g).le)
    (by simpa only [zero_add] using he)
  simp only [zero_add,add_zero] at hh
  exact hh.mono _ S.earlyLast_nonneg (le_refl b)

lemma episode_inner_start {f : ℤ → Alphabet} {b : ℤ}
    (he : EpisodeEnd.EndAt L.endRule.d L.endRule.K L.endRule.tail f
      (L.lag+L.endRule.offset) (L.endRule.small f (L.lag+L.endRule.offset)) b)
    (i : Fin (g+1)) (q : ℤ)
    (hq : (S.parameters g L hB).inner f i
      ((S.parameters g L hB).residue ((S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag-L.lag))
      L.lag=some q) : S.β (Fin.last g')≤q := by
  have hv := S.actual_visible g L hB (s := 0) (δ := 0)
    (Q := (S.parameters g L hB).anchor f (b-L.endRule.tail) L.lag)
    (by simpa only [abs_zero] using (S.sweepWidth_pos g).le)
    (by simpa only [zero_add] using he)
  have hh := (hv.inner i).1
  have hq' := (S.parameters g L hB).inner_bounds hq
  have hr : 0≤(S.parameters g L hB).innerRule.r :=
    (Int.natCast_nonneg _).trans (S.parameters g L hB).innerRule.radius_ge
  have hw : 0≤(S.parameters g L hB).w₀ := Int.natCast_nonneg _
  simp only [zero_add,add_zero] at hh
  omega

end SourceSchedule.Early
namespace SourceSchedule.Early

open WordIntervals SplitMetadata LocalMarkers EpisodeAlgebra
variable {Alphabet : Type uAlphabet2} {M : Type uM} {V : Type uV} {K : Type uK} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype C] [Finite Alphabet] [Nonempty Alphabet]
    {g g' μ B : ℕ}
    {clock : RobustClock.Specification (Tag M V g B) (Roster M (V × K) K g' μ) C}
    {reserved : Roster M (V × K) K g' μ → ℤ}
    (S : Early (Alphabet := Alphabet) clock B (Fintype.card M) (fun i => i.1.j) reserved)
    (L : Late Alphabet B S.diameter (S.sweepWidth g) (S.envelope g) (S.β (Fin.last g')))
    (hB : 0<B) (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)

lemma inner_graph_height
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    (reference : Roster M (V × K) K g' μ) (x y : V × K) :
    HasHeightAtMost (graph ((S.parameters g L hB).failedDomain L.lag)
      (InnerStream.wordUpdate (S.parameters g L hB) clock T ρ β S.β γ L.lag) x y) 2 := by
  let A := S.parameters g L hB
  have hw₀ : 0≤A.w₀ := Int.natCast_nonneg _
  have hm := L.decoder_margins hB S.diameter_pos.le (S.sweepWidth_pos g).le
  have hs : SplitSound (A.failedDomain L.lag) (InnerStream.wordUpdate A clock T ρ β S.β γ L.lag)
      (InnerStream.prefixLanguage T S.β γ S.p)
      (InnerStream.suffixLanguage A clock T ρ β S.β S.p L.lag reference) := by
    apply InnerStream.word_sound A clock T ρ β S.β γ S.p L.lag reference
        S.β_strict S.β_zero S.block hw₀ (fun f b he => S.episode_visible g L hB he)
    · intro f b he a i
      have hh := S.roster_visible L hB (s := 0) (by simpa only [A,parameters,zero_add] using he) a i
      convert hh using 1 <;> simp only [SuffixDecoder.origin,zero_add] <;> congr 1 <;> ring
    · intro a
      have hh := difference_bound S.p a reference
      change |S.p a-S.p reference|≤S.diameter at hh
      change (L.endRule.d:ℤ)^2≤L.endRule.K-_
      omega
    · intro a
      exact (difference_bound S.p a reference).trans_lt hm.2.2
    · exact fun f b he => S.episode_last g L he
  have ha : SplitAvailable (A.failedDomain L.lag) 0 (InnerStream.wordUpdate A clock T ρ β S.β γ L.lag)
      (InnerStream.prefixLanguage T S.β γ S.p)
      (InnerStream.suffixLanguage A clock T ρ β S.β S.p L.lag reference) := by
    apply InnerStream.word_available A clock T ρ β S.β γ S.p L.lag reference
      S.β_strict.monotone S.β_zero S.block hw₀ (fun f b he => S.episode_visible g L hB he) (fun f b he => S.episode_last g L he)
    intro f b he hf x
    simpa only [zero_add] using S.inner_available L hB T ρ β γ hmod hμ hγ reference
      (s := 0) (by simpa only [A,parameters,zero_add] using he) (by simpa only [A,parameters,zero_add] using hf) x
  exact split_height (L.endRule.prefix_code L.lag) (A.failedDomain_subset L.lag) bot_le
    (InnerStream.wordUpdate A clock T ρ β S.β γ L.lag)
    (InnerStream.prefixLanguage T S.β γ S.p)
    (InnerStream.suffixLanguage A clock T ρ β S.β S.p L.lag reference) hs ha 0
    (A.failedDomain_height S.period S.period_pos (S.clock_period g L hB) hw₀ L.lag)
    (fun x => (InnerStream.prefix_height T S.β γ S.p x).mono (by decide))
    (InnerStream.suffix_height A clock T ρ β S.β S.p L.lag S.period S.period_pos
      (S.clock_period g L hB) hw₀ reference)
    (empty_skip_height _) x y

lemma failed_outer_graph_height
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    (reference : Roster M (V × K) K g' μ) (x y : V) :
    HasHeightAtMost (graph ((S.parameters g L hB).failedDomain L.lag)
      (OuterStream.wordUpdate (S.parameters g L hB) clock T ρ β L.lag) x y) 2 := by
  let A := S.parameters g L hB
  have hG := S.inner_graph_height L hB T ρ β γ hmod hμ hγ reference
  have hlin := AffineRecovery.recovery_height (L.endRule.prefix_code L.lag)
    (A.failedDomain_subset L.lag)
    (fun w => (InnerStream.wordLinear A clock T ρ β S.β L.lag w).toAddMonoidHom)
    (InnerStream.wordShift A clock T ρ β S.β γ L.lag) 2 (fun x y => by
      rw [←InnerStream.wordUpdate_affine A clock T ρ β S.β γ L.lag]
      exact hG x y)
  apply InnerStream.linear_graph_recovery A clock T ρ β S.β S.β_strict.monotone S.β_zero L.lag 2
    (fun w hw => S.episode_last g L (A.endRule.complete_realizes hw.1 (stream_realizes w)).2)
    (fun w hw => S.episode_inner_start g L hB (A.endRule.complete_realizes hw.1 (stream_realizes w)).2)
    hlin x y

lemma outer_graph_height
    (hmod : ∀ i j i' j', i ≠ j → i' ≠ j' → (i,j) ≠ (i',j') →
      (reserved i-reserved j)%B ≠ (reserved i'-reserved j')%B)
    (hμ : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ)
    (hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c))
    (hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ))
    (innerReference : Roster M (V × K) K g' μ) (outerReference : ℤ)
    (hr : outerReference∈(S.cuts g).offsets) (x y : V) :
    HasHeightAtMost (graph (L.endRule.complete L.lag)
      (OuterStream.wordUpdate (S.parameters g L hB) clock T ρ β L.lag) x y) 3 := by
  let A := S.parameters g L hB
  have hw₀ : 0≤A.w₀ := Int.natCast_nonneg _
  have hs := OuterStream.word_sound A (S.cuts g) clock T ρ β (S.geometry g L hB)
    L.lag outerReference hw₀ (fun f b he => S.episode_visible g L hB he)
  have ha : SplitAvailable (L.endRule.complete L.lag) (A.failedDomain L.lag)
      (OuterStream.wordUpdate A clock T ρ β L.lag)
      (OuterStream.prefixLanguage A (S.cuts g) clock T ρ β L.lag)
      (OuterStream.suffixLanguage A (S.cuts g) clock T ρ outerReference) := by
    apply OuterStream.word_available A (S.cuts g) clock T ρ β L.lag outerReference hw₀
      (fun f b he => S.episode_visible g L hB he)
    intro f b he hn x
    simpa only [A,parameters,zero_add] using S.outer_available L hB T ρ β hβ hr
      (s := 0) (by simpa only [A,parameters,zero_add] using he) (by simpa only [A,parameters,zero_add] using hn) x
  exact split_height (L.endRule.prefix_code L.lag) le_rfl (A.failedDomain_subset L.lag)
    (OuterStream.wordUpdate A clock T ρ β L.lag)
    (OuterStream.prefixLanguage A (S.cuts g) clock T ρ β L.lag)
    (OuterStream.suffixLanguage A (S.cuts g) clock T ρ outerReference) hs ha 2
    (L.endRule.complete_height L.lag)
    (fun x => (OuterStream.prefix_height A (S.cuts g) clock T ρ β L.lag x).mono (by decide))
    (OuterStream.suffix_height A (S.cuts g) clock T ρ S.period S.period_pos
      (S.clock_period g L hB) outerReference)
    (S.failed_outer_graph_height L hB T ρ β γ hmod hμ hγ innerReference) x y

end SourceSchedule.Early
namespace CanonicalEpisodes.Parameters

open LocalMarkers WordIntervals EpisodeEnd EpisodeAlgebra
variable {Alphabet : Type uAlphabet3} (C : CanonicalEpisodes.Parameters Alphabet)

lemma remainder_fiber_height [Finite Alphabet] [Nonempty Alphabet] {M : Type uM2}
    [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) (d : M) (lag : ℤ)
    (hvisible : ∀ (f : ℤ → Alphabet) b,
      EndAt C.d C.K C.tail f (lag+C.offset) (C.small f (lag+C.offset)) b →
      C.Visible 0 b (lag+C.offset)) :
    HasHeightAtMost ({w | w∈remainder (C.complete lag) ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) 1 := by
  obtain ⟨N,hN⟩ := C.remainder_middle lag hvisible
  have hreg : Language.IsRegular
      ({w | w∈remainder (C.complete lag) ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) :=
    (C.remainder_regular lag).inf (FiniteRecognition.regular_recognized T {d})
  exact PeriodicTemplates.regular_middle_height _ hreg
    (N+C.tail.toNat) N C.tail.toNat C.d (fun w hw => hN w hw.1)

end CanonicalEpisodes.Parameters

namespace SourceSchedule

open SplitMetadata EpisodeAlgebra

theorem episode_linear_graphs {Alphabet : Type uAlphabet4} {M : Type uM3} {V : Type uV2} {K : Type uK2}
    [Finite Alphabet] [Nonempty Alphabet] [Monoid M] [Fintype M]
    [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V]
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V)) :
    ∃ E : Language Alphabet, PrefixCode E ∧
      (∀ d : M, HasHeightAtMost ({w | w∈remainder E ∧ T (FreeMonoid.ofList w)=d} : Language Alphabet) 1) ∧
      ∀ x y : V, HasHeightAtMost (graph E (fun w => ρ (T (FreeMonoid.ofList w))) x y) 3 := by
  classical
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  obtain ⟨g,hg,hs₁⟩ := exists_shift_table (A := M) (K := K) (S := V)
  let β : M → M → (Fin g → M) → V := fun a c => (hs₁ (ClockAffine.productTable ρ a c)).choose
  have hβ : ∀ a c, ShiftTableProperty g (ClockAffine.productTable ρ a c) (β a c) :=
    fun a c => (hs₁ (ClockAffine.productTable ρ a c)).choose_spec
  obtain ⟨g',hg',hs₂⟩ := exists_shift_table (A := M) (K := K) (S := V × K)
  let γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K :=
    fun ψ => (hs₂ (ObservedInner.table ψ)).choose
  have hγ : ∀ ψ, ShiftTableProperty g' (ObservedInner.table ψ) (γ ψ) :=
    fun ψ => (hs₂ (ObservedInner.table ψ)).choose_spec
  let κ := Fintype.card (Kind M (V × K) K g')
  obtain ⟨μ,hμpos,hμ⟩ := exists_copies (M := M) (S := V) g κ (by omega)
  let P := Roster M (V × K) K g' μ
  let B := SlotResidues.slotModulus P
  have hB : 0<B := SlotResidues.slotModulus_pos P
  have hμ' : 20*(10000000*Real.log (2*Fintype.card (Tag M V g B))+4*(g+1))+10<μ := by
    simpa only [B,SlotResidues.slotModulus,P,Fintype.card_prod,Fintype.card_fin,κ] using hμ
  let : Nonempty (Tag M V g B) := ⟨Sum.inr ⟨0,⟨0,hB⟩,1,0,0⟩⟩
  obtain ⟨clock⟩ := RobustClock.exists_clock (Tag M V g B) P
  have honto : Function.Surjective (fun i : P => i.1.j) := by
    intro j
    exact ⟨(⟨j,0,0,fun _ => 1,fun _ => 0⟩,⟨0,hμpos⟩),rfl⟩
  let reference : P := (⟨⟨0,by omega⟩,0,0,fun _ => 1,fun _ => 0⟩,⟨0,hμpos⟩)
  obtain ⟨S⟩ := exists_early (Alphabet := Alphabet) clock B (Fintype.card M) hB
    (fun i : P => i.1.j) honto (SlotResidues.reserved P)
  obtain ⟨L⟩ := S.exists_full_late hB g
  let A := S.parameters g L hB
  let j : Fin g := ⟨0,by omega⟩
  have hr : (S.cuts g).main j∈(S.cuts g).offsets := by
    simpa only [OuterStream.Cuts.base,Nat.cast_zero,zero_mul,add_zero] using
      (S.cuts g).offset_mem (.inl j) 0 S.R_pos
  have hG := S.outer_graph_height L hB T ρ β γ
    (SlotResidues.reserved_distinct P) hμ' hβ hγ reference ((S.cuts g).main j) hr
  have hlin := AffineRecovery.recovery_height (L.endRule.prefix_code L.lag) le_rfl
    (fun w => (ρ (T w)).toAddMonoidHom) (OuterStream.wordShift A clock T ρ β L.lag) 3
    (fun x y => by
      rw [←OuterStream.wordUpdate_affine A clock T ρ β L.lag]
      exact hG x y)
  refine ⟨L.endRule.complete L.lag,L.endRule.prefix_code L.lag,?_,hlin⟩
  intro d
  exact L.endRule.remainder_fiber_height T d L.lag
    (fun f b he => (S.episode_visible g L hB he).base)

end SourceSchedule

end GeneralizedStarHeight

end OAI
