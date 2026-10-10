import OAI.Computability.StarHeight.OriginSplicing

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uM uV uAlphabet2 uM2 uV2 uK uP
universe uC uAlphabet3 uM3 uV3 uK2 uP2 uC2 uAlphabet4
universe uAlphabet5 uM4 uV4 uK3 uP3 uC3 uAlphabet6 uM5
universe uV5 uK4 uP4 uC4

namespace StreamSplice.Frame

open WordIntervals LocalMarkers
variable {Alphabet : Type uAlphabet} {M : Type uM} [Monoid M] {f f' : ℤ → Alphabet} {N : ℤ} {x y : List Alphabet}
    (H : Frame f f' N x y)

include H

lemma piece_left_any {s t : ℤ} (ht : t≤N) : piece f s t=piece f' s t := by
  unfold piece
  apply List.ofFn_inj.mpr
  funext i
  exact (H.left _ (by have hi := i.isLt;omega)).symm

lemma product_left_any (T : FreeMonoid Alphabet →* M) {s t : ℤ} (ht : t≤N) :
    WordIntervals.product T f s t=WordIntervals.product T f' s t :=
  congrArg (fun w => T (FreeMonoid.ofList w)) (H.piece_left_any ht)

lemma observedSuffix {V : Type uV}
    {g B : ℕ} (T : FreeMonoid Alphabet →* M) {tag : SplitMetadata.MainTag M V g B}
    {k b : ℤ} {search search' : Fin (g+1) → Option ℤ}
    (hT : T (FreeMonoid.ofList x)=T (FreeMonoid.ofList y)) (hb : N+x.length≤b)
    (hs : search=search') (hsearch : ∀ i q, search i=some q → q≤N)
    (hq : ObservedMain.SuffixRead T tag f k b search) :
    ObservedMain.SuffixRead T tag f' k (b+((y.length:ℤ)-x.length)) search' := by
  subst search'
  have hpos : ∀ i, tag.j.val < i.val → BoundarySnapshot.positions search i≤N := by
    intro i hi
    exact hsearch i _ (BoundarySnapshot.positions_return (hq.present i hi))
  have hg : tag.j.val < (Fin.last g).val := tag.j.isLt
  have hbN : N≤b+((y.length:ℤ)-x.length) := by omega
  refine ⟨⟨hq.present,?_,?_⟩,?_,hq.ordered⟩
  · rw [H.product T hT (hpos _ hg) hb]
    exact hq.final
  · intro i hi
    rw [←H.product_left_any T (hpos _ (by exact Nat.lt_succ_of_lt hi))]
    exact hq.later i hi
  · intro i hi
    exact ⟨(hq.bounds i hi).1,(hpos i hi).trans hbN⟩

end StreamSplice.Frame

namespace OuterStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet2} {M : Type uM2} {V : Type uV2} {K : Type uK} {P : Type uP} {C : Type uC} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def originBound : ℕ := H.offsets.sup (fun h => h.natAbs)

omit [Fintype C] in
lemma origin_bound {t : ℤ} (ht : t∈H.origins 0) : |t|≤(originBound A H:ℤ) := by
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp ht
  have hle := Finset.le_sup (f := fun h : ℤ => h.natAbs) hh
  simpa only [zero_sub,abs_neg,Int.natCast_natAbs] using
    (show (h.natAbs:ℤ)≤(originBound A H:ℤ) by exact_mod_cast hle)

omit [Fintype C] in
lemma main_origin (j : Fin g) {a : ℕ} (ha : a<H.R) :
    -H.main j-a*A.B∈H.origins 0 := by
  apply Finset.mem_image.mpr
  refine ⟨H.main j+a*A.B,?_,by omega⟩
  exact H.offset_mem (.inl j) a ha

lemma suffix_splice {N : ℕ} (HN : A.Inspection (originBound A H) N)
    {f f' : ℤ → Alphabet} {x y : List Alphabet} {b reference : ℤ}
    {tag : Tag M V g A.B} (HF : Frame f f' N x y)
    (hb : (N:ℤ)+x.length≤b-A.endRule.tail) (hsum : SummaryEq A T x y)
    (hq : Suffix A H clock T ρ reference tag f 0 b) :
    Suffix A H clock T ρ reference tag f' 0 (b+((y.length:ℤ)-x.length)) := by
  have hbn : (N:ℤ)+x.length≤b := by have := A.endRule.tail_pos;omega
  have hvis := fun t ht => (HN.full t (origin_bound A H ht) (0:ℤ)).base
  have href : -reference∈H.origins 0 := by simpa only [zero_sub] using hq.guard.1
  have hphase := HF.anchor_relative_phase A (t := -reference) (b := b) (r := 0)
    (hvis _ href) hsum.residue_dvd hsum.clock_eq
  simp only [sub_zero] at hphase
  have hbN : (N:ℤ)≤b+((y.length:ℤ)-x.length) := by omega
  refine ⟨by omega,HF.guard A.endRule (fun t ht => ⟨hvis t ht,HN.strict t (origin_bound A H ht)⟩)
    hb hsum.period_dvd hsum.matcher_eq hq.guard,?_,?_,?_⟩
  · change A.φ (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) (0-reference)-0)∈clock.J tag
    simpa only [suffixAnchor,zero_sub,sub_zero,hphase.2] using hq.clock_mem
  · change A.residue (A.anchor f' (b+((y.length:ℤ)-x.length)-A.endRule.tail) (0-reference)-0)=tag.residue
    simpa only [suffixAnchor,zero_sub,sub_zero,hphase.1] using hq.residue_eq
  · cases tag with
    | inr tag =>
      change tag.output=ρ (tag.prefixProduct*product T f' 0 (b+((y.length:ℤ)-x.length))) tag.input
      rw [HF.product T hsum.monoid_eq (by omega) hbn]
      exact hq.letter_test
    | inl tag =>
      have present : SuffixMain A H T tag f 0 b := hq.letter_test
      have hv (a : ℕ) (ha : a<H.R) (i : Fin (g+1)) :
          A.InnerVisible (-(N:ℤ)) N (-H.main tag.j-a*A.B) i tag.u :=
        HN.inner _ (origin_bound A H (main_origin A H tag.j ha)) i tag.u
      have hR : 0<H.R := H.R_pos
      have hzero : -H.main tag.j-0*A.B=-H.main tag.j := by ring
      have hbase (i : Fin (g+1)) : A.InnerVisible (-(N:ℤ)) N (-H.main tag.j) i tag.u := by
        simpa only [Nat.cast_zero,zero_mul,sub_zero] using hv 0 hR i
      have hsearch : search A f tag.u (-H.main tag.j)=search A f' tag.u (-H.main tag.j) := by
        funext i
        exact A.inner_congr (hbase i) (HF.agrees_left (le_refl _))
      refine ⟨?_,?_,?_⟩
      · intro a ha i hi
        have old := present.visible a ha i hi
        have new := hv a ha i
        exact ⟨old.1,by simpa only [zero_sub] using new.2.trans hbN⟩
      · intro a ha i hi
        have hs := A.inner_congr (hv a ha i) (HF.agrees_left (le_refl _))
        have ho := present.stable a ha i hi
        simp only [zero_sub] at ho ⊢
        exact hs.symm.trans (ho.trans (congrFun hsearch i))
      · have hh := HF.observedSuffix T hsum.monoid_eq hbn hsearch (fun i q hq => by
          have hb' := A.inner_bounds hq
          have hv' := (hbase i).2
          have hr := A.innerRule.radius_ge
          omega) (by simpa only [zero_sub] using present.observed)
        simpa only [zero_sub] using hh

end OuterStream
namespace InnerStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet3} {M : Type uM3} {V : Type uV3} {K : Type uK2} {P : Type uP2} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)

lemma hypothetical_splice {N : ℕ} {f f' : ℤ → Alphabet} {x y : List Alphabet} {s b t : ℤ}
    (HF : Frame f f' N x y) (ha : s+early (Fin.last g')≤N) (hb : (N:ℤ)+x.length≤b)
    (hend : A.endRule.Visible (-(N:ℤ)) N (t+A.endRule.offset))
    (hv : ∀ j u, A.InnerVisible (-(N:ℤ)) N t j u) (hsum : SummaryEq A T x y) :
    hypothetical A clock T ρ β early f' s (b+((y.length:ℤ)-x.length)) t=
      hypothetical A clock T ρ β early f s b t := by
  have hphase := HF.anchor_phase A (b := b) hend hsum.residue_dvd hsum.clock_eq
  let u := A.residue (A.anchor f (b-A.endRule.tail) t-t)
  have hsearch : OuterStream.search A f u t=OuterStream.search A f' u t := by
    funext j
    exact A.inner_congr (hv j u) (HF.agrees_left (le_refl _))
  have hl := HF.later T ha hb hsum.monoid_eq (OuterStream.search A f u t) (fun j q hq => by
    have hq' := A.inner_bounds hq
    have hv' := (hv j u).2
    have hr := A.innerRule.radius_ge
    omega)
  dsimp only [hypothetical]
  rw [←hphase.1,←hphase.2,←hsearch,hl]

variable [Fintype K]
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

noncomputable def inspectionBound : ℕ :=
  SourceSchedule.absoluteBound p + lag.natAbs + SourceSchedule.absoluteBound early

omit [Monoid M] in
lemma origin_bound (slot : Roster M (V × K) K g' μ) :
    |SuffixDecoder.origin p lag 0 slot|≤(inspectionBound early p lag:ℤ) := by
  have hp := abs_le.mp (SourceSchedule.abs_le_absoluteBound p slot)
  have hl := abs_le.mp (le_refl |lag|)
  have hn : (0:ℤ)≤SourceSchedule.absoluteBound early := Int.natCast_nonneg _
  rw [abs_le]
  simp only [SuffixDecoder.origin,zero_add,inspectionBound,Nat.cast_add,Int.natCast_natAbs]
  constructor <;> omega

omit [Monoid M] in
lemma boundary_bound (slot : Roster M (V × K) K g' μ) (i : Fin (g'+1)) :
    -p slot+early i≤(inspectionBound early p lag:ℤ) := by
  have hp := abs_le.mp (SourceSchedule.abs_le_absoluteBound p slot)
  have he := abs_le.mp (SourceSchedule.abs_le_absoluteBound early i)
  have hl : (0:ℤ)≤lag.natAbs := Int.natCast_nonneg _
  simp only [inspectionBound,Nat.cast_add]
  omega

lemma suffix_splice {N : ℕ} (HN : A.Inspection (inspectionBound early p lag) N)
    {f f' : ℤ → Alphabet} {x y : List Alphabet} {b : ℤ}
    {reference slot : Roster M (V × K) K g' μ} (hw₀ : 0≤A.w₀)
    (HF : Frame f f' N x y) (hb : (N:ℤ)+x.length≤b-A.endRule.tail)
    (hsum : SummaryEq A T x y) (hq : Suffix A clock T ρ β early p lag reference slot f 0 b) :
    Suffix A clock T ρ β early p lag reference slot f' 0 (b+((y.length:ℤ)-x.length)) := by
  have hbn : (N:ℤ)+x.length≤b := by have := A.endRule.tail_pos;omega
  have hD : (inspectionBound early p lag:ℤ)≤N := by exact_mod_cast HN.contains.le
  have hvis := fun i Q => HN.full _ (origin_bound early p lag i) Q
  have hbase (i : Roster M (V × K) K g' μ) := (hvis i (0:ℤ)).base
  refine ⟨HF.decoder A hw₀ (fun i => hvis i _) hvis
    (fun i => HN.strict _ (origin_bound early p lag i)) hb hsum.period_dvd hsum.matcher_eq
    hsum.residue_dvd hsum.clock_eq hq.decoder,?_,?_⟩
  · intro i hi
    have hb' := (boundary_bound early p lag slot i.val.succ).trans hD
    simpa only [zero_sub] using (HF.product_left_any T hb').symm.trans (by simpa only [zero_sub] using hq.observed.later i hi)
  · have hend : A.endRule.Visible (-(N:ℤ)) N (-p slot+lag+A.endRule.offset) := by
      simpa only [SuffixDecoder.origin,zero_add,add_zero,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hbase slot
    have hi : ∀ j u, A.InnerVisible (-(N:ℤ)) N (-p slot+lag) j u := by
      intro j u
      have hh := HN.inner _ (origin_bound early p lag slot) j u
      simpa only [SuffixDecoder.origin,zero_add,add_zero,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh
    have hh := hypothetical_splice A clock T ρ β early (s := -p slot) (b := b)
      (t := -p slot+lag) HF
      ((boundary_bound early p lag slot (Fin.last g')).trans hD) hbn
      hend hi hsum
    simpa only [zero_sub] using hh.trans (by simpa only [zero_sub] using hq.observed.hypothetical_eq)

end InnerStream
namespace StreamSplice

variable {Alphabet : Type uAlphabet4}

lemma wordTest_finite [Finite Alphabet] {R : (ℤ → Alphabet) → ℤ → Prop} (N : ℕ)
    (hR : ∀ f b, R f b → b≤N) : (wordTest R : Set (List Alphabet)).Finite := by
  apply (List.finite_length_le Alphabet N).subset
  rintro w ⟨f,_,hw⟩
  exact_mod_cast hR f _ hw

end StreamSplice

namespace OuterStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet5} {M : Type uM4} {V : Type uV4} {K : Type uK3} {P : Type uP3} {C : Type uC3} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def prefixLanguage (lag : ℤ) (x : V) : Language Alphabet :=
  ⨆ tag : {tag : Tag M V g A.B // tag.input=x},
    wordTest (fun f b => Prefix A H clock T ρ β tag.val f 0 lag b)

noncomputable def suffixLanguage (reference : ℤ) (y : V) : Language Alphabet :=
  ⨆ tag : {tag : Tag M V g A.B // tag.output=y},
    wordTest (fun f b => Suffix A H clock T ρ reference tag.val f 0 b)

lemma prefix_finite [Finite Alphabet] (lag : ℤ) (x : V) :
    (prefixLanguage A H clock T ρ β lag x : Set (List Alphabet)).Finite := by
  apply (List.finite_length_le Alphabet (lag.natAbs+originBound A H)).subset
  intro w hw
  obtain ⟨tag,f,hf,hp⟩ := Language.mem_iSup.mp hw
  obtain ⟨a,ha,hcut⟩ := hp.cut
  have hm := H.offset_mem (H.tagRole tag.val) a ha
  have hb := abs_le.mp (show |H.base (H.tagRole tag.val)+(a:ℤ)*A.B|≤(originBound A H:ℤ) by
    simpa only [originBound,Int.natCast_natAbs] using
      (show ((H.base (H.tagRole tag.val)+(a:ℤ)*A.B).natAbs:ℤ)≤(originBound A H:ℤ) from
        by exact_mod_cast Finset.le_sup (f := fun h : ℤ => h.natAbs) hm))
  have hl : lag≤(lag.natAbs:ℤ) := by simpa only [Int.natCast_natAbs] using le_abs_self lag
  have hwlen : (w.length:ℤ)≤(lag.natAbs+originBound A H:ℕ) := by
    rw [Nat.cast_add]
    omega
  exact_mod_cast hwlen

lemma prefix_height [Finite Alphabet] (lag : ℤ) (x : V) :
    HasHeightAtMost (prefixLanguage A H clock T ρ β lag x) 0 :=
  HasHeightAtMost.finite _ (prefix_finite A H clock T ρ β lag x) 0

lemma suffix_regular [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (reference : ℤ) (y : V) : (suffixLanguage A H clock T ρ reference y).IsRegular := by
  obtain ⟨N,HN⟩ := A.exists_inspection (originBound A H)
  apply FiniteRecognition.regular_iSup
  intro tag
  exact wordTest_regular A T n hn hφ N _ (fun f f' b x y HF hb hs hq =>
    suffix_splice A H clock T ρ HN HF hb hs hq)

lemma suffix_height [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (reference : ℤ) (y : V) : HasHeightAtMost (suffixLanguage A H clock T ρ reference y) 1 := by
  apply A.endRule.ending_height _ (suffix_regular A H clock T ρ n hn hφ reference y)
    (originBound A H)
  intro w hw
  obtain ⟨tag,f,hf,hq⟩ := Language.mem_iSup.mp hw
  refine ⟨f,-reference,hf,?_,?_⟩
  · exact origin_bound A H (by simpa only [zero_sub] using hq.guard.1)
  · simpa only [zero_sub] using hq.guard.2.2.2

end OuterStream

namespace InnerStream

open WordIntervals LocalMarkers StreamSplice SplitMetadata BoundarySnapshot
variable {Alphabet : Type uAlphabet6} {M : Type uM5} {V : Type uV5} {K : Type uK4} {P : Type uP4} {C : Type uC4} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype K] [Fintype P] [Fintype C] {g g' μ : ℕ}
variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V) (early : Fin (g'+1) → ℤ)
    (γ : (M → (V × K →ₗ[K] V × K)) → (Fin g' → M) → V × K)
    (p : Roster M (V × K) K g' μ → ℤ) (lag : ℤ)

noncomputable def prefixLanguage (x : V × K) : Language Alphabet :=
  ⨆ slot : {slot : Roster M (V × K) K g' μ // slot.1.input=x},
    wordTest (fun f b => Prefix T early γ p slot.val f 0 b)

noncomputable def suffixLanguage (reference : Roster M (V × K) K g' μ) (y : V × K) : Language Alphabet :=
  ⨆ slot : {slot : Roster M (V × K) K g' μ // slot.1.output=y},
    wordTest (fun f b => Suffix A clock T ρ β early p lag reference slot.val f 0 b)

lemma prefix_finite [Finite Alphabet] (x : V × K) :
    (prefixLanguage T early γ p x : Set (List Alphabet)).Finite := by
  apply (List.finite_length_le Alphabet (SourceSchedule.absoluteBound p)).subset
  intro w hw
  obtain ⟨slot,f,_,hp⟩ := Language.mem_iSup.mp hw
  have hb := (abs_le.mp (SourceSchedule.abs_le_absoluteBound p slot.val)).2
  have hwlen : (w.length:ℤ)≤SourceSchedule.absoluteBound p := by rw [hp.cut];simpa only [zero_add] using hb
  exact_mod_cast hwlen

lemma prefix_height [Finite Alphabet] (x : V × K) :
    HasHeightAtMost (prefixLanguage T early γ p x) 0 :=
  HasHeightAtMost.finite _ (prefix_finite T early γ p x) 0

lemma suffix_regular [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (hw₀ : 0≤A.w₀) (reference : Roster M (V × K) K g' μ) (y : V × K) :
    (suffixLanguage A clock T ρ β early p lag reference y).IsRegular := by
  obtain ⟨N,HN⟩ := A.exists_inspection (inspectionBound early p lag)
  apply FiniteRecognition.regular_iSup
  intro slot
  exact wordTest_regular A T n hn hφ N _ (fun f f' b x y HF hb hs hq =>
    suffix_splice A clock T ρ β early p lag HN hw₀ HF hb hs hq)

lemma suffix_height [Finite Alphabet] (n : ℕ) (hn : 0<n) (hφ : A.φ (n:ℤ)=0)
    (hw₀ : 0≤A.w₀) (reference : Roster M (V × K) K g' μ) (y : V × K) :
    HasHeightAtMost (suffixLanguage A clock T ρ β early p lag reference y) 1 := by
  apply A.endRule.ending_height _ (suffix_regular A clock T ρ β early p lag n hn hφ hw₀ reference y)
    (inspectionBound early p lag)
  intro w hw
  obtain ⟨slot,f,hf,hq⟩ := Language.mem_iSup.mp hw
  exact ⟨f,SuffixDecoder.origin p lag 0 slot.val,hf,origin_bound early p lag slot.val,
    hq.decoder.final_guard⟩

end InnerStream

end GeneralizedStarHeight

end OAI
