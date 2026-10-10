import OAI.Computability.StarHeight.ObservedActions

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uAlphabet uAlphabet2 uJ uC uAlphabet3 uM uS uK
universe uM2 uS2 uM3 uS3 uAlphabet4 uM4 uV uK2
universe uP uC2

namespace PeriodicTemplates

open WordIntervals LocalMarkers

variable {Alphabet : Type uAlphabet}

lemma segment_power {v : ℤ → Alphabet} {p : ℕ}
    (hp : Function.Periodic v (p : ℤ)) (s : ℤ) (q : ℕ) :
    segment v s (q*p) = wordPower (segment v s p) q := by
  induction q with
  | zero => simp [WordIntervals.segment]
  | succ q ih =>
    rw [Nat.succ_mul,segment_add,ih,wordPower_add,wordPower_one]
    congr 1
    simpa only [Nat.cast_mul] using PeriodicCuts.segment_shift_period hp s q p

lemma decompose_middle {w : List Alphabet} {f v : ℤ → Alphabet} {N tail p : ℕ}
    (hf : Realizes w 0 f) (hlen : N+tail ≤ w.length) (hp : 0 < p)
    (hper : Function.Periodic v (p : ℤ))
    (he : AgreesOn f v N (w.length-tail)) :
    ∃ a c b : List Alphabet, a.length = N ∧ c.length = p ∧ b.length < p+tail ∧
      ∃ q, w = a ++ wordPower c q ++ b := by
  let m := w.length-N-tail
  let q := m/p
  let r := m%p
  have hr : r<p := Nat.mod_lt _ hp
  have hm : m = q*p+r := by
    simpa only [q,r,Nat.mul_comm] using (Nat.div_add_mod m p).symm
  have hlen' : w.length = N+m+tail := by
    have : m = w.length-N-tail := rfl
    omega
  let a := segment f 0 N
  let c := segment v N p
  let b := segment v N r ++ segment f (N+m) tail
  refine ⟨a,c,b,length_segment _ _ _,length_segment _ _ _,?_,q,?_⟩
  · simpa only [b,List.length_append,length_segment] using Nat.add_lt_add_right hr tail
  · have hw : w = segment f 0 w.length := (realizes_iff_segment.mp hf).symm
    rw [hw,hlen',segment_add,segment_add]
    simp only [zero_add,Nat.cast_add]
    have he' : segment f N m = segment v N m := by
      apply segment_congr
      intro x hx hx'
      apply he x hx
      rw [hlen']
      push_cast
      omega
    rw [he',hm,segment_add,segment_power hper]
    have hs : segment v ((N : ℤ)+(q*p : ℕ)) r = segment v N r := by
      simpa only [Nat.cast_mul] using PeriodicCuts.segment_shift_period hper N q r
    rw [hs]
    simp only [a,c,b,List.append_assoc]
    rw [← hm]

noncomputable def boundedTemplates [Finite Alphabet] (A C B : ℕ) :
    Finset (Template Alphabet) :=
  (List.finite_length_le Alphabet A).toFinset ×ˢ
    ((List.finite_length_le Alphabet C).toFinset ×ˢ
      (List.finite_length_le Alphabet B).toFinset)

lemma mem_boundedTemplates [Finite Alphabet] (A C B : ℕ) (a c b : List Alphabet) :
    (a,c,b) ∈ boundedTemplates A C B ↔ a.length≤A ∧ c.length≤C ∧ b.length≤B := by
  simp only [boundedTemplates,Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

lemma finite_cover_of_middle [Finite Alphabet] (L : Language Alphabet) (short N tail d : ℕ)
    (h : ∀ w ∈ L, w.length ≤ short ∨
      ∃ (f v : ℤ → Alphabet) (p : ℕ), Realizes w 0 f ∧ N+tail≤w.length ∧
        0<p ∧ p≤d ∧ Function.Periodic v (p : ℤ) ∧
        AgreesOn f v N (w.length-tail)) :
    ∃ templates : Finset (Template Alphabet),
      ∀ w ∈ L, ∃ t ∈ templates, ∃ i, w = instanceWord t i := by
  refine ⟨boundedTemplates (max short N) d (d+tail),?_⟩
  intro w hw
  rcases h w hw with hs | ⟨f,v,p,hf,hlen,hp,hpd,hper,he⟩
  · refine ⟨(w,[],[]),(mem_boundedTemplates _ _ _ _ _ _).mpr ?_,0,?_⟩
    · exact ⟨hs.trans (le_max_left _ _),by simp,by simp⟩
    · simp [instanceWord]
  · obtain ⟨a,c,b,ha,hc,hb,q,hq⟩ := decompose_middle hf hlen hp hper he
    refine ⟨(a,c,b),(mem_boundedTemplates _ _ _ _ _ _).mpr ?_,q,hq⟩
    exact ⟨ha ▸ le_max_right _ _,hc ▸ hpd,hb.le.trans (Nat.add_le_add_right hpd tail)⟩

lemma regular_middle_height [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular)
    (short N tail d : ℕ)
    (h : ∀ w ∈ L, w.length ≤ short ∨
      ∃ (f v : ℤ → Alphabet) (p : ℕ), Realizes w 0 f ∧ N+tail≤w.length ∧
        0<p ∧ p≤d ∧ Function.Periodic v (p : ℤ) ∧
        AgreesOn f v N (w.length-tail)) : HasHeightAtMost L 1 := by
  obtain ⟨templates,hcover⟩ := finite_cover_of_middle L short N tail d h
  exact regular_cover_height L hL templates hcover

end PeriodicTemplates

namespace ExceptionalOrigins.Parameters

open LocalMarkers

variable {Alphabet : Type uAlphabet2} {J : Type uJ} {C : Type uC} (A : ExceptionalOrigins.Parameters Alphabet J C)

def InnerVisible (s b t : ℤ) (j : J) (u : Fin A.B) : Prop :=
  s ≤ t+A.offset j-A.innerRule.r ∧ t+A.offset j+A.H u+A.innerRule.r ≤ b

lemma inner_congr {f g : ℤ → Alphabet} {s b t : ℤ} {j : J} {u : Fin A.B}
    (hv : A.InnerVisible s b t j u) (he : AgreesOn f g s b) :
    A.inner f j u t = A.inner g j u t := by
  apply MarkerSearch.search_congr
  intro m hm hm'
  apply A.innerRule.locality
  intro x hx hx'
  exact he x (by have := hv.1; omega) (by have := hv.2; omega)

lemma inner_bounds {f : ℤ → Alphabet} {j : J} {u : Fin A.B} {t p : ℤ}
    (hp : A.inner f j u t = some p) : t+A.offset j ≤ p ∧ p ≤ t+A.offset j+A.H u := by
  exact ⟨(MarkerSearch.search_some.mp hp).1.2.1,(MarkerSearch.search_some.mp hp).2⟩

lemma inner_position_bounds {g : ℕ} (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    {f : ℤ → Alphabet} {u : Fin A.B} {s b t : ℤ} {j : Fin (g+1)}
    (hv : A.InnerVisible s b t j u) (hp : A.inner f j u t ≠ none) :
    s ≤ BoundarySnapshot.positions (fun i => A.inner f i u t) j ∧
      BoundarySnapshot.positions (fun i => A.inner f i u t) j ≤ b := by
  have hb := A.inner_bounds (f := f) (t := t) (j := j) (u := u)
    (BoundarySnapshot.positions_return (search := fun i => A.inner f i u t) (i := j) hp)
  have hr := A.innerRule.radius_ge
  exact ⟨by have := hv.1;omega,by have := hv.2;omega⟩

end ExceptionalOrigins.Parameters

namespace ObservedMain

open WordIntervals BoundarySnapshot SplitMetadata

variable {Alphabet : Type uAlphabet3} {M : Type uM} {S : Type uS} {K : Type uK} [Monoid M] [Field K] [AddCommGroup S] [Module K S]
    {g B : ℕ}
variable (T : FreeMonoid Alphabet →* M) (ρ : M → (S →ₗ[K] S))
    (β : M → M → (Fin g → M) → S)

structure PrefixRead (tag : MainTag M S g B) (f : ℤ → Alphabet) (s k : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop extends Prefix T ρ β tag f s search where
  bounds : ∀ i, i.val ≤ tag.j.val → s ≤ positions search i ∧ positions search i ≤ k
  ordered : ∀ i : Fin g, i < tag.j → positions search i.castSucc ≤ positions search i.succ

structure SuffixRead (tag : MainTag M S g B) (f : ℤ → Alphabet) (k b : ℤ)
    (search : Fin (g+1) → Option ℤ) : Prop extends Suffix T tag f b search where
  bounds : ∀ i, tag.j.val < i.val → k ≤ positions search i ∧ positions search i ≤ b
  ordered : ∀ i : Fin g, tag.j < i → positions search i.castSucc ≤ positions search i.succ

lemma PrefixRead.transfer {tag : MainTag M S g B} {f f' : ℤ → Alphabet} {s k : ℤ}
    {search search' : Fin (g+1) → Option ℤ}
    (hp : PrefixRead T ρ β tag f s k search) (he : LocalMarkers.AgreesOn f f' s k)
    (hs : ∀ i, i.val ≤ tag.j.val → search i = search' i) :
    PrefixRead T ρ β tag f' s k search' := by
  have hpos : ∀ i, i.val ≤ tag.j.val → positions search i = positions search' i := by
    intro i hi
    simp only [positions,hs i hi]
  have hzero : (0 : Fin (g+1)).val ≤ tag.j.val := by simp
  have hp0 := hp.bounds 0 hzero
  refine ⟨⟨?_,?_,?_,hp.certificate⟩,?_,?_⟩
  · intro i hi; rw [←hs i hi]; exact hp.present i hi
  · rw [←hpos 0 hzero,←hp.initial]
    symm
    apply product_congr T hp0.1
    intro z hz hz'
    exact he z hz (hz'.trans_le hp0.2)
  · intro i hi
    have h₁ : i.val.castSucc.val ≤ tag.j.val := Nat.le_of_lt hi
    have h₂ : i.val.succ.val ≤ tag.j.val := hi
    rw [←hpos _ h₁,←hpos _ h₂,←hp.earlier i hi]
    symm
    apply product_congr T (hp.ordered i.val hi)
    intro z hz hz'
    exact he z ((hp.bounds _ h₁).1.trans hz) (hz'.trans_le (hp.bounds _ h₂).2)
  · intro i hi; rw [←hpos i hi]; exact hp.bounds i hi
  · intro i hi
    rw [←hpos _ (Nat.le_of_lt hi),←hpos _ (show i.val+1 ≤ tag.j.val from hi)]
    exact hp.ordered i hi

omit [AddCommGroup S] in
lemma SuffixRead.transfer {tag : MainTag M S g B} {f f' : ℤ → Alphabet} {k b : ℤ}
    {search search' : Fin (g+1) → Option ℤ}
    (hq : SuffixRead T tag f k b search) (he : LocalMarkers.AgreesOn f f' k b)
    (hs : ∀ i, tag.j.val < i.val → search i = search' i) :
    SuffixRead T tag f' k b search' := by
  have hpos : ∀ i, tag.j.val < i.val → positions search i = positions search' i := by
    intro i hi
    simp only [positions,hs i hi]
  have hlast : tag.j.val < (Fin.last g).val := tag.j.isLt
  have hp0 := hq.bounds (Fin.last g) hlast
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro i hi; rw [←hs i hi]; exact hq.present i hi
  · rw [←hpos _ hlast,←hq.final]
    symm
    apply product_congr T hp0.2
    intro z hz hz'
    exact he z (hp0.1.trans hz) hz'
  · intro i hi
    have h₁ : tag.j.val < i.val.castSucc.val := hi
    have h₂ : tag.j.val < i.val.succ.val := Nat.lt_succ_of_lt hi
    rw [←hpos _ h₁,←hpos _ h₂,←hq.later i hi]
    symm
    apply product_congr T (hq.ordered i.val hi)
    intro z hz hz'
    exact he z ((hq.bounds _ h₁).1.trans hz) (hz'.trans_le (hq.bounds _ h₂).2)
  · intro i hi; rw [←hpos i hi]; exact hq.bounds i hi
  · intro i hi
    rw [←hpos _ hi,←hpos _ (Nat.lt_succ_of_lt hi)]
    exact hq.ordered i hi

end ObservedMain

namespace OuterStream

open SplitMetadata WordIntervals LocalMarkers BoundarySnapshot
open scoped Classical

structure Cuts (g B : ℕ) where
  main : Fin g → ℤ
  periodic : Fin (g+1) → Fin B → ℤ
  R : ℕ
  N : ℕ
  R_pos : 0 < R
  N_pos : 0 < N

namespace Cuts

variable {g B : ℕ} (H : Cuts g B)

abbrev Role (_H : Cuts g B) := Fin g ⊕ (Fin (g+1) × Fin B)

def base : H.Role → ℤ
  | .inl j => H.main j
  | .inr (j,u) => H.periodic j u

def count : H.Role → ℕ
  | .inl _ => H.R
  | .inr _ => H.N

noncomputable def offsets : Finset ℤ :=
  Finset.univ.biUnion fun role : H.Role => (Finset.range (H.count role)).image
    (fun a : ℕ => H.base role + (a:ℤ)*(B:ℤ))

lemma offset_mem (role : H.Role) (a : ℕ) (ha : a < H.count role) :
    H.base role+a*B ∈ H.offsets := by
  exact Finset.mem_biUnion.mpr ⟨role,Finset.mem_univ _,Finset.mem_image.mpr
    ⟨a,Finset.mem_range.mpr ha,rfl⟩⟩

def tagRole (H : Cuts g B) {M : Type uM2} {S : Type uS2} : Tag M S g B → H.Role
  | .inl m => .inl m.j
  | .inr p => .inr (p.j,p.u)

noncomputable def origins (k : ℤ) : Finset ℤ := H.offsets.image (fun h => k-h)

lemma true_origin {M : Type uM3} {S : Type uS3} (tag : Tag M S g B) {t k : ℤ}
    (hcut : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*B) :
    t ∈ H.origins k := by
  obtain ⟨a,ha,hk⟩ := hcut
  apply Finset.mem_image.mpr
  exact ⟨_,H.offset_mem _ _ ha,by omega⟩

end Cuts

variable {Alphabet : Type uAlphabet4} {M : Type uM4} {V : Type uV} {K : Type uK2} {P : Type uP} {C : Type uC2} [Monoid M] [Field K] [AddCommGroup V] [Module K V]
    [Fintype M] [Fintype V] [Fintype P] [Fintype C] {g : ℕ}

variable (A : ExceptionalOrigins.Parameters Alphabet (Fin (g+1)) C)
    (H : Cuts g A.B) (clock : RobustClock.Specification (Tag M V g A.B) P C)
    (T : FreeMonoid Alphabet →* M) (ρ : M → (V →ₗ[K] V))
    (β : M → M → (Fin g → M) → V)

noncomputable def search (f : ℤ → Alphabet) (u : Fin A.B) (t : ℤ) : Fin (g+1) → Option ℤ :=
  fun i => A.inner f i u t

noncomputable def snapshot (f : ℤ → Alphabet) (s b t : ℤ) : ClockAffine.Snapshot M g :=
  actual T f s b (search A f (A.residue (A.anchor f (b-A.endRule.tail) t-t)) t)

noncomputable def update (f : ℤ → Alphabet) (s b t : ℤ) (x : V) : V :=
  ClockAffine.update clock ρ β Tag.input Tag.output
    (A.φ (A.anchor f (b-A.endRule.tail) t-t)) (snapshot A T f s b t) x

structure PrefixMain (tag : MainTag M V g A.B) (f : ℤ → Alphabet) (s t k : ℤ) : Prop where
  visible : ∀ i, i.val ≤ tag.j.val → A.InnerVisible s k t i tag.u
  observed : ObservedMain.PrefixRead T ρ β tag f s k (search A f tag.u t)

structure PrefixPeriodic (tag : PeriodicTag M V g A.B) (f : ℤ → Alphabet)
    (s t k : ℤ) : Prop where
  visible : A.InnerVisible s k t tag.j tag.u
  absent : A.inner f tag.j tag.u t = none
  product_eq : product T f s k = tag.prefixProduct

structure Prefix (tag : Tag M V g A.B) (f : ℤ → Alphabet) (s t k : ℤ) : Prop where
  positive : s < k
  cut : ∃ a : ℕ, a < H.count (H.tagRole tag) ∧ k=t+H.base (H.tagRole tag)+a*A.B
  clock_mem : A.φ (k-t) ∈ clock.I tag
  letter_test : match tag with
    | .inl tag => PrefixMain A T ρ β tag f s t k
    | .inr tag => PrefixPeriodic A T tag f s t k

structure SuffixMain (tag : MainTag M V g A.B) (f : ℤ → Alphabet) (k b : ℤ) : Prop where
  visible : ∀ a : ℕ, a < H.R → ∀ i, tag.j.val < i.val →
    A.InnerVisible k b (k-H.main tag.j-a*A.B) i tag.u
  stable : ∀ a : ℕ, a < H.R → ∀ i, tag.j.val < i.val →
    A.inner f i tag.u (k-H.main tag.j-a*A.B) = A.inner f i tag.u (k-H.main tag.j)
  observed : ObservedMain.SuffixRead T tag f k b (search A f tag.u (k-H.main tag.j))

noncomputable def suffixAnchor (reference k b : ℤ) (f : ℤ → Alphabet) : ℤ :=
  A.anchor f (b-A.endRule.tail) (k-reference)

structure Suffix (reference : ℤ) (tag : Tag M V g A.B) (f : ℤ → Alphabet)
    (k b : ℤ) : Prop where
  ordered : k ≤ b
  guard : A.endRule.Guard (H.origins k) (k-reference) k b f
  clock_mem : A.φ (suffixAnchor A reference k b f-k) ∈ clock.J tag
  residue_eq : A.residue (suffixAnchor A reference k b f-k) = tag.residue
  letter_test : match tag with
    | .inl tag => SuffixMain A H T tag f k b
    | .inr tag => tag.output = ρ (tag.prefixProduct * product T f k b) tag.input

end OuterStream

end GeneralizedStarHeight

end OAI
