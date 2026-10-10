import OAI.Combinatorics.HadwigerCounterexample.ScriptGramCorrespondence

namespace OAI

/-! # Key Test Correspondence -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def pairedRead (s : Script p I) (m : Mixer p n) (z : Inputs p n I) (i j : I) :=
  ∀ a:MOne p, s i j a=evmat (orderedM m a) (v.croon i (z i)) (v.croon j (z j))

def knows (s : Script p I) (m : Mixer p n) (z : Inputs p n I) (i j : I) :=
  v.aim i=v.aim j→ v.pairedRead s m z i j∧v.pairedRead s m z j i
omit [Fintype I] [DecidableEq I] in
theorem knows_rev (v : Template p I) {s : Script p I} {m : Mixer p n} {z} {i j}
    (h : v.knows s m z i j) : v.knows s m z j i := fun ht => (h ht.symm).symm

omit [DecidableEq I] in
theorem voice_agreement (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : UnitType p n N) (z : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i))
    (hg : 2≤p.g) (j : v.Chorus) :
    listen v.choral (v.chime m x) z j = v.lyrics s j ↔
      v.verges ((v.draw z).keys v.t x) (v.verses j).1 (v.verses j).2 ∧
        v.knows s m z (v.verses j).1 (v.verses j).2 := by
  classical
  let y := (v.draw z).keys v.t x
  cases j with
  | inr k =>
    let a := k.val.1; let b := k.val.2
    have he : v.aim a≠v.aim b := by rw [k.property.1,k.property.2]; decide
    have hh e ha hb q :
        listen v.choral (v.chime m x) z (.inr k) (⟨(e,q),ha,hb⟩ :
          Crossing p (v.t a) (v.t b))=v.voices y a b e ha hb q := by
      change evmat (duel p (x.1 e) (x.2 e) q) _ _=_
      rw [voice_note,k.property.1,k.property.2]; rfl
    constructor
    · intro h
      exact ⟨fun e ha hb q => (hh e ha hb q).symm.trans (congr_fun h _),fun ht => (he ht).elim⟩
    rintro ⟨h,_⟩
    apply funext
    rintro ⟨⟨e,q⟩,ha,hb⟩
    exact (hh e ha hb q).trans (h e ha hb q)
  | inl k =>
    let a := k.val.1; let b:= k.val.2
    have he : v.aim a=v.aim b := k.property.1
    let u := listen v.choral (v.chime m x) z (.inl k)
    let d := v.lyrics s (.inl k)
    have hi1 i :
        u (Sum.inl (i,true))=d (Sum.inl (i,true)) ↔
          s a b i=evmat (orderedM m i) (v.croon a (z a)) (v.croon b (z b)) := Eq.comm
    have hi2 i :
        u (Sum.inl (i,false))=d (Sum.inl (i,false)) ↔
          s b a i=evmat (orderedM m i) (v.croon b (z b)) (v.croon a (z a)) := by
      change evmat (orderedM m i)ᵀ _ _=s b a i ↔ _
      rw [evmat_transpose]; exact Eq.comm
    have ht e ha hb q :
        u (Sum.inr q)=d (Sum.inr q) ↔ v.voices y a b e ha hb q=0 := by
      rw [voice_same _ x z m hw e a b ha hb he q]; rfl
    change u=d↔v.verges y a b ∧ v.knows s m z a b
    constructor
    · intro h
      exact ⟨fun e ha hb q => (ht e ha hb q).mp (congr_fun h _),
        fun _ => ⟨fun i => (hi1 i).mp (congr_fun h _),fun i => (hi2 i).mp (congr_fun h _)⟩⟩
    have hk : ∃ e : Comp p.g,inc e (v.t a) ∧ inc e (v.t b) := by
      by_cases hx : v.t a=v.t b
      · rw [hx]
        have h : 0<Fintype.card (TagStar (v.t b)) := by rw [card_star]; omega
        obtain ⟨⟨i,hi⟩⟩ := Fintype.card_pos_iff.mp h
        exact ⟨i,hi,hi⟩
      refine ⟨edge _ _ hx,inc_edge_fst hx,(inc_edge_iff hx).mpr (Or.inr rfl)⟩
    rintro ⟨h1,h2⟩; specialize h2 he
    apply funext
    rintro (⟨i,_|_⟩|q)
    · exact (hi2 i).mpr (h2.2 i)
    · exact (hi1 i).mpr (h2.1 i)
    obtain ⟨i,hi,hj⟩ := hk
    exact (ht i hi hj q).mpr (h1 ..)

def neigh (v : Template p I) (s : Script p I) (m : Mixer p n) (x : UnitType p n N)
    (z : Inputs p n I) := (v.draw z).reads s m ∧ ∀ i j, i≠j →
      v.verges ((v.draw z).keys v.t x) i j

omit [DecidableEq I] in
theorem neigh_voice (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : UnitType p n N) (z : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i))
    (hg : 2 ≤ p.g) :
    v.performs s m x z ↔ v.neigh s m x z := by
  classical
  let y := (v.draw z).keys v.t x
  let g i j := v.verges y i j∧ v.knows s m z i j
  have h1 :
      v.performs s m x z ↔ ∀ i j,i≠j→ g i j := by
    unfold performs; rw [funext_iff]; simp_rw [voice_agreement _ _ _ _ _ hw hg]
    change (∀ i,g (v.verses i).1 (v.verses i).2) ↔_
    constructor
    · intro h i j hh
      obtain ⟨k,h'|h'⟩ := across_duet v hh
      · specialize h k; rwa [h'] at h
      specialize h k; rw [h'] at h
      exact ⟨v.verges_rev h.1,v.knows_rev h.2⟩
    exact fun h _ => h _ _ (v.choral.diff _)
  rw [h1]; unfold g neigh
  constructor
  · intro h; exact ⟨fun i j e he => ((h i j e).2 he).1,fun i j e => (h i j e).1⟩
  rintro ⟨h,h'⟩ i j he
  exact ⟨h' i j he,fun e => ⟨h i j he e,h j i (Ne.symm he) (Eq.symm e)⟩⟩

theorem performs_own (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : UnitType p n N) (z : Inputs p n I) (hw : ∀ i,frameLaw m (onSide x i))
    (hg : 2 ≤ p.g) (hj : 1 ≤ p.j)
    (q : I→F) (hq : ∀ i,dialed p (v.t i) (v.f i) (z i)=q i) :
    v.performs s m x z ↔ (v.draw z).reads s m ∧
      ownPart (p:=p) v.t q ((v.draw z).keys v.t x) := by
  rw [neigh_voice _ _ _ _ _ hw hg,ownPart_def]
  unfold neigh
  apply and_congr Iff.rfl
  have ht (i : I) := v.voices_diag m x z hw hj i
  simp_rw [hq] at ht
  let y := (v.draw z).keys v.t x
  constructor
  · intro h; exact ⟨ht,fun i j e hi hj hh => h i j hh e hi hj true⟩
  rintro ⟨_,h⟩ i j hh e hi hj (b|b)
  · unfold voices; rw [dotProduct_comm]; exact h j i e hj hi (Ne.symm hh)
  exact h i j e hi hj hh

end Template
end HadwigerCounterexample

end

end OAI
