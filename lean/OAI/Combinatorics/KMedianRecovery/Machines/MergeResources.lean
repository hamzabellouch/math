import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeafOrder

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

def HeightBound (h : ℕ) : Label V → Prop
  | .inl _ => True
  | .inr c => Height c.2.2 h

lemma parent_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    parent (shorten key i l u x)=parent x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

lemma height_shorten (key : ℕ) (i : V) (l u : ℚ) (h : ℕ)
    (hl : Height l h) (hu : Height u h) (x : Label V) (hx : HeightBound h x) :
    HeightBound h (shorten key i l u x) := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs
  · exact hl
  · exact hu
  · exact hx

structure BankBound (F : Finset V) (h key size : ℕ) (B : Finset (Label V)) : Prop where
  rooted : ∀ x∈B,parent x∈F
  height : ∀ x∈B,HeightBound h x
  before : Before key B
  card : B.card ≤ size

omit [DecidableEq V] in
lemma BankBound.mono {F : Finset V} {h key size key' size' : ℕ} {B : Finset (Label V)}
    (hb : BankBound F h key size B) (hk : key ≤ key') (hs : size ≤ size') :
    BankBound F h key' size' B :=
  ⟨hb.rooted,hb.height,hb.before.mono hk,hb.card.trans hs⟩

lemma BankBound.pool {F : Finset V} {h key size : ℕ} {B : Finset (Label V)}
    (hb : BankBound F h key size B) :
    BankBound F h (key+1) (size+F.card) (PhaseMergePath.pool (F.image original) B (copy key)) := by
  refine ⟨?_,?_,pool_before F B key hb.before,?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hb.rooted x hx
    · obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hy
      exact hi
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hb.height x hx
    · obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hy
      exact RationalHeight.zero h
  · have h₁ := Finset.card_union_le B ((F.image original).image (copy key))
    have h₂ := Finset.card_image_le (f:=copy key) (s:=F.image original)
    have h₃ := Finset.card_image_le (f:=original) (s:=F)
    have hc := hb.card
    dsimp only [PhaseMergePath.pool]
    omega

lemma BankBound.insert {F : Finset V} {h key size : ℕ} {B : Finset (Label V)}
    (hb : BankBound F h key size B) (i : V) (hi : i∈F) (s : ℚ) (hs : Height s h) :
    BankBound F h (key+1) (size+1) (insert (leaf key i s) B) := by
  refine ⟨?_,?_,singleton_before key i s B hb.before,?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hi
    · exact hb.rooted x hx
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hs
    · exact hb.height x hx
  · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hb.card 1)

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

def Correction.Bounded (h : ℕ) : Correction V → Prop
  | .identity => True
  | .shorten _ _ l u => Height l h ∧ Height u h

lemma Correction.parent (r : Correction V) (x : Label V) : parent (r.apply x)=parent x := by
  cases r with
  | identity=>rfl
  | shorten key i l u=>exact parent_shorten key i l u x

lemma Correction.height {h : ℕ} (r : Correction V) (hr : r.Bounded h)
    (x : Label V) (hx : HeightBound h x) : HeightBound h (r.apply x) := by
  cases r with
  | identity=>exact hx
  | shorten key i l u=>exact height_shorten key i l u h hr.1 hr.2 x hx

structure State.Resources (F : Finset V) (q h p : ℕ) (s : State V) : Prop where
  bank : BankBound F h (3*q) (q*(2*F.card+1)) s.B
  correction : s.correction.Bounded h
  oldPrice : Height s.lam p
  newPrice : Height s.lam' p

lemma State.Resources.map_bank {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) (hb : Before (3*q) s.mapFree) :
    BankBound F h (3*q) (q*(2*F.card+1)) s.mapFree := by
  refine ⟨?_,?_,hb,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [Correction.parent]
    exact hs.bank.rooted y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact s.correction.height hs.correction y (hs.bank.height y hy)
  · exact (Finset.card_image_le).trans hs.bank.card

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
