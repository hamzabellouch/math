import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoupledResolve
import OAI.Combinatorics.KMedianRecovery.Machines.MergeResources

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]

def level : Label V → ℕ
  | .inl _ => 0
  | .inr c => c.1+1

omit [DecidableEq V] in
lemma Before.level {key : ℕ} {B : Finset (Label V)} (hb : Before key B)
    (x : Label V) (hx : x∈B) : level x ≤ key := by
  cases x with
  | inl i=>exact Nat.zero_le _
  | inr c=>exact hb c hx

lemma level_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    level (shorten key i l u x)=level x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

lemma Correction.level (r : Correction V) (x : Label V) : level (r.apply x)=level x := by
  cases r with
  | identity=>rfl
  | shorten key i l u=>exact level_shorten key i l u x

lemma Correction.before (r : Correction V) {key : ℕ} {B : Finset (Label V)}
    (hb : Before key B) : Before key (B.image r.apply) := by
  intro c hc
  obtain ⟨x,hx,he⟩:=Finset.mem_image.mp hc
  have h:=hb.level x hx
  rw [←r.level x,he] at h
  exact h

lemma State.Resources.map_bound {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) : BankBound F h (3*q) (q*(2*F.card+1)) s.mapFree :=
  hs.map_bank (s.correction.before hs.bank.before)

omit [DecidableEq V] in
lemma State.Resources.advance {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) (G : List (Label V)) (T U : List (List (Label V))) :
    (advanceState s G T U).Resources F (q+1) h p :=
  ⟨hs.bank.mono (by omega) (Nat.mul_le_mul_right _ (by omega)),hs.correction,hs.oldPrice,hs.newPrice⟩

structure Output.Resources (F : Finset V) (q h p : ℕ) (o : Output V) : Prop where
  bank : BankBound F h (3*q) (q*(2*F.card+1)) o.B
  price : Height o.lam p

omit [DecidableEq V] in
lemma Output.Resources.mono {F : Finset V} {q q' h p : ℕ} {o : Output V}
    (ho : o.Resources F q h p) (hq : q ≤ q') : o.Resources F q' h p :=
  ⟨ho.bank.mono (by omega) (Nat.mul_le_mul_right _ hq),ho.price⟩

def Outcome.Resources (F : Finset V) (q h p : ℕ) : Outcome V → Prop
  | .inl o => o.Resources F (q+1) h p
  | .inr s => s.Resources F (q+1) h p

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
