import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingClassification

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset ReciprocalBands
open scoped Classical
noncomputable section

abbrev SlotClass (d : ℕ) := (Bool×Fin (d+1))⊕(Fin (d+1)×Fin (d+1))
lemma slotClass_card (d : ℕ) : Fintype.card (SlotClass d)=2*(d+1)+(d+1)^2 := by
  simp only [SlotClass,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,pow_two]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def ValidSlotClass (d : ℕ) (gap : ℝ)
    (D : Finset (ProjectivePair (K:=K) (V:=V))) : SlotClass d→Prop
  | .inl (integer,r) => ∃ u : ℝ,
      Real.log (Nat.card K:ℝ)≤u ∧ u≤(d:ℝ)*Real.log (Nat.card K:ℝ) ∧
      ((D.image Prod.fst).card:ℝ)≤1024*Real.exp (((d:ℝ)+1)*Real.log (Nat.card K:ℝ)-u) ∧
      ((D.image Prod.snd).card:ℝ)≤1024*Real.exp u ∧
      1≤r.val ∧ (if integer then IntegerBand r.val (Real.log (Nat.card K:ℝ)) gap u
        else 2≤r.val ∧ OpenBand r.val (Real.log (Nat.card K:ℝ)) gap u)
  | .inr (r,r') =>
      1≤r.val ∧ 1≤r'.val ∧ d+1<r.val+r'.val ∧
      ((D.image Prod.fst).card:ℝ)≤32*(Nat.card K:ℝ)^r.val ∧
      ((D.image Prod.snd).card:ℝ)≤32*(Nat.card K:ℝ)^r'.val ∧
      (∀ b,((D.filter (fun f=>f.1=b)).card:ℝ)≤2*(Nat.card K:ℝ)^(d-r.val)) ∧
      (∀ a,((D.filter (fun f=>f.2=a)).card:ℝ)≤2*(Nat.card K:ℝ)^(d-r'.val))

theorem exists_valid_slot_class {n : ℕ} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (h : (twoDomain W W' m m').Nonempty) :
    ∃ c : SlotClass (n+2),ValidSlotClass (n+2) gap (twoDomain W W' m m') c := by
  obtain hlow|⟨hm,hm',hr,hr',hs,hs',hsum⟩ := twoDomain_low_or_high hdim W W' m m' h
  · have hd : Module.finrank K V=(n+2)+1 := by omega
    obtain ⟨hu,hu',ha,hb⟩ := twoDomain_reciprocal_caps (by omega : 1≤n+2) hd _ h hlow
    have hq : (1:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)
    obtain ⟨r,hr,hr',hband⟩ := ReciprocalBands.cover (Real.log_pos hq) hgap hu hu'
    rcases hband with hi|ho
    · refine ⟨.inl (true,⟨r,by omega⟩),_,hu,hu',ha,hb,hr,?_⟩
      exact hi
    · refine ⟨.inl (false,⟨r,by omega⟩),_,hu,hu',ha,hb,hr,?_⟩
      exact ho
  · have hd : Module.finrank K V=(n+2)+1 := by omega
    obtain ⟨ha,hb,ha',hb'⟩ := twoPopular_caps hd W W' m m' hm hm'
    exact ⟨.inr (⟨m.1.val,by omega⟩,⟨m'.1.val,by omega⟩),hr,hs,by omega,ha,hb,ha',hb'⟩

theorem cheapBoth_valid_slot_class {n N : ℕ} {Γ : Type*}
    (hdim : Module.finrank K V=n+3) {gap : ℝ} (hgap : 0≤gap)
    (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N)
    (h : (cheapBoth z i).Nonempty) :
    ∃ c : SlotClass (n+2),ValidSlotClass (n+2) gap (cheapBoth z i) c := by
  unfold cheapBoth cheapTuple at h ⊢
  exact exists_valid_slot_class hdim hgap _ _ _ _ h

def messageClass {n N : ℕ} {Γ : Type*} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap) (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N) :
    SlotClass (n+2) :=
  if h : (cheapBoth z i).Nonempty then
    (cheapBoth_valid_slot_class hdim hgap z i h).choose
  else .inl (false,0)

lemma messageClass_valid {n N : ℕ} {Γ : Type*} (hdim : Module.finrank K V=n+3)
    {gap : ℝ} (hgap : 0≤gap) (z : TwoMessage (K:=K) (V:=V) Γ N) (i : Fin N)
    (h : (cheapBoth z i).Nonempty) :
    ValidSlotClass (n+2) gap (cheapBoth z i) (messageClass hdim hgap z i) := by
  rw [messageClass,dite_eq_left h]
  exact (cheapBoth_valid_slot_class hdim hgap z i h).choose_spec

end
end SharpLogRamsey.Marking

end

end OAI
