import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyPrecision
import OAI.NumberTheory.Ostmann.Characters.ResidueDivision
import OAI.NumberTheory.Ostmann.Construction.HistoryGiantGuard

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction Characters.ResidueDivision

def nodePivot (N M : ℕ) (s v w : ℤ) (xplus xminus hplus hminus : ZMod N)
    (u : (ZMod M)ˣ) : ZMod M :=
  unitDivideResidue N M s u ((v:ZMod N)*(xminus*hminus)-(w:ZMod N)*(xplus*hplus))

theorem nodePivot_eq (N M : ℕ) (s v w : ℤ) (Xplus Xminus Hplus Hminus U p : ℕ)
    (u : (ZMod M)ˣ) (hu : (U:ZMod M)=u) (hs : s≠0) (hNM : s.natAbs*M∣N)
    (hrev : reversalNumerator v w ((Xplus*Hplus:ℕ):ℤ) ((Xminus*Hminus:ℕ):ℤ)=
      s*(U:ℤ)*(p:ℤ)) :
    nodePivot N M s v w Xplus Xminus Hplus Hminus u=(p:ZMod M) := by
  have he := unitDivideResidue_reversal N M s (U:ℤ) v w ((Xplus*Hplus:ℕ):ℤ)
    ((Xminus*Hminus:ℕ):ℤ) p u (by simpa using hu) hs hNM hrev.symm
  simpa only [nodePivot,Nat.cast_mul,Int.cast_natCast,Int.cast_mul] using he

theorem supported_nodePivot {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (R n : ℕ) (hsR : a.frequency.natAbs∣R) (u : (ZMod (R^n))ˣ)
    (hu : ((comp.map SmallSlot.value).prod:ZMod (R^n))=u) :
    nodePivot (R^(n+1)) (R^n) a.frequency left.root.frequency right.root.frequency
      a.giantPlus a.giantMinus (hp.map SmallSlot.value).prod (hm.map SmallSlot.value).prod u =
      (p:ZMod (R^n)) :=
  nodePivot_eq _ _ _ _ _ _ _ _ _ _ _ u hu (History.supported_root_frequency_ne_zero hs)
    (frequency_power_divides R a.frequency hsR n) (History.supported_reversal hs)

theorem small_coprime_frequency_power {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (b : ℕ) (hb : b.Prime) (hV : ∀ j≤l,V j<b) (n : ℕ) :
    Nat.Coprime b (FrequencyPrecision.product (h.frequencies++k.frequencies)^n) := by
  apply Nat.Coprime.pow_right
  apply Nat.coprime_list_prod_right_iff.mpr
  intro z hz
  obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hz
  have hf : s≠0 ∧ ∃j≤l,s.natAbs≤V j := by
    rcases List.mem_append.mp hs' with hs' | hs'
    · exact History.supported_frequency_bounds hs s hs'
    · exact History.supported_frequency_bounds ks s hs'
  obtain ⟨hzero,j,hjl,hbound⟩ := hf
  exact History.prime_coprime_small_frequency hb hzero (hbound.trans_lt (hV j hjl))

def compensationUnit {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (comp : List SmallSlot) (hprime : ∀ q∈comp,q.value.Prime)
    (hV : ∀ q∈comp,∀j≤l,V j<q.value) (n : ℕ) :
    (ZMod (FrequencyPrecision.product (h.frequencies++k.frequencies)^n))ˣ :=
  ZMod.unitOfCoprime (comp.map SmallSlot.value).prod (by
    apply Nat.coprime_list_prod_left_iff.mpr
    intro b hb
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
    exact small_coprime_frequency_power h k hs ks q.value (hprime q hq) (hV q hq) n)

@[simp] theorem coe_compensationUnit {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (comp : List SmallSlot) (hprime : ∀ q∈comp,q.value.Prime)
    (hV : ∀ q∈comp,∀j≤l,V j<q.value) (n : ℕ) :
    (compensationUnit h k hs ks comp hprime hV n :
      ZMod (FrequencyPrecision.product (h.frequencies++k.frequencies)^n)) =
      ((comp.map SmallSlot.value).prod:ℕ) := ZMod.coe_unitOfCoprime _ _

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
