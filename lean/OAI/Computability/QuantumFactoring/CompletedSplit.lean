import Mathlib
import OAI.Computability.QuantumFactoring.CompletedOrderSlots
import OAI.Computability.QuantumFactoring.TransitionWords
import OAI.Computability.QuantumFactoring.ProvidedSplits

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

namespace OrderSlots

lemma unitOrder_eq {n : ℕ} (a m : Basis n) (u : (ZMod (bitsValue m).toNat)ˣ)
    (hlt : (bitsValue a).toNat < (bitsValue m).toNat)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat)) :
    unitOrder a m=orderOf u := by
  classical
  have hu : IsUnit ((bitsValue a).toNat : ZMod (bitsValue m).toNat) := ha.symm ▸ u.isUnit
  have hva : Usable a m := ⟨hlt,hu⟩
  rw [unitOrder,dite_eq_left hva]
  congr 1
  apply Units.ext
  exact hu.unit_spec.trans ha

lemma passed_value {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) (r : Result n)
    (hp : passed a m r) : (bitsValue (output a m r)).toNat=unitOrder a m := by
  rw [passed_output a m r hp,canonical,natBasis_value,Nat.mod_eq_of_lt]
  exact (unitOrder_lt a m hm).trans_le (TransitionWords.pow_width_le n (n^5))

lemma passed_order {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (u : (ZMod (bitsValue m).toNat)ˣ)
    (hlt : (bitsValue a).toNat < (bitsValue m).toNat)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (r : Result n) (hp : passed a m r) : (bitsValue (output a m r)).toNat=orderOf u := by
  rw [passed_value a m hm r hp,unitOrder_eq a m u hlt ha]

end OrderSlots

namespace CompletedSplit

abbrev Raw {n : ℕ} (m : Basis n) :=
  ListSlots.Result n (bitsValue m).toNat × (Fin (n^5)→OrderSlots.Result n)

noncomputable instance rawFintype {n : ℕ} (m : Basis n) : Fintype (Raw m) := inferInstance

def bases {n : ℕ} (m : Basis n) (r : ListSlots.Result n (bitsValue m).toNat) : Fin (n^5)→Basis n :=
  TransitionWords.read (ListSlots.output (bitsValue m).isLt r)

/-- Actual next fresh registers depend only on the completed list output,
including its rare guessing branch. Previous outcomes remain in the record. -/
noncomputable def fresh {n : ℕ} (m : Basis n) : Raw m→ℂ :=
  RecordedHistory.appendState (ListSlots.fresh n (bitsValue m).toNat)
    (fun l => productState (fun i => OrderSlots.fresh n (bases m l i) m))

noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) (r : Raw m) : Prop :=
  ListSlots.passed hm (bitsValue m).isLt p₀ r.1 ∧
    ∀ i,OrderSlots.passed (bases m r.1 i) m (r.2 i)

noncomputable def pairs {n : ℕ} (m : Basis n) (r : Raw m) : List (ℕ×ℕ) :=
  List.ofFn (fun i : Fin (n^5) => ((bitsValue (bases m r.1 i)).toNat,
    (bitsValue (OrderSlots.output (bases m r.1 i) m (r.2 i))).toNat))

noncomputable def divisor {n : ℕ} (m : Basis n) (r : Raw m) : ℕ :=
  suppliedDivisor (bitsValue m).toNat n (pairs m r)

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 := by
  apply RecordedHistory.append_normalized
  · exact ListSlots.fresh_normalized _ _
  · intro l
    exact productState_normalized _ (fun _ => OrderSlots.fresh_normalized _ _ _)

/-- One list transition followed by the K order/dummy transitions has exactly
z^(K+1) retained mass, unconditioned on the successful factor-data computation. -/
theorem passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r => ListSlots.passed (by omega) (bitsValue m).isLt p₀ r.1 ∧
    (fun l (rr : Fin (n^5)→OrderSlots.Result n) => ∀ i,OrderSlots.passed (bases m l i) m (rr i)) r.1 r.2)
    (RecordedHistory.appendState _ _) = _
  rw [RecordedHistory.append_constant_mass _ _ _ _ ((Completion.target n:ℝ)^(n^5))
    (fun l _ => OrderSlots.all_passed_mass hn m hm (bases m l))]
  rw [ListSlots.passed_mass hn hm (bitsValue m).isLt hodd p₀ p₁ hne]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

lemma passed_pair {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw m) (hp : passed m (by omega) p₀ r) :
    ∃ u : (ZMod (bitsValue m).toNat)ˣ,
      FavorableUnit (by omega : (bitsValue m).toNat≠0) (bitsValue m).isLt p₀ u ∧
        ((u : ZMod (bitsValue m).toNat).val,orderOf u)∈pairs m r := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  obtain ⟨i,u,ha,hf⟩ := ListSlots.passed_good hn (by omega) (bitsValue m).isLt hodd p₀ p₁ hne r.1 hp.1
  have haz : ((bitsValue (bases m r.1 i)).toNat : ZMod (bitsValue m).toNat)=u := by
    rw [show (bitsValue (bases m r.1 i)).toNat=(u : ZMod (bitsValue m).toNat).val from ha]
    exact ZMod.natCast_zmod_val _
  have ho := OrderSlots.passed_order (bases m r.1 i) m hm u (by change (bitsValue (TransitionWords.read (ListSlots.output (bitsValue m).isLt r.1) i)).toNat < _; rw [ha]; exact (u : ZMod (bitsValue m).toNat).val_lt) haz (r.2 i) (hp.2 i)
  refine ⟨u,hf,?_⟩
  exact List.mem_ofFn.mpr ⟨i,Prod.ext ha ho⟩

/-- The output is the actual guarded even/root/order divisor scan, not a chosen
mathematical divisor. Both ordinary and guessed good list outputs are covered. -/
theorem passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hc : ¬(bitsValue m).toNat.Prime) (hodd : Odd (bitsValue m).toNat)
    (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw m) (hp : passed m (by omega) p₀ r) :
    FactorController.ProperDivisor (bitsValue m).toNat (divisor m r) := by
  obtain ⟨u,hf,hu⟩ := passed_pair hn m hm hodd p₀ p₁ hne r hp
  exact suppliedDivisor_good hm (bitsValue m).isLt hc (pairs m r) (fun _ _ => ⟨p₀,u,hf,hu⟩)

end CompletedSplit
end ExactQuantumFactoring


end

end OAI
