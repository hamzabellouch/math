import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalListSlots
import OAI.Computability.QuantumFactoring.CompletedSplit

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

namespace FixedSplit

abbrev Raw (n : ℕ) :=
  PhysicalListSlots.Result n × (Fin (n^5)→OrderSlots.Result n)

noncomputable instance rawFintype (n : ℕ) : Fintype (Raw n) := inferInstance

def bases {n : ℕ} (r : PhysicalListSlots.Result n) : Fin (n^5)→Basis n :=
  TransitionWords.read (PhysicalListSlots.output r)

/-- Actual next fresh registers depend only on the completed list output,
including its rare guessing branch. Previous outcomes remain in the record. -/
noncomputable def fresh {n : ℕ} (m : Basis n) : Raw n→ℂ :=
  RecordedHistory.appendState (PhysicalListSlots.fresh m)
    (fun l => productState (fun i => OrderSlots.fresh n (bases l i) m))

noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) (r : Raw n) : Prop :=
  PhysicalListSlots.passed m hm p₀ r.1 ∧
    ∀ i,OrderSlots.passed (bases r.1 i) m (r.2 i)

noncomputable def pairs {n : ℕ} (m : Basis n) (r : Raw n) : List (ℕ×ℕ) :=
  List.ofFn (fun i : Fin (n^5) => ((bitsValue (bases r.1 i)).toNat,
    (bitsValue (OrderSlots.output (bases r.1 i) m (r.2 i))).toNat))

noncomputable def divisor {n : ℕ} (m : Basis n) (r : Raw n) : ℕ :=
  suppliedDivisor (bitsValue m).toNat n (pairs m r)

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 := by
  apply RecordedHistory.append_normalized
  · exact PhysicalListSlots.fresh_normalized _
  · intro l
    exact productState_normalized _ (fun _ => OrderSlots.fresh_normalized _ _ _)

/-- One list transition followed by the K order/dummy transitions has exactly
z^(K+1) retained mass, unconditioned on the successful factor-data computation. -/
theorem passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ)^(n^5+1) := by
  change outcomeMass (fun r => PhysicalListSlots.passed m (by omega) p₀ r.1 ∧
    (fun l (rr : Fin (n^5)→OrderSlots.Result n) => ∀ i,OrderSlots.passed (bases l i) m (rr i)) r.1 r.2)
    (RecordedHistory.appendState _ _) = _
  rw [RecordedHistory.append_constant_mass _ _ _ _ ((Completion.target n:ℝ)^(n^5))
    (fun l _ => OrderSlots.all_passed_mass hn m hm (bases l))]
  rw [PhysicalListSlots.passed_mass hn m hm hodd p₀ p₁ hne]
  exact (mul_comm _ _).trans (pow_succ (Completion.target n:ℝ) (n^5)).symm

lemma passed_pair {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw n) (hp : passed m (by omega) p₀ r) :
    ∃ u : (ZMod (bitsValue m).toNat)ˣ,
      FavorableUnit (by omega : (bitsValue m).toNat≠0) (bitsValue m).isLt p₀ u ∧
        ((u : ZMod (bitsValue m).toNat).val,orderOf u)∈pairs m r := by
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  obtain ⟨i,u,ha,hf⟩ := PhysicalListSlots.passed_good hn m (by omega) hodd p₀ p₁ hne r.1 hp.1
  have haz : ((bitsValue (bases r.1 i)).toNat : ZMod (bitsValue m).toNat)=u := by
    rw [show (bitsValue (bases r.1 i)).toNat=(u : ZMod (bitsValue m).toNat).val from ha]
    exact ZMod.natCast_zmod_val _
  have ho := OrderSlots.passed_order (bases r.1 i) m hm u (by change (bitsValue (TransitionWords.read (PhysicalListSlots.output r.1) i)).toNat < _; rw [ha]; exact (u : ZMod (bitsValue m).toNat).val_lt) haz (r.2 i) (hp.2 i)
  refine ⟨u,hf,?_⟩
  exact List.mem_ofFn.mpr ⟨i,Prod.ext ha ho⟩

/-- The output is the actual guarded even/root/order divisor scan, not a chosen
mathematical divisor. Both ordinary and guessed good list outputs are covered. -/
theorem passed_divisor {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hc : ¬(bitsValue m).toNat.Prime) (hodd : Odd (bitsValue m).toNat)
    (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Raw n) (hp : passed m (by omega) p₀ r) :
    FactorController.ProperDivisor (bitsValue m).toNat (divisor m r) := by
  obtain ⟨u,hf,hu⟩ := passed_pair hn m hm hodd p₀ p₁ hne r hp
  exact suppliedDivisor_good hm (bitsValue m).isLt hc (pairs m r) (fun _ _ => ⟨p₀,u,hf,hu⟩)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
