import Mathlib
import OAI.Computability.QuantumFactoring.TransitionEqualization
import OAI.Computability.QuantumFactoring.ProductStates

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

namespace Completion

/-- Dummy slots retain their internal preparation too. Only the constant output
is visible to the controller; no branch-local normalization is performed. -/
lemma dummy_passed_mass {α : Type*} [Fintype α] (ψ : α→ℂ) (n d : ℕ)
    (hn : 128 ≤ n) (hψ : ∑ x,Complex.normSq (ψ x)=1) (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (fun _ => True) y₀ 1 (target n))
      (fresh ψ (transitionWidth n) (2*n) d)=(target n:ℝ) := by
  apply passed_mass ψ _ y₀ 1 (target n) hψ
  · simpa only [outcomeMass,ite_true,Rat.cast_one] using hψ
  · exact DyadicAt.integer d 1
  · exact target_at n
  · unfold coinBits; omega
  · norm_num
  · norm_num
  · omega
  · exact target_pos (by omega)
  · apply target_le_ordinary (by omega : 1 ≤ n)
    have hp : (0:ℚ) ≤ 1/(2:ℚ)^(2*n) := by positivity
    linarith

end Completion

namespace OrderSlots

abbrev sampleExponent (n : ℕ) := 16*n-2
lemma sampleExponent_spec {n : ℕ} (hn : 128 ≤ n) :
    2^(sampleExponent n+2)=(2^n)^16 := by
  rw [←pow_mul]
  congr 1
  unfold sampleExponent
  omega

abbrev Result (n : ℕ) := Completion.Raw (Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n)
  (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

noncomputable instance resultFintype (n : ℕ) : Fintype (Result n) := inferInstance

noncomputable def fresh (n : ℕ) (a m : Basis n) : Result n→ℂ :=
  Completion.fresh (tensorState (rawState (sampleExponent n) n a m) (n^5))
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

def Usable {n : ℕ} (a m : Basis n) : Prop :=
  (bitsValue a).toNat < (bitsValue m).toNat ∧
    IsUnit ((bitsValue a).toNat : ZMod (bitsValue m).toNat)

noncomputable def unitOrder {n : ℕ} (a m : Basis n) : ℕ := by
  classical
  exact if h : Usable a m then orderOf h.2.unit else 0

noncomputable def canonical {n : ℕ} (a m : Basis n) : Basis (Completion.transitionWidth n) :=
  natBasis _ (unitOrder a m)

noncomputable def ordinary {n : ℕ} (a m : Basis n)
    (r : Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n) : Basis (Completion.transitionWidth n) := by
  classical
  exact if Usable a m then
    natBasis _ (orderResult (sampleExponent n) n a m (n^5) r) else natBasis _ 0

noncomputable def passed {n : ℕ} (a m : Basis n) : Result n→Prop := by
  classical
  exact if h : Usable a m then
    Completion.passed (fun r => orderResult (sampleExponent n) n a m (n^5) r=orderOf h.2.unit)
      (canonical a m) (Completion.orderSuccess (orderOf h.2.unit) (n^5)) (Completion.target n)
  else Completion.passed (fun _ => True) (canonical a m) 1 (Completion.target n)

noncomputable def output {n : ℕ} (a m : Basis n) : Result n→Basis (Completion.transitionWidth n) :=
  Completion.output (ordinary a m)

lemma fresh_normalized (n : ℕ) (a m : Basis n) :
    ∑ r,Complex.normSq (fresh n a m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (tensor_normalized _ _ (raw_normalized _ _ a m))

lemma unitOrder_lt {n : ℕ} (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    unitOrder a m < 2^n := by
  classical
  let : NeZero (bitsValue m).toNat := ⟨by omega⟩
  unfold unitOrder
  split_ifs with h
  · have hh := orderOf_le_card (x:=h.2.unit)
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient] at hh
    exact (hh.trans (Nat.totient_le _)).trans_lt (bitsValue m).isLt
  · positivity

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    outcomeMass (passed a m) (fresh n a m)=(Completion.target n:ℝ) := by
  classical
  unfold passed
  split_ifs with h
  · have hlt := unitOrder_lt a m hm
    simp only [unitOrder,dite_eq_left h] at hlt
    exact Completion.order_passed_mass hn (sampleExponent_spec hn) a m hm h.2.unit
      h.2.unit_spec.symm hlt (canonical a m)
  · exact Completion.dummy_passed_mass _ n _ hn
      (tensor_normalized _ _ (raw_normalized _ _ a m)) (canonical a m)

lemma passed_output {n : ℕ} (a m : Basis n) (r : Result n) (hp : passed a m r) :
    output a m r=canonical a m := by
  classical
  unfold passed at hp
  split_ifs at hp with h
  · rcases hp with hp | hp
    · simp only [output,Completion.output,ite_eq_right hp.1,ordinary,ite_eq_left h,canonical,
        unitOrder,dite_eq_left h,hp.2.1]
    · simp only [output,Completion.output,ite_eq_left hp.1,hp.2.1]
  · rcases hp with hp | hp
    · simp only [output,Completion.output,ite_eq_right hp.1,ordinary,ite_eq_right h,canonical,
        unitOrder,dite_eq_right h]
    · simp only [output,Completion.output,ite_eq_left hp.1,hp.2.1]

/-- Every supplied base has exactly z retained mass. Out-of-range entries and nonunits are dummy slots,
not an assumption that a random list consists only of units. -/
theorem all_passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (as : Fin (n^5)→Basis n) :
    outcomeMass (fun r : Fin (n^5)→Result n => ∀ i,passed (as i) m (r i))
      (productState (fun i => fresh n (as i) m))=(Completion.target n:ℝ)^(n^5) := by
  exact productState_constant_mass _ _ _ (fun _ => passed_mass hn _ _ hm)

end OrderSlots
end ExactQuantumFactoring


end

end OAI
