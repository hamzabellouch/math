import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalSupported

namespace OAI

/-! A local Pauli expansion multiplies each source-region occupancy by a fixed constant. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [Fintype ι] in
theorem qmaLocalPauli_filter_card (S : α → Finset ι) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun w : QMALocalPauliTerm S => p w.1)).card =
      ∑ a : {a : α // p a}, 4^(S a.val).card := by
  rw [←Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun a => {i // i ∈ S a} → Fin 4) p)]
  simp only [Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]

omit [Fintype ι] in
theorem qmaLocalEvenPauli_filter_card (S : α → Finset ι) {d : ℕ}
    (hS : ∀ a, (S a).card ≤ d) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun w : QMALocalEvenPauliTerm S => p w.val.1)).card ≤
      4^d*(Finset.univ.filter p).card := by
  have hinj : (Finset.univ.filter (fun w : QMALocalEvenPauliTerm S => p w.val.1)).card ≤
      (Finset.univ.filter (fun w : QMALocalPauliTerm S => p w.1)).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2⟩
    · intro w _ v _ h
      exact Subtype.ext h
  calc
    _ ≤ _ := hinj
    _ = ∑ a : {a : α // p a}, 4^(S a.val).card := qmaLocalPauli_filter_card S p
    _ ≤ ∑ _a : {a : α // p a}, 4^d := Finset.sum_le_sum (fun a _ =>
      pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 4) (hS a.val))
    _ = 4^d*(Finset.univ.filter p).card := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_subtype]
      exact Nat.mul_comm _ _

end ContinuumCoulomb

end

end OAI
