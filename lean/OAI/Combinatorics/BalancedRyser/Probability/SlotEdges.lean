import Mathlib.Data.Sym.Sym2
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability

namespace OAI

noncomputable section

namespace Balanced.Slots

universe u v w
variable {ι : Type u} (V : ι → Type v)

def edgeEvent (e : Sym2 (Sigma V)) : Set (Assignment V) :=
  {ω | ∀ z ∈ e, ω z.1 = z.2}

def edgeSupport (e : Sym2 (Sigma V)) : Finset ι := by
  classical
  exact e.toFinset.image Sigma.fst

def edgeSlotsDistinct (e : Sym2 (Sigma V)) : Prop :=
  Sym2.lift ⟨fun a b : Sigma V => a.1 ≠ b.1, fun _ _ => propext ne_comm⟩ e

def edgeMass [∀ i, Fintype (V i)] (e : Sym2 (Sigma V)) : ℝ :=
  Sym2.lift ⟨fun a b : Sigma V =>
    (Fintype.card (V a.1) : ℝ)⁻¹ * (Fintype.card (V b.1) : ℝ)⁻¹,
    fun _ _ => mul_comm _ _⟩ e

def supportNeighbors {κ : Type w} [Fintype κ]
    (support : κ → Finset ι) (e : κ) : Finset κ := by
  classical
  exact Finset.univ.filter (fun f => f ≠ e ∧ ¬ Disjoint (support e) (support f))

def touching {κ : Type w} [Fintype κ]
    (support : κ → Finset ι) (J : Finset ι) : Finset κ := by
  classical
  exact Finset.univ.filter (fun e => ¬ Disjoint J (support e))

end Balanced.Slots

end

end OAI
