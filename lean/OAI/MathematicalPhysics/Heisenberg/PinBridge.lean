import OAI.MathematicalPhysics.Heisenberg.CutColors

namespace OAI

noncomputable section
open scoped BigOperators Classical
attribute [-instance] instDecidableEqFin
@[reducible] local instance pinDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Cycle
open Heisenberg.Return
variable {V : Type*} [Fintype V]
lemma missing_iff_not_hit (π : Equiv.Perm V) (P : Set V) (v : V) :
    v∈MissingSet π P ↔ ¬HasHit π P v := by
  simp only [MissingSet,Set.mem_ofPred_eq,hasHit_iff_cycle]
  simp only [not_exists,not_and,ne_eq,classOf_eq_iff]
end Heisenberg.Cycle

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return Heisenberg.Serial Heisenberg.SparseWitness
variable {V : Type} [Fintype V]

omit [Fintype V] in
lemma coinWiring_eq_history {m : ℕ} (s : Equiv.Perm (Fin m)) (a b : Fin m → V) :
    LayeredExchange.coinWiring s a b=layerHistory s (fun i=>Equiv.swap (a i) (b i)) := by
  funext c
  apply congrArg (LayeredExchange.wiring s)
  funext i
  cases c i <;> rfl

omit [Fintype V] in
lemma layerMass_pinDensity {m : ℕ} (s : Equiv.Perm (Fin m)) (a b : Fin m → V)
    (P : Set (Fin m×V)) (p : Fin m → ℝ) (c : Fin m → Bool) :
    layerMass s a b P p c=pinDensity (LayeredExchange.layerWeight p)
      (LayeredExchange.coinWiring s a b) P c := by
  simp only [layerMass,layerPartition,layerWeight,pinDensity,pinPartition,LayeredExchange.layerWeight,Bernoulli.weight,layerHistory,LayeredExchange.coinWiring,swap_classical]

def cutAdmissible {X : Type} [PseudoMetricSpace X] {m : ℕ} (loc : V → X)
    (α L : ℝ) (U : Finset (Fin m×V)) : Prop :=
  ∃ t J, U=J.image (fun j=>(t,j)) ∧ localGrowth loc α L J

omit [Fintype V] in
lemma growth_subtype {X : Type} [PseudoMetricSpace X] (loc : V → X)
    (α L : ℝ) (J : Finset V) (hg : localGrowth loc α L J) :
    ∀ z r,0 ≤ r → ((Finset.univ.filter (fun j : J=>dist (loc j.val) z ≤ r)).card:ℝ) ≤ L*(1+r)^α := by
  intro z r hr
  have he : (Finset.univ.filter (fun j : J=>dist (loc j.val) z ≤ r)).card=
      (J.filter (fun j=>dist (loc j) z ≤ r)).card := by
    rw [←Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext j
    simp [and_comm]
  rw [he]
  exact hg z r hr

lemma cut_moment_of_induction {X : Type} [PseudoMetricSpace X] {m : ℕ}
    (loc : V → X) (α L : ℝ) (s : Equiv.Perm (Fin m)) (a b : Fin m → V)
    (P : Set (Fin m×V)) (rates : Fin m → ℝ) (p : ℝ)
    (hIH : ∀ U : Finset (Fin m×V),cutAdmissible loc α L U → Disjoint P (U:Set (Fin m×V)) →
      (∑ c,if ∀ j∈U,¬HasHit (LayeredExchange.coinWiring s a b c) P j then
        pinDensity (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring s a b) P c else 0) ≤ p^U.card) :
    ∀ t U,localGrowth loc α L U → (∀ j∈U,(t,j)∉P) →
      (∑ c,if ∀ j∈U,(t,j)∈MissingSet (layerHistory s (fun i=>Equiv.swap (a i) (b i)) c) P then
        layerMass s a b P rates c else 0) ≤ p^U.card := by
  intro t U hU hP
  have hh:=hIH (U.image (fun j=>(t,j))) ⟨t,U,rfl,hU⟩ (by
    apply Set.disjoint_left.mpr
    intro z hz hzu
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hzu
    exact hP j hj hz)
  have hinj : Function.Injective (fun j : V=>(t,j)) := fun _ _ h=>(Prod.mk.inj h).2
  simpa only [Finset.card_image_of_injective _ hinj,Finset.forall_mem_image,
    missing_iff_not_hit,layerMass_pinDensity,layerHistory,LayeredExchange.coinWiring] using hh

lemma returnFraction_layer {m : ℕ} (s : Equiv.Perm (Fin m)) (a b : Fin m → V)
    (rates : Fin m → ℝ) (E : Set (Fin m×V)) (U : Finset (Fin m×V)) :
    returnFraction (LayeredExchange.layerWeight rates) (LayeredExchange.coinWiring s a b) E U=
      (∑ c,layerMass s a b (E∪(U:Set (Fin m×V))) rates c *
        returnCount (layerHistory s (fun i=>Equiv.swap (a i) (b i)) c) (E∪(U:Set (Fin m×V))) (testPins E U))/U.card := by
  unfold returnFraction returnCount
  rw [coinWiring_eq_history]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [layerMass_pinDensity,coinWiring_eq_history]
  split_ifs <;> simp_all only [mul_one,mul_zero]

end Heisenberg.Exposure
end

end OAI
