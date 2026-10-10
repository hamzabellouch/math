import OAI.Analysis.MarkovType.FiniteChains

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

structure FiniteMarkedChain (S E : Type*) [Fintype S] [Fintype E] where
  π : S → ℝ
  π_nonneg : ∀ s, 0 ≤ π s
  sum_π : ∑ s, π s = 1
  src : E → S
  tgt : E → S
  rev : E → E
  rev_rev : Function.Involutive rev
  src_rev : ∀ e, src (rev e) = tgt e
  tgt_rev : ∀ e, tgt (rev e) = src e
  q : E → ℝ
  q_nonneg : ∀ e, 0 ≤ q e
  sum_q : ∀ s, ∑ e, (if src e = s then q e else 0) = 1
  balance : ∀ e, π (src e) * q e = π (tgt e) * q (rev e)

abbrev MarkedPath (S E : Type*) (n : ℕ) := S × (Fin n → E)

def markedState {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) {n : ℕ} (ω : MarkedPath S E n)
    (i : Fin (n + 1)) : S :=
  if h : i = 0 then ω.1 else C.tgt (ω.2 (i.pred h))

def markedValid {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) {n : ℕ} (ω : MarkedPath S E n) : Prop :=
  ∀ i : Fin n, C.src (ω.2 i) = markedState C ω i.castSucc

def markedPathWeight {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) (n : ℕ) (ω : MarkedPath S E n) : ℝ := by
  classical
  exact if markedValid C ω then C.π ω.1 * ∏ i : Fin n, C.q (ω.2 i) else 0

def markedExpect {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) (n : ℕ) (F : MarkedPath S E n → ℝ) : ℝ :=
  ∑ ω, markedPathWeight C n ω * F ω

def markedProb {S E : Type*} [Fintype S] [Fintype E]
    (C : FiniteMarkedChain S E) (n : ℕ) (A : MarkedPath S E n → Prop) : ℝ := by
  classical
  exact ∑ ω, if A ω then markedPathWeight C n ω else 0

def edgeSum {S E V : Type*} [AddCommMonoid V] {n : ℕ}
    (g : E → V) (ω : MarkedPath S E n) : V :=
  ∑ i : Fin n, g (ω.2 i)

def stationaryEdgeCost {S E V : Type*} [Fintype S] [Fintype E]
    [NormedAddCommGroup V] (C : FiniteMarkedChain S E) (g : E → V) (p : ℝ) : ℝ :=
  ∑ e, C.π (C.src e) * C.q e * Real.rpow (‖g e‖) p

def markedSumCost {S E V : Type*} [Fintype S] [Fintype E]
    [NormedAddCommGroup V] (C : FiniteMarkedChain S E) (g : E → V) (p : ℝ)
    (n : ℕ) : ℝ :=
  markedExpect C n (fun ω => Real.rpow (‖edgeSum g ω‖) p)

def OddLabel {S E V : Type*} [Fintype S] [Fintype E] [Neg V]
    (C : FiniteMarkedChain S E) (g : E → V) : Prop :=
  ∀ e, g (C.rev e) = -g e

end MarkovSuperreflexivity

end

end OAI
