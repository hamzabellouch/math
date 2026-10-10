import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkDegreeBound
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkDegrees

namespace OAI

/-! Private active ports remain private after a simultaneous fork round. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

abbrev QMAForkPair {c : ℕ} (d : Fin c → ℕ) := Σ i, Fin (d i / 2)
abbrev QMAForkRemainder {c : ℕ} (d : Fin c → ℕ) := Σ i, Fin (d i % 2)

def qmaForkAllPortEquiv {c : ℕ} (d : Fin c → ℕ) :
    ((Σ i, Fin (d i / 2) × Fin 2) ⊕ QMAForkRemainder d) ≃ (Σ i, Fin (d i)) :=
  (Equiv.sigmaSumDistrib (fun i => Fin (d i / 2) × Fin 2)
    (fun i => Fin (d i % 2))).symm.trans
      (Equiv.sigmaCongrRight (fun i => qmaForkPortEquiv (d i)))

def qmaForkPairedPort {c : ℕ} (d : Fin c → ℕ) (p : QMAForkPair d × Fin 2) :
    Σ i, Fin (d i) :=
  qmaForkAllPortEquiv d (.inl (Equiv.sigmaProdDistrib (fun i => Fin (d i / 2)) (Fin 2) p))

def qmaForkRemainingPort {c : ℕ} (d : Fin c → ℕ) (p : QMAForkRemainder d) :
    Σ i, Fin (d i) := qmaForkAllPortEquiv d (.inr p)

theorem qmaForkPairedPort_injective {c : ℕ} (d : Fin c → ℕ) :
    Function.Injective (qmaForkPairedPort d) :=
  (qmaForkAllPortEquiv d).injective.comp
    (Sum.inl_injective.comp (Equiv.sigmaProdDistrib _ _).injective)

theorem qmaForkRemainingPort_injective {c : ℕ} (d : Fin c → ℕ) :
    Function.Injective (qmaForkRemainingPort d) :=
  (qmaForkAllPortEquiv d).injective.comp Sum.inr_injective

theorem qmaForkPairedPort_ne_remaining {c : ℕ} (d : Fin c → ℕ)
    (p : QMAForkPair d × Fin 2) (q : QMAForkRemainder d) :
    qmaForkPairedPort d p ≠ qmaForkRemainingPort d q := by
  intro h
  have := (qmaForkAllPortEquiv d).injective h
  cases this

structure QMAForkPorts (n c : ℕ) (d : Fin c → ℕ) where
  center : Fin c → Fin n
  port : (Σ i, Fin (d i)) → Fin n
  center_injective : Function.Injective center
  port_injective : Function.Injective port
  center_ne_port : ∀ i p, center i ≠ port p

namespace QMAForkPorts
variable {n c : ℕ} {d : Fin c → ℕ} (P : QMAForkPorts n c d)

abbrev pairCount (_P : QMAForkPorts n c d) := Fintype.card (QMAForkPair d)
def pairEquiv : QMAForkPair d ≃ Fin (P.pairCount) := Fintype.equivFin _

def site (e : Fin P.pairCount) : Fin 3 → Fin n :=
  ![P.center (P.pairEquiv.symm e).1,
    P.port (qmaForkPairedPort d (P.pairEquiv.symm e,0)),
    P.port (qmaForkPairedPort d (P.pairEquiv.symm e,1))]

theorem site_injective (e : Fin P.pairCount) : Function.Injective (P.site e) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [site] at h ⊢
  · exact (P.center_ne_port _ _ h).elim
  · exact (P.center_ne_port _ _ h).elim
  · exact (P.center_ne_port _ _ h.symm).elim
  · have hh := qmaForkPairedPort_injective d (P.port_injective h)
    have := congrArg Prod.snd hh
    norm_num at this
  · exact (P.center_ne_port _ _ h.symm).elim
  · have hh := qmaForkPairedPort_injective d (P.port_injective h)
    have := congrArg Prod.snd hh
    norm_num at this

theorem outer_injective : Function.Injective (qmaForkOuter P.site) := by
  have hf : qmaForkOuter P.site = fun p =>
      P.port (qmaForkPairedPort d (P.pairEquiv.symm p.1,p.2)) := by
    funext p
    rcases p with ⟨e,b⟩
    fin_cases b <;> simp [qmaForkOuter,site]
  rw [hf]
  exact P.port_injective.comp ((qmaForkPairedPort_injective d).comp
    (Equiv.prodCongr P.pairEquiv.symm (Equiv.refl _)).injective)

def nextPortEquiv (_P : QMAForkPorts n c d) : (Σ i, Fin (d i / 2 + d i % 2)) ≃
    QMAForkPair d ⊕ QMAForkRemainder d :=
  (Equiv.sigmaCongrRight (fun _ => finSumFinEquiv.symm)).trans
    (Equiv.sigmaSumDistrib _ _)

def nextPortAux : QMAForkPair d ⊕ QMAForkRemainder d → Fin (n + P.pairCount*2)
  | .inl p => fresh n P.pairCount (P.pairEquiv p) 0
  | .inr p => old n P.pairCount (P.port (qmaForkRemainingPort d p))

theorem nextPortAux_injective : Function.Injective P.nextPortAux := by
  intro p q h
  rcases p with p | p <;> rcases q with q | q
  · apply congrArg Sum.inl
    apply P.pairEquiv.injective
    exact congrArg Prod.fst (fresh_injective n P.pairCount
      (a₁ := (P.pairEquiv p,0)) (a₂ := (P.pairEquiv q,0)) h)
  · exact ((old_ne_fresh n P.pairCount _ _ _) h.symm).elim
  · exact ((old_ne_fresh n P.pairCount _ _ _) h).elim
  · apply congrArg Sum.inr
    exact qmaForkRemainingPort_injective d (P.port_injective (old_injective n P.pairCount h))

def next : QMAForkPorts (n + P.pairCount*2) c (fun i => d i / 2 + d i % 2) where
  center := fun i => old n P.pairCount (P.center i)
  port := P.nextPortAux ∘ P.nextPortEquiv
  center_injective := (old_injective n P.pairCount).comp P.center_injective
  port_injective := P.nextPortAux_injective.comp P.nextPortEquiv.injective
  center_ne_port := by
    intro i p
    change old n P.pairCount (P.center i) ≠ P.nextPortAux (P.nextPortEquiv p)
    rcases P.nextPortEquiv p with q | q
    · exact old_ne_fresh n P.pairCount _ _ _
    · intro h
      exact P.center_ne_port _ _ (old_injective n P.pairCount h)

theorem pairCount_bound : P.pairCount ≤ ∑ i, d i := by
  change Fintype.card (QMAForkPair d) ≤ _
  simp only [QMAForkPair,Fintype.card_sigma,Fintype.card_fin]
  exact Finset.sum_le_sum (fun i _ => Nat.div_le_self _ _)

end QMAForkPorts
end ContinuumCoulomb

end

end OAI
