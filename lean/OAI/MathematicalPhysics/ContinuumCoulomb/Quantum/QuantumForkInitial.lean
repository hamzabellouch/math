import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkRounds

namespace OAI

/-! Odd subdivision gives every original incidence its own private fork port. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

def qmaOriginalEndpoint {n m : ℕ} (left right : Fin m → Fin n) (p : Fin m × Fin 2) : Fin n :=
  if p.2 = 0 then left p.1 else right p.1

def qmaOriginalPortCount {n m : ℕ} (left right : Fin m → Fin n) (i : Fin n) : ℕ :=
  Fintype.card {p : Fin m × Fin 2 // qmaOriginalEndpoint left right p = i}

def qmaOriginalPortEquiv {n m : ℕ} (left right : Fin m → Fin n) :
    (Σ i, Fin (qmaOriginalPortCount left right i)) ≃ Fin m × Fin 2 :=
  (Equiv.sigmaCongrRight (fun i => (Fintype.equivFin
    {p : Fin m × Fin 2 // qmaOriginalEndpoint left right p = i}).symm)).trans
      (Equiv.sigmaFiberEquiv (qmaOriginalEndpoint left right))

theorem qmaOriginalPortCount_eq_degree {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (i : Fin n) :
    qmaOriginalPortCount left right i = qmaGraphDegree left right i := by
  unfold qmaOriginalPortCount
  rw [Fintype.card_subtype]
  have hc : (∑ p : Fin m × Fin 2, if qmaOriginalEndpoint left right p = i then 1 else 0 : ℕ) =
      (Finset.univ.filter (fun p => qmaOriginalEndpoint left right p = i)).card := by simp
  rw [← hc]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two,qmaOriginalEndpoint]
  apply Finset.sum_congr rfl
  intro e _
  have h := hneq e
  by_cases hl : left e = i <;> by_cases hr : right e = i <;> simp_all

def qmaSubdivisionPorts {n m : ℕ} (left right : Fin m → Fin n) :
    QMAForkPorts (n+m*2) n (qmaOriginalPortCount left right) where
  center := old n m
  port := fun p => fresh n m (qmaOriginalPortEquiv left right p).1
    (qmaOriginalPortEquiv left right p).2
  center_injective := old_injective n m
  port_injective := (fresh_injective n m).comp (qmaOriginalPortEquiv left right).injective
  center_ne_port := fun _ _ => old_ne_fresh n m _ _ _

def qmaSubdivisionLeft (n m : ℕ) (e : Fin m) : Fin (n+m*2) := fresh n m e 0
def qmaSubdivisionRight (n m : ℕ) (e : Fin m) : Fin (n+m*2) := fresh n m e 1

theorem qmaSubdivision_distinct (n m : ℕ) (e : Fin m) :
    qmaSubdivisionLeft n m e ≠ qmaSubdivisionRight n m e := by
  intro h
  have hh := fresh_injective n m (a₁ := (e,0)) (a₂ := (e,1)) h
  have := congrArg Prod.snd hh
  norm_num at this

theorem qmaSubdivision_old_degree (n m : ℕ) (v : Fin n) :
    qmaGraphDegree (qmaSubdivisionLeft n m) (qmaSubdivisionRight n m) (old n m v) = 0 := by
  have h (e : Fin m) (b : Fin 2) : fresh n m e b ≠ old n m v := (old_ne_fresh n m v e b).symm
  simp [qmaGraphDegree,qmaSubdivisionLeft,qmaSubdivisionRight,h]

theorem qmaSubdivision_fresh_degree (n m : ℕ) (e : Fin m) (b : Fin 2) :
    qmaGraphDegree (qmaSubdivisionLeft n m) (qmaSubdivisionRight n m) (fresh n m e b) = 1 := by
  have hh (f : Fin m) (a : Fin 2) : fresh n m f a = fresh n m e b ↔ f = e ∧ a = b := by
    constructor
    · intro h
      exact Prod.mk.inj (fresh_injective n m (a₁ := (f,a)) (a₂ := (e,b)) h)
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [qmaGraphDegree,qmaSubdivisionLeft,qmaSubdivisionRight,hh]
  fin_cases b <;> simp

def qmaSubdivisionState {n m : ℕ} (left right : Fin m → Fin n) :
    QMAForkState (n+m*2) n (qmaOriginalPortCount left right) (Fin m) where
  ports := qmaSubdivisionPorts left right
  left := qmaSubdivisionLeft n m
  right := qmaSubdivisionRight n m
  distinct := qmaSubdivision_distinct n m
  degree_le := by
    intro v
    obtain ⟨v,rfl⟩ := (vertexEquiv n m).surjective v
    rcases v with v | ⟨e,b⟩
    · rw [show vertexEquiv n m (.inl v) = old n m v from rfl,qmaSubdivision_old_degree]
      omega
    · rw [show vertexEquiv n m (.inr (e,b)) = fresh n m e b from rfl,
        qmaSubdivision_fresh_degree]
      omega
  center_degree := qmaSubdivision_old_degree n m
  port_degree := by
    intro p
    change qmaGraphDegree _ _ (fresh n m (qmaOriginalPortEquiv left right p).1
      (qmaOriginalPortEquiv left right p).2) ≤ 1
    rw [qmaSubdivision_fresh_degree]

def qmaSubdivisionNetwork {n m : ℕ} (left right : Fin m → Fin n) : QMAForkNetwork n where
  n := n+m*2
  degree := qmaOriginalPortCount left right
  Edge := Fin m
  state := qmaSubdivisionState left right

theorem qmaSubdivision_degree_three {n m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ e, left e ≠ right e) (D : ℕ)
    (hD : ∀ i, qmaGraphDegree left right i ≤ D)
    (v : Fin ((qmaSubdivisionNetwork left right).iterate D).n) :
    qmaGraphDegree ((qmaSubdivisionNetwork left right).iterate D).state.fullLeft
      ((qmaSubdivisionNetwork left right).iterate D).state.fullRight v ≤ 3 := by
  apply QMAForkNetwork.constant_round_degree
  intro i
  exact (qmaOriginalPortCount_eq_degree left right hneq i).le.trans (hD i)

end ContinuumCoulomb

end

end OAI
