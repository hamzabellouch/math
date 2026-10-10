import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumParallelGraph

namespace OAI

/-! Incidence counts for the actual ordinary-spin routing graphs. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν κ : Type*} [Fintype ν] [Fintype κ]

def qmaGraphDegree {n : ℕ} (left right : ν → Fin n) (v : Fin n) : ℕ :=
  ∑ e, if left e = v ∨ right e = v then 1 else 0

theorem qmaParallelGraph_old_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (v : Fin n) :
    qmaGraphDegree (qmaParallelGraphLeft left site) (qmaParallelGraphRight right member) (old n r v) =
      qmaGraphDegree left right v + ∑ e, ∑ a, if site e a = v then 1 else 0 := by
  have ho := old_injective n r
  have hf (e : Fin r) (b : Fin 2) : fresh n r e b ≠ old n r v := (old_ne_fresh n r v e b).symm
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp [qmaParallelGraphLeft,qmaParallelGraphRight,ho.eq_iff,hf]

theorem qmaParallelGraph_new_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → κ → Fin n) (member : Fin r → κ → Fin 2) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaParallelGraphLeft left site) (qmaParallelGraphRight right member) (fresh n r e b) =
      1 + ∑ a, if member e a = b then 1 else 0 := by
  have hf := fresh_injective n r
  have ho (v : Fin n) : old n r v ≠ fresh n r e b := old_ne_fresh n r v e b
  have heq (f : Fin r) (a : Fin 2) : fresh n r f a = fresh n r e b ↔ f = e ∧ a = b := by
    constructor
    · intro h
      have hh : (f,a) = (e,b) := hf h
      exact Prod.mk.inj hh
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [qmaParallelGraphLeft,qmaParallelGraphRight,ho,false_or,heq,ite_false,
    Finset.sum_const_zero,zero_add]
  have hc : (∑ f : Fin r, if f = e ∧ (0:Fin 2) = b ∨ f = e ∧ (1:Fin 2) = b then 1 else 0) = 1 := by
    fin_cases b <;> simp
  rw [hc]
  apply congrArg (1+·)
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp [hfe]
  · simp

theorem qmaParallelGraph_fork_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaParallelGraphLeft left site)
      (qmaParallelGraphRight right (fun _ => qmaForkMember)) (fresh n r e b) =
        if b = 0 then 2 else 3 := by
  rw [qmaParallelGraph_new_degree]
  fin_cases b <;> simp [qmaForkMember,Fin.sum_univ_three]

end ContinuumCoulomb

end

end OAI
