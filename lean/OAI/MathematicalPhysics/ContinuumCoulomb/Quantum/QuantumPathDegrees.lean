import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGraphDegree
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsGraph

namespace OAI

/-! Path subdivision preserves every old degree and adds only bounded-degree vertices. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

theorem qmaPaths_new_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 2 → Fin n) (even : Fin r → Bool) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaParallelGraphLeft left site)
      (qmaParallelGraphRight right (fun f => qmaPathMember (even f))) (fresh n r e b) ≤ 3 := by
  rw [qmaParallelGraph_new_degree]
  simp only [Fin.sum_univ_two]
  cases even e <;> fin_cases b <;> norm_num [qmaPathMember]

theorem qmaPaths_old_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 2 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (even : Fin r → Bool) (v : Fin n) :
    qmaGraphDegree (qmaParallelGraphLeft left site)
      (qmaParallelGraphRight right (fun e => qmaPathMember (even e))) (old n r v) =
    qmaGraphDegree (Sum.elim left (fun e => site e 0)) (Sum.elim right (fun e => site e 1)) v := by
  rw [qmaParallelGraph_old_degree]
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_two]
  apply congrArg (fun x => (∑ a, if left a = v ∨ right a = v then 1 else 0)+x)
  apply Finset.sum_congr rfl
  intro e _
  have hne : site e 0 ≠ site e 1 := fun h => (by decide : (0:Fin 2) ≠ 1) (hsite e h)
  by_cases h0 : site e 0 = v <;> by_cases h1 : site e 1 = v <;> simp_all

theorem qmaCrossings_new_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 4 → Fin n) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaParallelGraphLeft left site)
      (qmaParallelGraphRight right (fun _ => qmaCrossingMember)) (fresh n r e b) = 3 := by
  rw [qmaParallelGraph_new_degree]
  simp only [Fin.sum_univ_four]
  fin_cases b <;> norm_num [qmaCrossingMember]

end ContinuumCoulomb

end

end OAI
