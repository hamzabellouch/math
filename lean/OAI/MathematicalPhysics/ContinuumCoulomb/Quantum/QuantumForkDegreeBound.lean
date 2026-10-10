import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGraphDegree
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkGraph

namespace OAI

/-! Degree control for many fork centers sharing a retained background graph. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

theorem qmaGraphDegree_sum {n : ℕ} {κ : Type*} [Fintype κ]
    (left right : ν → Fin n) (left' right' : κ → Fin n) (v : Fin n) :
    qmaGraphDegree (Sum.elim left left') (Sum.elim right right') v =
      qmaGraphDegree left right v+qmaGraphDegree left' right' v := by
  simp only [qmaGraphDegree,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

theorem qmaCount_eq_le_one {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (v : β) :
    (∑ a, if f a = v then 1 else 0 : ℕ) ≤ 1 := by
  simp only [Finset.sum_boole]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact hf ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)

def qmaForkOuter {n r : ℕ} (site : Fin r → Fin 3 → Fin n) (p : Fin r × Fin 2) : Fin n :=
  site p.1 (if p.2 = 0 then 1 else 2)

theorem qmaForkOuter_count {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (houter : Function.Injective (qmaForkOuter site)) (v : Fin n) :
    (∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0) : ℕ)) ≤ 1 := by
  have h := qmaCount_eq_le_one (qmaForkOuter site) houter v
  simpa [qmaForkOuter,Fintype.sum_prod_type,Fin.sum_univ_two] using h

theorem qmaForks_old_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (v : Fin n) :
    qmaGraphDegree (qmaParallelGraphLeft (qmaForksBaseLeft left site) site)
      (qmaParallelGraphRight (qmaForksBaseRight right site) (fun _ => qmaForkMember)) (old n r v) =
      qmaGraphDegree left right v+
        (∑ e, if site e 1 = v ∨ site e 2 = v then 1 else 0)+
        ∑ e, ((if site e 0 = v then 1 else 0)+(if site e 1 = v then 1 else 0)+
          (if site e 2 = v then 1 else 0)) := by
  rw [qmaParallelGraph_old_degree]
  simp only [qmaGraphDegree,Fintype.sum_sum_type,qmaForksBaseLeft,qmaForksBaseRight,
    Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_three]
  rfl

theorem qmaForks_noncenter_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (houter : Function.Injective (qmaForkOuter site))
    (v : Fin n) (hcenter : ∀ e, site e 0 ≠ v) (hbase : qmaGraphDegree left right v ≤ 1) :
    qmaGraphDegree (qmaParallelGraphLeft (qmaForksBaseLeft left site) site)
      (qmaParallelGraphRight (qmaForksBaseRight right site) (fun _ => qmaForkMember)) (old n r v) ≤ 3 := by
  have hp := qmaForkOuter_count site houter v
  have hc : (∑ e, if site e 1 = v ∨ site e 2 = v then 1 else 0 : ℕ) ≤
      ∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0) : ℕ) := by
    apply Finset.sum_le_sum
    intro e _
    split_ifs <;> omega
  rw [qmaForks_old_degree]
  simp only [hcenter,ite_false,zero_add]
  omega

theorem qmaForks_center_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (v : Fin n)
    (houter : ∀ e, site e 1 ≠ v ∧ site e 2 ≠ v) :
    qmaGraphDegree (qmaParallelGraphLeft (qmaForksBaseLeft left site) site)
      (qmaParallelGraphRight (qmaForksBaseRight right site) (fun _ => qmaForkMember)) (old n r v) =
        qmaGraphDegree left right v+∑ e, if site e 0 = v then 1 else 0 := by
  rw [qmaForks_old_degree]
  simp [houter]

end ContinuumCoulomb

end

end OAI
