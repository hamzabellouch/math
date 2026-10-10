import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkPorts

namespace OAI

/-! The part of a fork layer left after its new active center edges are removed. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
variable {ν : Type*} [Fintype ν]

def qmaForkBackgroundLeft {n r : ℕ} (left : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) :=
  qmaParallelGraphLeft (qmaForksBaseLeft left site)
    (fun e b => qmaForkOuter site (e,b))

def qmaForkBackgroundRight {n r : ℕ} (right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) :=
  qmaParallelGraphRight (qmaForksBaseRight right site)
    (fun (_ : Fin r) (_ : Fin 2) => (1 : Fin 2))

theorem qmaForkBackground_old_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (v : Fin n) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site)
      (old n r v) = qmaGraphDegree left right v +
        2 * ∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0)) := by
  unfold qmaForkBackgroundLeft qmaForkBackgroundRight
  rw [qmaParallelGraph_old_degree]
  simp only [qmaForksBaseLeft,qmaForksBaseRight]
  rw [qmaGraphDegree_sum]
  have hc : qmaGraphDegree (fun e => site e 1) (fun e => site e 2) v =
      ∑ e, ((if site e 1 = v then 1 else 0)+(if site e 2 = v then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro e _
    have hne : site e 1 ≠ site e 2 := fun h => (by decide : (1:Fin 3) ≠ 2) (hsite e h)
    by_cases h1 : site e 1 = v <;> by_cases h2 : site e 2 = v <;> simp_all
  change qmaGraphDegree left right v + qmaGraphDegree (fun e => site e 1) (fun e => site e 2) v + _ = _
  rw [hc]
  simp only [Fin.sum_univ_two,qmaForkOuter,ite_true]
  norm_num only [show (1 : Fin 2) ≠ 0 by decide]
  simp only [ite_false]
  omega

theorem qmaForkBackground_new_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (e : Fin r) (b : Fin 2) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site)
      (fresh n r e b) = if b = 0 then 1 else 3 := by
  unfold qmaForkBackgroundLeft qmaForkBackgroundRight
  rw [qmaParallelGraph_new_degree]
  simp only [Fin.sum_univ_two]
  fin_cases b <;> norm_num

theorem qmaForkBackground_away_degree {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (v : Fin n) (hv : ∀ e, site e 1 ≠ v ∧ site e 2 ≠ v) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site)
      (old n r v) = qmaGraphDegree left right v := by
  rw [qmaForkBackground_old_degree left right site hsite]
  simp [hv]

theorem qmaForkBackground_degree_le_three {n r : ℕ} (left right : ν → Fin n)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (houter : Function.Injective (qmaForkOuter site))
    (hbase : ∀ v, qmaGraphDegree left right v ≤ 3)
    (hport : ∀ e b, qmaGraphDegree left right (qmaForkOuter site (e,b)) ≤ 1)
    (v : Fin (n+r*2)) :
    qmaGraphDegree (qmaForkBackgroundLeft left site) (qmaForkBackgroundRight right site) v ≤ 3 := by
  obtain ⟨v,rfl⟩ := (vertexEquiv n r).surjective v
  rcases v with v | ⟨e,b⟩
  · change qmaGraphDegree (qmaForkBackgroundLeft left site)
      (qmaForkBackgroundRight right site) (old n r v) ≤ 3
    by_cases hp : ∃ e b, qmaForkOuter site (e,b) = v
    · obtain ⟨e,b,rfl⟩ := hp
      rw [qmaForkBackground_old_degree left right site hsite]
      have hc := qmaForkOuter_count site houter (qmaForkOuter site (e,b))
      have hb := hport e b
      omega
    · have hv : ∀ e, site e 1 ≠ v ∧ site e 2 ≠ v := by
        intro e
        constructor
        · intro h
          exact hp ⟨e,0,by simpa [qmaForkOuter] using h⟩
        · intro h
          exact hp ⟨e,1,by simpa [qmaForkOuter] using h⟩
      rw [qmaForkBackground_away_degree left right site hsite v hv]
      exact hbase v
  · change qmaGraphDegree (qmaForkBackgroundLeft left site)
      (qmaForkBackgroundRight right site) (fresh n r e b) ≤ 3
    rw [qmaForkBackground_new_degree]
    split <;> omega

end ContinuumCoulomb

end

end OAI
