import OAI.Combinatorics.ContingencyTables.Transport.PublishedEdmondsKarp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # Integral augmentation along a simple path

The identities here prove conservation and capacity preservation for the
literal forward-minus-reverse update in the published-input interface.
-/

namespace ContingencyTables.PathAugmentation

open PublishedEdmondsKarp
open scoped BigOperators

variable {n k : ℕ}

def arcCount (p : Fin (k+1) → Fin n) (u v : Fin n) : ℤ :=
  ∑ i : Fin k,if p i.castSucc=u ∧ p i.succ=v then 1 else 0

def update (f : Flow n) (p : Fin (k+1) → Fin n) (a : ℤ) : Flow n :=
  fun u v=>f u v+a*(arcCount p u v-arcCount p v u)

lemma arcCount_nonneg (p : Fin (k+1) → Fin n) (u v : Fin n) :
    0≤arcCount p u v := by
  apply Finset.sum_nonneg
  intro i _
  split <;> omega

lemma arcCount_eq_zero (p : Fin (k+1) → Fin n) (u v : Fin n)
    (h : ¬∃ i : Fin k,p i.castSucc=u ∧ p i.succ=v) : arcCount p u v=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun hi=>h ⟨i,hi⟩)

lemma arcCount_eq_one (p : Fin (k+1) → Fin n) (hp : Function.Injective p)
    (i : Fin k) : arcCount p (p i.castSucc) (p i.succ)=1 := by
  unfold arcCount
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    apply ite_eq_right
    intro h
    exact hji (Fin.castSucc_inj.mp (hp h.1))
  · simp

lemma arcCount_le_one (p : Fin (k+1) → Fin n) (hp : Function.Injective p)
    (u v : Fin n) : arcCount p u v≤1 := by
  by_cases h : ∃ i : Fin k,p i.castSucc=u ∧ p i.succ=v
  · obtain ⟨i,rfl,rfl⟩ := h
    exact (arcCount_eq_one p hp i).le
  · rw [arcCount_eq_zero p u v h]
    omega

lemma row_arcCount (p : Fin (k+1) → Fin n) (u : Fin n) :
    (∑ v,arcCount p u v)=∑ i : Fin k,if p i.castSucc=u then (1:ℤ) else 0 := by
  unfold arcCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i.castSucc=u
  · simp [h]
  · simp [h]

lemma column_arcCount (p : Fin (k+1) → Fin n) (u : Fin n) :
    (∑ v,arcCount p v u)=∑ i : Fin k,if p i.succ=u then (1:ℤ) else 0 := by
  unfold arcCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i.succ=u
  · simp [h]
  · simp [h]

lemma path_divergence (p : Fin (k+1) → Fin n) (u : Fin n) :
    (∑ v : Fin n,(arcCount p u v-arcCount p v u))=
      (if p 0=u then (1:ℤ) else 0)-(if p (Fin.last k)=u then 1 else 0) := by
  have he : (∑ v : Fin n,(arcCount p u v-arcCount p v u))=
      (∑ v : Fin n,arcCount p u v)-(∑ v : Fin n,arcCount p v u) :=
    Finset.sum_sub_distrib (fun v : Fin n=>arcCount p u v) (fun v : Fin n=>arcCount p v u)
  have h1 := Fin.sum_univ_castSucc (fun i : Fin (k+1)=>if p i=u then (1:ℤ) else 0)
  have h2 := Fin.sum_univ_succ (fun i : Fin (k+1)=>if p i=u then (1:ℤ) else 0)
  rw [row_arcCount,column_arcCount] at he
  omega

lemma update_skew (f : Flow n) (hf : ∀ u v,f u v= -f v u)
    (p : Fin (k+1) → Fin n) (a : ℤ) :
    ∀ u v,update f p a u v= -update f p a v u := by
  intro u v
  unfold update
  rw [hf u v]
  ring

lemma update_capacity (c : Capacity n) (f : Flow n)
    (hf : ∀ u v,f u v≤c u v) (p : Fin (k+1) → Fin n)
    (hp : Function.Injective p) (a : ℤ) (ha : 0≤a)
    (hres : ∀ i : Fin k,a≤(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) :
    ∀ u v,update f p a u v≤c u v := by
  intro u v
  have hr := arcCount_nonneg p v u
  by_cases he : ∃ i : Fin k,p i.castSucc=u ∧ p i.succ=v
  · obtain ⟨i,rfl,rfl⟩ := he
    rw [update,arcCount_eq_one p hp i]
    have h := hres i
    have hn := mul_nonneg ha hr
    nlinarith
  · rw [update,arcCount_eq_zero p u v he]
    have h := hf u v
    have hn := mul_nonneg ha hr
    nlinarith

lemma update_sum (f : Flow n) (p : Fin (k+1) → Fin n) (a : ℤ) (u : Fin n) :
    (∑ v,update f p a u v)=(∑ v,f u v)+
      a*((if p 0=u then (1:ℤ) else 0)-(if p (Fin.last k)=u then 1 else 0)) := by
  simp only [update,Finset.sum_add_distrib,←Finset.mul_sum]
  exact congrArg (fun z : ℤ=>(∑ v,f u v)+a*z) (path_divergence p u)

theorem update_feasible (c : Capacity n) (s t : Fin n) (f : Flow n)
    (hf : Feasible c s t f) (p : Fin (k+1) → Fin n)
    (hp : ResidualPath c f s t k p) (a : ℤ) (ha : 0≤a)
    (hres : ∀ i : Fin k,a≤(c (p i.castSucc) (p i.succ):ℤ)-f (p i.castSucc) (p i.succ)) :
    Feasible c s t (update f p a) := by
  refine ⟨update_skew f hf.1 p a,update_capacity c f hf.2.1 p hp.2.2.1 a ha hres,?_⟩
  intro u hus hut
  rw [update_sum,hp.1,hp.2.1,hf.2.2 u hus hut]
  simp [Ne.symm hus,Ne.symm hut]

theorem update_value (c : Capacity n) (s t : Fin n) (hst : s≠t)
    (f : Flow n) (p : Fin (k+1) → Fin n)
    (hp : ResidualPath c f s t k p) (a : ℤ) :
    value s (update f p a)=value s f+a := by
  unfold value
  rw [update_sum,hp.1,hp.2.1]
  simp [Ne.symm hst]

end ContingencyTables.PathAugmentation

end OAI
