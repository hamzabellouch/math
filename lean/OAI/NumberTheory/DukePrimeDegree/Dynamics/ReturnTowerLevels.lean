import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic

namespace OAI

/-! # Disjoint towers for positive first return times -/

open Set Function
namespace DukePrimeDegree

/-- The points of `S` whose first positive return occurs at time `n+1`. -/
def firstReturnLevel {Y : Type*} (T : Y → Y) (S : Set Y) (n : ℕ) : Set Y :=
  {x | x ∈ S ∧ T^[n+1] x ∈ S ∧ ∀ j, 0 < j → j ≤ n → T^[j] x ∉ S}

theorem measurableSet_firstReturnLevel {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {S : Set Y} (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet (firstReturnLevel T S n) := by
  have he : {x | ∀ j : ℕ, 0 < j → j ≤ n → T^[j] x ∉ S} =
      ⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j ≤ n), (T^[j] ⁻¹' S)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_compl_iff,Set.mem_preimage]
  have hm : MeasurableSet {x | ∀ j : ℕ, 0 < j → j ≤ n → T^[j] x ∉ S} := by
    rw [he]
    exact MeasurableSet.iInter fun (j : ℕ) => MeasurableSet.iInter fun (_ : 0 < j) =>
      MeasurableSet.iInter fun (_ : j ≤ n) => (hS.preimage (hT.iterate j)).compl
  exact hS.inter ((hS.preimage (hT.iterate (n+1))).inter hm)

theorem firstReturnLevel_unique {Y : Type*} (T : Y → Y) (S : Set Y)
    {n m : ℕ} {x : Y} (hn : x ∈ firstReturnLevel T S n)
    (hm : x ∈ firstReturnLevel T S m) : n=m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hm.2.2 (n+1) (by omega) (by omega) hn.2.1).elim
  · exact h
  · exact (hn.2.2 (m+1) (by omega) (by omega) hm.2.1).elim

/-- Distinct levels and heights cannot meet after translating up their
return towers. No recurrence or ergodicity hypothesis is needed. -/
theorem firstReturnTower_unique {Y : Type*} (T : Y → Y) (hT : Injective T)
    (S : Set Y) {n m j k : ℕ} {x y : Y}
    (hx : x ∈ firstReturnLevel T S n) (hy : y ∈ firstReturnLevel T S m)
    (hj : j ≤ n) (hk : k ≤ m) (he : T^[j] x=T^[k] y) : n=m ∧ j=k := by
  have hheight : j=k := by
    rcases lt_trichotomy j k with h | h | h
    · have he' : T^[j] x=T^[j] (T^[k-j] y) := by
        rw [←Function.iterate_add_apply]
        simpa only [Nat.add_sub_of_le h.le] using he
      have hxy : x=T^[k-j] y := (hT.iterate j) he'
      exact (hy.2.2 (k-j) (by omega) (by omega) (hxy ▸ hx.1)).elim
    · exact h
    · have he' : T^[k] y=T^[k] (T^[j-k] x) := by
        rw [←Function.iterate_add_apply]
        simpa only [Nat.add_sub_of_le h.le] using he.symm
      have hyx : y=T^[j-k] x := (hT.iterate k) he'
      exact (hx.2.2 (j-k) (by omega) (by omega) (hyx ▸ hy.1)).elim
  subst k
  have hxy : x=y := (hT.iterate j) he
  subst y
  exact ⟨firstReturnLevel_unique T S hx hy,rfl⟩

def firstReturnTower {Y : Type*} (T : Y → Y) (S : Set Y)
    (p : Σ n : ℕ, Fin (n+1)) : Set Y := T^[p.2.val] '' firstReturnLevel T S p.1

theorem pairwise_disjoint_firstReturnTower {Y : Type*} (T : Y → Y)
    (hT : Injective T) (S : Set Y) : Pairwise (Disjoint on firstReturnTower T S) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have H := firstReturnTower_unique T hT S hx hy (by have := p.2.isLt; omega)
    (by have := q.2.isLt; omega) he.symm
  apply hpq
  rcases p with ⟨n,j⟩
  rcases q with ⟨m,k⟩
  dsimp at H
  rcases H with ⟨rfl,hjk⟩
  exact congrArg (Sigma.mk n) (Fin.ext hjk)

end DukePrimeDegree

end OAI
