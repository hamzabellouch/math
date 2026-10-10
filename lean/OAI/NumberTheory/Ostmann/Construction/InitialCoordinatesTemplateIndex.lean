import OAI.NumberTheory.Ostmann.Construction.InitialLogGeometry
import OAI.NumberTheory.Ostmann.Construction.TemplateLabels

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialCoordinatesTemplate

@[simp] theorem initialRoles_length (m k : ℕ) :
    (Template.initialRoles m k).length = m + 6 + 4*k := by
  simp [Template.initialRoles, List.length_flatMap, List.map_const', Nat.mul_comm]
  omega

@[simp] theorem initial_length (m k : ℕ) :
    (Template.initial m k).length = m + 6 + 4*k := by
  simp [Template.initial]

theorem matches_initial_length {m k : ℕ} {xs : List SmallSlot}
    (h : Template.Matches (Template.initial m k) xs) : xs.length = m+6+4*k :=
  (Template.matches_length h).trans (initial_length m k)

theorem initialRoles_bulk_iff (m k : ℕ) (i : Fin (Template.initialRoles m k).length) :
    (Template.initialRoles m k)[i.val] = .bulk ↔ i.val < m := by
  by_cases hi : i.val < m
  · constructor
    · exact fun _ => hi
    · intro _
      simp only [Template.initialRoles, List.append_assoc]
      rw [List.getElem_append_left (show i.val < (List.replicate m SlotRole.bulk).length by simpa using hi)]
      exact List.getElem_replicate _
  · have hmi : m ≤ i.val := by omega
    have hrest : SlotRole.bulk ∉ List.replicate 6 SlotRole.top ++
        (List.range k).flatMap (fun j => List.replicate 4 (SlotRole.compensation (j+1))) := by
      simp
    constructor
    · intro hb
      have he : (Template.initialRoles m k)[i.val] ∈
          List.replicate 6 SlotRole.top ++
          (List.range k).flatMap (fun j => List.replicate 4 (SlotRole.compensation (j+1))) := by
        simp only [Template.initialRoles, List.append_assoc]
        rw [List.getElem_append_right (show (List.replicate m SlotRole.bulk).length ≤ i.val by simpa using hmi)]
        exact List.getElem_mem _
      exact (hrest (hb ▸ he)).elim
    · exact fun h => (hi h).elim

theorem matches_initial_metadata {m k : ℕ} {xs : List SmallSlot}
    (h : Template.Matches (Template.initial m k) xs) (i : Fin xs.length) :
    (xs.get i).origin = i.val ∧ ((xs.get i).role = .bulk ↔ i.val < m) := by
  have hi : i.val < (Template.initialRoles m k).length := by
    simpa only [initialRoles_length, ← matches_initial_length h] using i.isLt
  have hlabels := congrArg (fun l : List (SlotRole × ℕ) => l[i.val]?) h
  have hget : (xs.get i).role = (Template.initialRoles m k)[i.val] ∧
      (xs.get i).origin = i.val := by
    have hiN : i.val < m+6+4*k := by simpa only [initialRoles_length] using hi
    simpa [Template.initial, List.getElem?_eq_getElem, i.isLt, hi, hiN] using hlabels
  exact ⟨hget.2, hget.1 ▸ initialRoles_bulk_iff m k ⟨i.val,hi⟩⟩

def halfEquiv (n : ℕ) : (Bool × Fin n) ≃ Fin (2*n) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans finProdFinEquiv

@[simp] theorem halfEquiv_val (n : ℕ) (h : Bool) (i : Fin n) :
    (halfEquiv n (h,i)).val = (if h then n else 0) + i.val := by
  cases h <;> simp [halfEquiv, finTwoEquiv, finProdFinEquiv, Nat.add_comm]

def compensationEquiv (k : ℕ) : (Fin k × (Bool × Fin 2)) ≃ Fin (4*k) :=
  ((Equiv.prodCongr (Equiv.refl _) (halfEquiv 2)).trans finProdFinEquiv).trans
    (finCongr (by omega))

@[simp] theorem compensationEquiv_val (k : ℕ) (j : Fin k) (h : Bool) (i : Fin 2) :
    (compensationEquiv k (j,(h,i))).val = 4*j.val + (if h then 2 else 0) + i.val := by
  change (halfEquiv 2 (h,i)).val + 4*j.val = _
  rw [halfEquiv_val]
  omega

abbrev SmallShape (b k : ℕ) := (Bool × Fin b) ⊕ ((Bool × Fin 3) ⊕ (Fin k × (Bool × Fin 2)))

def smallEquiv (b k : ℕ) : SmallShape b k ≃ Fin (2*b+6+4*k) :=
  ((Equiv.sumCongr (halfEquiv b)
    ((Equiv.sumCongr (halfEquiv 3) (compensationEquiv k)).trans finSumFinEquiv)).trans
      finSumFinEquiv).trans (finCongr (by omega))

@[simp] theorem smallEquiv_bulk_val (b k : ℕ) (h : Bool) (i : Fin b) :
    (smallEquiv b k (.inl (h,i))).val = (if h then b else 0)+i.val := by
  simp [smallEquiv, finSumFinEquiv]

@[simp] theorem smallEquiv_top_val (b k : ℕ) (h : Bool) (i : Fin 3) :
    (smallEquiv b k (.inr (.inl (h,i)))).val = 2*b+(if h then 3 else 0)+i.val := by
  change 2*b+(halfEquiv 3 (h,i)).val = _
  rw [halfEquiv_val]
  omega

@[simp] theorem smallEquiv_compensation_val (b k : ℕ) (j : Fin k) (h : Bool) (i : Fin 2) :
    (smallEquiv b k (.inr (.inr (j,(h,i))))).val = 2*b+6+4*j.val+(if h then 2 else 0)+i.val := by
  simp [smallEquiv, finSumFinEquiv, Nat.add_assoc]

end Ostmann.Construction.InitialCoordinatesTemplate

end

end OAI
