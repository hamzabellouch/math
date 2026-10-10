import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.FastLookup

namespace OAI

noncomputable section

namespace Foulkes.Enumeration
open Finset

def compositions : (n d : ℕ) → List (Fin n → ℕ)
  | 0, d => if d = 0 then [Fin.elim0] else []
  | n+1, d => (List.range (d+1)).flatMap fun k =>
      (compositions n (d-k)).map (Fin.cons k)

lemma mem_compositions (n d : ℕ) (v : Fin n → ℕ) :
    v ∈ compositions n d ↔ ∑ j, v j = d := by
  induction n generalizing d with
  | zero =>
    have hv : v = Fin.elim0 := by funext j; exact Fin.elim0 j
    subst v
    by_cases hd : d = 0
    · simp [compositions, hd]
    · simp [compositions, hd, Ne.symm hd]
  | succ n ih =>
    rw [compositions, List.mem_flatMap]
    constructor
    · rintro ⟨k,hk,hv⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
      have hw' := (ih (d-k) w).mp hw
      have hk' : k ≤ d := by simpa using List.mem_range.mp hk
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      omega
    · intro hv
      refine ⟨v 0, List.mem_range.mpr ?_, List.mem_map.mpr ⟨Fin.tail v, ?_, ?_⟩⟩
      · rw [Fin.sum_univ_succ] at hv
        omega
      · apply (ih (d-v 0) (Fin.tail v)).mpr
        rw [Fin.sum_univ_succ] at hv
        dsimp [Fin.tail]
        omega
      · exact Fin.cons_self_tail v

lemma nodup_compositions (n d : ℕ) : (compositions n d).Nodup := by
  induction n generalizing d with
  | zero => unfold compositions; split_ifs <;> simp
  | succ n ih =>
    rw [compositions, List.nodup_flatMap]
    refine ⟨fun k hk => (ih _).map ?_, (List.nodup_range (n := d+1)).imp ?_⟩
    · intro v w h
      funext j
      exact congrFun h j.succ
    · intro x y hxy v hx hy
      obtain ⟨vx,hvx,hex⟩ := List.mem_map.mp hx
      obtain ⟨vy,hvy,hey⟩ := List.mem_map.mp hy
      have hh := congrFun (hex.trans hey.symm) 0
      exact hxy hh

def compositionSet (n d : ℕ) : Finset (Fin n → ℕ) := (compositions n d).toFinset

@[simp] lemma mem_compositionSet (n d : ℕ) (v : Fin n → ℕ) :
    v ∈ compositionSet n d ↔ ∑ j, v j = d := by
  simp [compositionSet, mem_compositions]

def degreeComposition (n d : ℕ) : Foulkes.Complete.Degree (Fin n) d ≃
    {v : Fin n → ℕ // v ∈ compositionSet n d} where
  toFun a := ⟨fun j => a.val j, (mem_compositionSet n d _).mpr (by
    rw [← Finsupp.degree_eq_sum]; exact a.property)⟩
  invFun v := ⟨Foulkes.Strips.expVector v.val, by
    rw [Foulkes.Lookup.degree_expVector]
    exact (mem_compositionSet n d _).mp v.property⟩
  left_inv a := by apply Subtype.ext; ext j; rfl
  right_inv v := rfl

end Foulkes.Enumeration

end

end OAI
