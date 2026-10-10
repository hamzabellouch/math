import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPatch
import Mathlib.Data.List.GetD

namespace OAI

/-! The fixed crossing-patch lists as bounded, simple coordinate arrays. -/

namespace ContinuumCoulomb

def qmaPatchLength (e : Fin 9) : ℕ := (qmaCrossingPatchPath e).length-1

def qmaPatchPoint (e : Fin 9) (k : ℕ) : ℕ × ℕ :=
  (qmaCrossingPatchPath e).getD k (0,0)

theorem qmaPatchLength_pos (e : Fin 9) : 0 < qmaPatchLength e := by fin_cases e <;> decide

theorem qmaPatchLength_le (e : Fin 9) : qmaPatchLength e ≤ 12 := by fin_cases e <;> decide

theorem qmaPatchPoint_get (e : Fin 9) {k : ℕ} (hk : k ≤ qmaPatchLength e) :
    qmaPatchPoint e k = (qmaCrossingPatchPath e)[k]'(by have := qmaPatchLength_pos e; dsimp [qmaPatchLength] at *; omega) :=
  List.getD_eq_getElem _ _ _

@[simp] theorem qmaPatchPoint_first (e : Fin 9) :
    qmaPatchPoint e 0 = qmaCrossingPatchVertex (qmaCrossingPatchLeft e) := by fin_cases e <;> rfl

@[simp] theorem qmaPatchPoint_last (e : Fin 9) :
    qmaPatchPoint e (qmaPatchLength e) = qmaCrossingPatchVertex (qmaCrossingPatchRight e) := by fin_cases e <;> rfl

theorem qmaPatchPoint_simple (e : Fin 9) {i j : ℕ} (hi : i ≤ qmaPatchLength e) (hj : j ≤ qmaPatchLength e)
    (h : qmaPatchPoint e i = qmaPatchPoint e j) : i = j := by
  rw [qmaPatchPoint_get e hi,qmaPatchPoint_get e hj] at h
  exact (qmaCrossingPatch_simple e).getElem_inj_iff.mp h

theorem qmaPatchPoint_step (e : Fin 9) {k : ℕ} (hk : k < qmaPatchLength e) :
    Nat.dist (qmaPatchPoint e k).1 (qmaPatchPoint e (k+1)).1+
      Nat.dist (qmaPatchPoint e k).2 (qmaPatchPoint e (k+1)).2 = 1 := by
  rw [qmaPatchPoint_get e (Nat.le_of_lt hk),qmaPatchPoint_get e (by omega)]
  exact List.isChain_iff_getElem.mp (qmaCrossingPatch_chain e) k (by dsimp [qmaPatchLength] at hk; omega)

theorem qmaPatchPoint_mem (e : Fin 9) {k : ℕ} (hk : k ≤ qmaPatchLength e) :
    qmaPatchPoint e k ∈ qmaCrossingPatchPath e := by
  rw [qmaPatchPoint_get e hk]
  exact List.getElem_mem _

theorem qmaPatchPoint_interior_mem (e : Fin 9) {k : ℕ} (hk0 : 0 < k) (hk : k < qmaPatchLength e) :
    qmaPatchPoint e k ∈ ((qmaCrossingPatchPath e).drop 1).dropLast := by
  have hi : k-1 < ((qmaCrossingPatchPath e).drop 1).dropLast.length := by
    simp only [List.length_dropLast,List.length_drop]
    dsimp [qmaPatchLength] at hk
    omega
  have hm := List.getElem_mem (l := ((qmaCrossingPatchPath e).drop 1).dropLast) hi
  rw [List.getElem_dropLast,List.getElem_drop] at hm
  have he : 1+(k-1) = k := by omega
  simpa only [he,← qmaPatchPoint_get e hk.le] using hm

theorem qmaPatchPoint_avoids (e : Fin 9) {k : ℕ} (hk0 : 0 < k) (hk : k < qmaPatchLength e) (v : Fin 6) :
    qmaPatchPoint e k ≠ qmaCrossingPatchVertex v := by
  intro h
  have hm := qmaPatchPoint_interior_mem e hk0 hk
  rw [h] at hm
  exact Finset.disjoint_left.mp (qmaCrossingPatch_interior_fresh e) (List.mem_toFinset.mpr hm)
    (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)

theorem qmaPatchPoint_disjoint (e f : Fin 9) (hef : e ≠ f) {i j : ℕ}
    (hi0 : 0 < i) (hi : i < qmaPatchLength e) (hj : j ≤ qmaPatchLength f) :
    qmaPatchPoint e i ≠ qmaPatchPoint f j := by
  intro h
  have hm := qmaPatchPoint_interior_mem e hi0 hi
  rw [h] at hm
  exact Finset.disjoint_left.mp (qmaCrossingPatch_disjoint e f hef) (List.mem_toFinset.mpr hm)
    (List.mem_toFinset.mpr (qmaPatchPoint_mem f hj))

end ContinuumCoulomb

end OAI
