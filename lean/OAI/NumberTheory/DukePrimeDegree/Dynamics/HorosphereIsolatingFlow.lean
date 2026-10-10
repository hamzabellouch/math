import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereDiagonal

namespace OAI

/-!
# Isolating a peripheral root of the shearing horosphere

Each noncentral row or column coordinate can be left unchanged by a
trace-zero diagonal flow which contracts all other horospherical
coordinates. The resulting conjugates converge to that single root.
-/

noncomputable section
open Matrix Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def centerWeights (d : ℕ) (w : Fin (d + 1) → ℝ) (r : Fin (d + 1)) : ℝ :=
  w r - (∑ s, w s) / (d + 1 : ℝ)

lemma centerWeights_sum (d : ℕ) (w : Fin (d + 1) → ℝ) :
    ∑ r, centerWeights d w r = 0 := by
  simp only [centerWeights, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma centerWeights_sub (d : ℕ) (w : Fin (d + 1) → ℝ) (r s : Fin (d + 1)) :
    centerWeights d w r - centerWeights d w s = w r - w s := by
  unfold centerWeights
  ring

def rowIsolatingRaw {n : ℕ} (i j k : Fin n) (r : Fin n) : ℝ :=
  if r = j then 1 else if r = i ∨ r = k then -1 else 0

def columnIsolatingRaw {n : ℕ} (i j k : Fin n) (r : Fin n) : ℝ :=
  if r = i then -1 else if r = j ∨ r = k then 1 else 0

lemma rowIsolatingRaw_equal {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hkj : k ≠ j) : rowIsolatingRaw i j k i = rowIsolatingRaw i j k k := by
  simp [rowIsolatingRaw, hij, hkj]

lemma columnIsolatingRaw_equal {n : ℕ} {i j k : Fin n}
    (hji : j ≠ i) (hki : k ≠ i) : columnIsolatingRaw i j k k = columnIsolatingRaw i j k j := by
  simp [columnIsolatingRaw, hji, hki]

lemma rowIsolatingRaw_negative {n : ℕ} {i j k r s : Fin n}
    (hij : i ≠ j) (hkj : k ≠ j)
    (hrs : r ≠ s) (hshape : r = i ∨ s = j) (hne : ¬ (r = i ∧ s = k)) :
    rowIsolatingRaw i j k r - rowIsolatingRaw i j k s < 0 := by
  rcases hshape with hri | hsj
  · subst r
    have hsi : s ≠ i := Ne.symm hrs
    have hsk : s ≠ k := fun h => hne ⟨rfl, h⟩
    by_cases hsj : s = j
    · subst s; simp [rowIsolatingRaw, hij]
    · simp [rowIsolatingRaw, hij, hsj, hsi, hsk]
  · subst s
    have hrj : r ≠ j := hrs
    by_cases hri : r = i <;> by_cases hrk : r = k <;>
      simp [rowIsolatingRaw, hij, hkj, hrj, hri, hrk]

lemma columnIsolatingRaw_negative {n : ℕ} {i j k r s : Fin n}
    (hij : i ≠ j) (hki : k ≠ i)
    (hrs : r ≠ s) (hshape : r = i ∨ s = j) (hne : ¬ (r = k ∧ s = j)) :
    columnIsolatingRaw i j k r - columnIsolatingRaw i j k s < 0 := by
  rcases hshape with hri | hsj
  · subst r
    have hsi : s ≠ i := Ne.symm hrs
    by_cases hsj : s = j <;> by_cases hsk : s = k <;>
      simp [columnIsolatingRaw, hij.symm, hki, hsi, hsj, hsk]
  · subst s
    have hrj : r ≠ j := hrs
    have hrk : r ≠ k := fun h => hne ⟨h, rfl⟩
    by_cases hri : r = i
    · subst r; simp [columnIsolatingRaw, hij.symm]
    · simp [columnIsolatingRaw, hij.symm, hri, hrj, hrk]

end DukePrimeDegree

end

end OAI
