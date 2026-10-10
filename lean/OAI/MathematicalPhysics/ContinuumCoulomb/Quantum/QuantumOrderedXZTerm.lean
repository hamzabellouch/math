import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZTerms

namespace OAI

/-! Deterministic X/Z term classification from a list of at most two sites.
The order of pair endpoints is the supplied order, with no finite-set choice. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZTerm
open scoped Classical

def axis (a : Fin 4) : Fin 2 := if a = 1 then 0 else 1

theorem axis_spec (a : Fin 4) (h0 : a ≠ 0) (h2 : a ≠ 2) :
    qmaXZLabel (axis a) = a := by
  fin_cases a <;> simp_all [axis,qmaXZLabel]

def field {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) : QMAXZTerm n :=
  if w i = 0 then .scalar else .field i (axis (w i))

def ofSites {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4) : QMAXZTerm n :=
  match xs with
  | [] => .scalar
  | [i] => field w i
  | i :: j :: _ =>
      if h : i = j then field w i
      else if w i = 0 then field w j
      else if w j = 0 then field w i
      else .pair i j h (axis (w i)) (axis (w j))

private theorem outside {n : ℕ} (w : Fin n → Fin 4) (xs : List (Fin n))
    (hs : qmaPauliSupport w ⊆ xs.toFinset) (i : Fin n) (hi : i ∉ xs) : w i = 0 := by
  by_contra h
  have hm := hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact hi (List.mem_toFinset.mp hm)

theorem field_word {n : ℕ} (w : Fin n → Fin 4) (i k : Fin n)
    (hy : w i ≠ 2) : (field w i).word k = if k = i then w i else 0 := by
  by_cases hz : w i = 0
  · simp [field,hz,QMAXZTerm.word]
  · simp only [field,hz,ite_false,QMAXZTerm.word,axis_spec _ hz hy]

theorem word_eq {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4)
    (hlen : xs.length ≤ 2) (hx : xs.Nodup)
    (hs : qmaPauliSupport w ⊆ xs.toFinset) (hy : ∀ i, w i ≠ 2) :
    (ofSites xs w).word = w := by
  cases xs with
  | nil =>
    funext k
    exact (outside w [] hs k (by simp)).symm
  | cons i xs =>
    cases xs with
    | nil =>
      funext k
      rw [ofSites,field_word w i k (hy i)]
      by_cases hk : k = i
      · simp [hk]
      · simpa [hk] using (outside w [i] hs k (by simp [hk])).symm
    | cons j xs =>
      cases xs with
      | cons l xs => simp at hlen
      | nil =>
        have hij : i ≠ j := by simpa using hx
        rw [ofSites,dite_eq_right hij]
        split_ifs with hi hj
        · funext k
          rw [field_word w j k (hy j)]
          by_cases hkj : k = j
          · simp [hkj]
          · by_cases hki : k = i
            · simp [hki,hi,hij]
            · simpa [hkj] using (outside w [i,j] hs k (by simp [hki,hkj])).symm
        · funext k
          rw [field_word w i k (hy i)]
          by_cases hki : k = i
          · simp [hki]
          · by_cases hkj : k = j
            · simp [hkj,hj,Ne.symm hij]
            · simpa [hki] using (outside w [i,j] hs k (by simp [hki,hkj])).symm
        · funext k
          simp only [QMAXZTerm.word,axis_spec _ hi (hy i),axis_spec _ hj (hy j)]
          by_cases hki : k = i
          · simp [hki]
          · by_cases hkj : k = j
            · simp [hkj,Ne.symm hij]
            · simpa [hki,hkj] using (outside w [i,j] hs k (by simp [hki,hkj])).symm

theorem matrix_eq {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4)
    (hlen : xs.length ≤ 2) (hx : xs.Nodup)
    (hs : qmaPauliSupport w ⊆ xs.toFinset) (hy : ∀ i, w i ≠ 2) :
    (ofSites xs w).matrix = qmaPauliWord w := by
  rw [← QMAXZTerm.word_matrix,word_eq xs w hlen hx hs hy]

end ContinuumCoulomb.QuantumOrderedXZTerm

end

end OAI
