import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketProgram

namespace OAI

/-! # The input-only loop through the lifted parent residue classes -/

namespace LowSpaceSubsetSum

/-- Primitive data retained before the residue loop. There is no designated
solution or selected successful residue in the runtime state. -/
structure RepresentationScheduleData (n g : ℕ) where
  input : Instance n
  signs : Finset (Fin n)
  leaves : Fin 2 → Fin 4 → RepresentationLeaf (Fin n)
  lowModuli : Fin 2 → ℕ
  firstResidues : Fin 2 → ℤ
  p0 : ℕ
  p0_positive : 0 < p0
  q : ℕ
  q_positive : 0 < q
  rho0 : Fin p0
  capacity : ℕ
  coordinates : TopCoordinates n g
  topOrder : List (Fin n)

namespace RepresentationScheduleData

variable {n g : ℕ} (D : RepresentationScheduleData n g)

def target : ℤ := (D.input.target : ℤ) -
  weight (fun i => (D.input.values i : ℤ)) D.signs

def modulus : ℤ := (D.p0 : ℤ) * D.q

theorem modulus_positive : 0 < D.modulus := by
  unfold modulus
  exact mul_pos (by exact_mod_cast D.p0_positive) (by exact_mod_cast D.q_positive)

def leftResidue (z : ℕ) : ℤ := (D.rho0.val : ℤ) + (D.p0 : ℤ) * z

def parentData (j : Fin 2) (z : ℕ) : RepresentationParentData n where
  input := D.input
  signs := D.signs
  leaves := D.leaves j
  lowModulus := D.lowModuli j
  modulus := D.modulus
  positive := D.modulus_positive
  childResidues k :=
    let base := if j = 0 then (D.rho0.val : ℤ) else D.target - D.rho0.val
    if k = 0 then D.firstResidues j else base - D.firstResidues j
  parentResidue := if j = 0 then D.leftResidue z else (D.target - D.leftResidue z) % D.modulus
  capacity := D.capacity
  maskRestriction := MaskRestriction.empty

def bucket (z : ℕ) : RepresentationBucketData n g where
  left := D.parentData 0 z
  right := D.parentData 1 z
  coordinates := D.coordinates
  topOrder := D.topOrder

/-- A counter loop, with no array of all residues. Each completed iteration
releases its parent workspace before the next iteration. -/
def scanBuckets (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) : ℕ → ℕ → Bool
  | _, 0 => false
  | z, remaining + 1 =>
    if (D.bucket z).run B families then true else scanBuckets B families (z + 1) remaining

def run (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) : Bool :=
  D.scanBuckets B families 0 D.q

theorem scanBuckets_sound (B : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (z remaining : ℕ) (hyes : D.scanBuckets B families z remaining = true) :
    ∃ k, z ≤ k ∧ k < z + remaining ∧ (D.bucket k).run B families = true := by
  induction remaining generalizing z with
  | zero => simp only [scanBuckets, Bool.false_eq_true] at hyes
  | succ remaining ih =>
    simp only [scanBuckets] at hyes
    split at hyes
    · rename_i h
      exact ⟨z, le_rfl, by omega, h⟩
    · obtain ⟨k, hk, hku, hrun⟩ := ih (z + 1) hyes
      exact ⟨k, by omega, by omega, hrun⟩

theorem scanBuckets_complete (B : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (z remaining k : ℕ) (hk : z ≤ k) (hku : k < z + remaining)
    (hyes : (D.bucket k).run B families = true) :
    D.scanBuckets B families z remaining = true := by
  induction remaining generalizing z with
  | zero => omega
  | succ remaining ih =>
    by_cases he : k = z
    · subst k
      simp only [scanBuckets, hyes, ↓reduceIte]
    · have hnext := ih (z + 1) (by omega) (by omega)
      simp only [scanBuckets]
      split
      · rfl
      · exact hnext

theorem run_complete (B : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (z : ℕ) (hz : z < D.q) (hyes : (D.bucket z).run B families = true) :
    D.run B families = true :=
  D.scanBuckets_complete B families 0 D.q z (Nat.zero_le _) (by simpa using hz) hyes

theorem run_sound (B : ℕ) (families : Fin 4 → Array (Finset (Fin g)))
    (htop : ∀ j, RepresentationUniverse.topDomain (D.leaves j) = D.coordinates.domain)
    (htl : ∀ j, Disjoint (RepresentationUniverse.topDomain (D.leaves j))
      (RepresentationUniverse.mixerDomain (D.leaves j)))
    (htb : ∀ j, Disjoint (RepresentationUniverse.topDomain (D.leaves j))
      (RepresentationUniverse.backgroundDomain (D.leaves j)))
    (hlb : ∀ j, Disjoint (RepresentationUniverse.mixerDomain (D.leaves j))
      (RepresentationUniverse.backgroundDomain (D.leaves j)))
    (hshared : RepresentationUniverse.parentDomain (D.leaves 0) ∩
      RepresentationUniverse.parentDomain (D.leaves 1) ⊆ D.coordinates.domain)
    (hsize : D.capacity + 1 + (D.capacity + 1) ≤ 2 ^ n)
    (hyes : D.run B families = true) : Solvable D.input := by
  obtain ⟨z, _, _, hz⟩ := D.scanBuckets_sound B families 0 D.q hyes
  apply (D.bucket z).sound B families rfl ?_
    (htl 0) (htb 0) (hlb 0) (htl 1) (htb 1) (hlb 1) hshared hsize hz
  intro j
  fin_cases j <;> exact htop _

end RepresentationScheduleData
end LowSpaceSubsetSum

end OAI
