import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLongBoxes
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootRestrictions

namespace OAI

/-!
# Exhausting upper-root time by compactly contained cubes

The ordered real root coordinates give explicit increasing open cubes,
compact closed cubes, and countable families of long quotient boxes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance specialLinear_secondCountable (n : ℕ) : SecondCountableTopology (G n) := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance upperRootTransverse_secondCountable (n : ℕ) :
    SecondCountableTopology (UpperRootTransverse n) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def cube : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → ℝ → Set c.Time
  | _, _, .done, _ => univ
  | _, _, .step _ _ _ _ _ tail, R => tail.cube R ×ˢ Ioo (-R) R

def closedCube : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → ℝ → Set c.Time
  | _, _, .done, _ => univ
  | _, _, .step _ _ _ _ _ tail, R => tail.closedCube R ×ˢ Icc (-R) R

lemma cube_open (c : EliminationChain P D) (R : ℝ) : IsOpen (c.cube R) := by
  induction c with
  | done => exact isOpen_univ
  | step a b hab hP hb tail ih => exact ih.prod isOpen_Ioo

lemma closedCube_compact (c : EliminationChain P D) (R : ℝ) : IsCompact (c.closedCube R) := by
  induction c with
  | done => exact (isCompact_univ : IsCompact (Set.univ : Set PUnit))
  | step a b hab hP hb tail ih => exact ih.prod isCompact_Icc

lemma cube_subset_closedCube (c : EliminationChain P D) (R : ℝ) :
    c.cube R ⊆ c.closedCube R := by
  induction c with
  | done => exact subset_rfl
  | step a b hab hP hb tail ih => exact Set.prod_mono ih Ioo_subset_Icc_self

lemma cube_mono (c : EliminationChain P D) : Monotone c.cube := by
  intro R S hRS
  induction c with
  | done => exact subset_rfl
  | step a b hab hP hb tail ih =>
      exact Set.prod_mono ih (Ioo_subset_Ioo (neg_le_neg hRS) hRS)

lemma mem_cube_exists (c : EliminationChain P D) (R : ℝ) (t : c.Time) :
    ∃ m : ℕ, t ∈ c.cube (R + m) := by
  induction c with
  | done => exact ⟨0, mem_univ _⟩
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      obtain ⟨m, hm⟩ := ih t.1
      obtain ⟨k, hk⟩ := exists_nat_gt (|t.2| + |R|)
      refine ⟨max m k, ?_, ?_, ?_⟩
      · exact tail.cube_mono (by have h : (m : ℝ) ≤ max m k := Nat.cast_le.mpr (le_max_left _ _); linarith) hm
      · have h₁ := neg_abs_le t.2
        have h₂ := neg_abs_le R
        have h₃ : (k : ℝ) ≤ max m k := Nat.cast_le.mpr (le_max_right _ _)
        linarith
      · have h₁ := le_abs_self t.2
        have h₂ := neg_abs_le R
        have h₃ : (k : ℝ) ≤ max m k := Nat.cast_le.mpr (le_max_right _ _)
        linarith

lemma cubes_cover (c : EliminationChain P D) (R : ℝ) :
    ⋃ m : ℕ, c.cube (R + m) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact mem_iUnion.mpr (c.mem_cube_exists R t)

end EliminationChain

def upperRootWindow (n : ℕ) (R : ℝ) (m : ℕ) : Set (UpperRootTime n) :=
  (completeRootChain n).cube (R + m)

lemma upperRootWindow_open (n : ℕ) (R : ℝ) (m : ℕ) :
    IsOpen (upperRootWindow n R m) := (completeRootChain n).cube_open _

lemma upperRootWindow_mono (n : ℕ) (R : ℝ) : Monotone (upperRootWindow n R) := by
  intro a b hab
  apply (completeRootChain n).cube_mono
  have h : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  linarith

lemma upperRootWindow_cover (n : ℕ) (R : ℝ) : ⋃ m, upperRootWindow n R m = univ :=
  (completeRootChain n).cubes_cover R

lemma exists_countable_upperRootBoxes_exact_time (n : ℕ) (g : G n) (R : ℝ) :
    ∃ C : Set (UpperRootBox n g), C.Countable ∧
      (∀ B ∈ C, B.time = (completeRootChain n).cube R) ∧
      ∀ s : UpperRootTransverse n,
        Function.Injective (fun t => upperRootQuotientParam n g (s, t)) →
        ∃ B ∈ C, s ∈ B.transverse := by
  let Good := {B : UpperRootBox n g | B.time = (completeRootChain n).cube R}
  obtain ⟨C, hCG, hCc, hC⟩ := isOpen_biUnion_countable Good
    (fun B : UpperRootBox n g => B.transverse) (fun B _ => B.transverse_open)
  refine ⟨C, hCc, fun B hB => hCG hB, ?_⟩
  intro s hs
  obtain ⟨B, hsB, hT⟩ := upperRootBox_contains_compact_time n g s hs
    ((completeRootChain n).closedCube R) ((completeRootChain n).closedCube_compact R)
  let E := B.shrink B.transverse ((completeRootChain n).cube R) B.transverse_open
    ((completeRootChain n).cube_open R) subset_rfl
    (((completeRootChain n).cube_subset_closedCube R).trans hT)
  have hE : E ∈ Good := rfl
  have H : s ∈ ⋃ B ∈ Good, B.transverse := mem_iUnion.mpr ⟨E, mem_iUnion.mpr ⟨hE, hsB⟩⟩
  rw [←hC] at H
  simpa only [mem_iUnion, exists_prop] using H

def upperRootLongBoxFamily (n : ℕ) (g : G n) (R : ℝ) (m : ℕ) : Set (UpperRootBox n g) :=
  (exists_countable_upperRootBoxes_exact_time n g (R + m)).choose

lemma upperRootLongBoxFamily_countable (n : ℕ) (g : G n) (R : ℝ) (m : ℕ) :
    (upperRootLongBoxFamily n g R m).Countable :=
  (exists_countable_upperRootBoxes_exact_time n g (R + m)).choose_spec.1

lemma upperRootLongBoxFamily_time (n : ℕ) (g : G n) (R : ℝ) (m : ℕ)
    (B : UpperRootBox n g) (hB : B ∈ upperRootLongBoxFamily n g R m) :
    B.time = upperRootWindow n R m :=
  (exists_countable_upperRootBoxes_exact_time n g (R + m)).choose_spec.2.1 B hB

lemma upperRootLongBoxFamily_covers (n : ℕ) (g : G n) (R : ℝ) (m : ℕ)
    (s : UpperRootTransverse n)
    (hs : Function.Injective (fun t => upperRootQuotientParam n g (s, t))) :
    ∃ B ∈ upperRootLongBoxFamily n g R m, s ∈ B.transverse :=
  (exists_countable_upperRootBoxes_exact_time n g (R + m)).choose_spec.2.2 s hs

end DukePrimeDegree

end

end OAI
