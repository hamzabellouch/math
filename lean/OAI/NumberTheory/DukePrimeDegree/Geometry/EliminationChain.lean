import OAI.NumberTheory.DukePrimeDegree.Geometry.OrderedRootElimination

namespace OAI

/-!
# Composing Gaussian root-coordinate charts

A finite sequence of compatible eliminations gives an actual open
embedding of the final transverse slice and all its real root
coordinates. Its parametrization is multiplication by the ordered
product of the elementary root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

inductive EliminationChain {n : ℕ} :
    Finset (Fin n × Fin n) → Finset (Fin n) → Type
  | done {P D} : EliminationChain P D
  | step {P D} (a b : Fin n) (hab : a ≠ b)
      (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D)
      (tail : EliminationChain (insert (a, b) P) (insert a D)) : EliminationChain P D

namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def finalEntries : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → Finset (Fin n × Fin n)
  | P, _, .done => P
  | _, _, .step _ _ _ _ _ tail => tail.finalEntries

def finalPivots : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → Finset (Fin n)
  | _, D, .done => D
  | _, _, .step _ _ _ _ _ tail => tail.finalPivots

theorem entries_subset_final (c : EliminationChain P D) : P ⊆ c.finalEntries := by
  induction c with
  | done => exact Finset.Subset.refl _
  | step a b hab hP hb tail ih =>
      exact (Finset.subset_insert _ _).trans ih

def Time : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → Type
  | _, _, .done => PUnit
  | _, _, .step _ _ _ _ _ tail => tail.Time × ℝ

instance timeTopology (c : EliminationChain P D) : TopologicalSpace c.Time := by
  induction c with
  | done => exact inferInstanceAs (TopologicalSpace PUnit)
  | step _ _ _ _ _ _ ih => exact @instTopologicalSpaceProd _ _ ih inferInstance

abbrev FinalSlice (c : EliminationChain P D) :=
  EliminationSlice c.finalEntries c.finalPivots

def param : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.FinalSlice × c.Time → EliminationSlice P D
  | _, _, .done, z => z.1
  | P, D, .step _ _ hab hP hb tail, z =>
      ((eliminationRootHomeomorph P D hab hP hb).symm
        (tail.param (z.1, z.2.1), z.2.2)).val

theorem param_isOpenEmbedding (c : EliminationChain P D) :
    Topology.IsOpenEmbedding c.param := by
  induction c with
  | done => exact (Homeomorph.prodPUnit _).isOpenEmbedding
  | @step P D a b hab hP hb tail ih =>
      exact ((eliminationRoot_isOpenEmbedding P D hab hP hb).comp
        (ih.prodMap (Topology.IsOpenEmbedding.id (X := ℝ)))).comp
          (Homeomorph.prodAssoc _ _ _).symm.isOpenEmbedding

def word : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.Time → G n
  | _, _, .done, _ => 1
  | _, _, .step _ _ hab _ _ tail, t =>
      tail.word t.1 * Matrix.SpecialLinearGroup.transvection hab t.2

theorem param_val (c : EliminationChain P D) (s : c.FinalSlice) (t : c.Time) :
    (c.param (s, t)).val = s.val * c.word t := by
  induction c with
  | done => exact (mul_one s.val).symm
  | step a b hab hP hb tail ih =>
      change tail.FinalSlice at s
      change tail.Time × ℝ at t
      change (tail.param (s, t.1)).val * Matrix.SpecialLinearGroup.transvection hab t.2 =
        s.val * (tail.word t.1 * Matrix.SpecialLinearGroup.transvection hab t.2)
      exact (congrArg (fun g : G n => g * Matrix.SpecialLinearGroup.transvection hab t.2)
        (ih s t.1)).trans (mul_assoc _ _ _)

def zeroTime : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.Time
  | _, _, .done => PUnit.unit
  | _, _, .step _ _ _ _ _ tail => (tail.zeroTime, 0)

@[simp] theorem word_zeroTime (c : EliminationChain P D) : c.word c.zeroTime = 1 := by
  induction c with
  | done => rfl
  | step a b hab hP hb tail ih =>
      change tail.word tail.zeroTime * Matrix.SpecialLinearGroup.transvection hab 0 = 1
      rw [ih, Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul]

theorem param_zeroTime (c : EliminationChain P D) (s : c.FinalSlice) :
    (c.param (s, c.zeroTime)).val = s.val := by
  rw [c.param_val, c.word_zeroTime, mul_one]

theorem word_mem_generated (c : EliminationChain P D)
    (S : Finset (Fin n × Fin n)) (hS : c.finalEntries ⊆ S) (t : c.Time) :
    c.word t ∈ positiveRootGeneratedGroup S := by
  induction c with
  | done => exact (positiveRootGeneratedGroup S).one_mem
  | step a b hab hP hb tail ih =>
      apply (positiveRootGeneratedGroup S).mul_mem
      · exact ih hS t.1
      · exact transvection_mem_positiveRootGeneratedGroup S hab
          (hS (tail.entries_subset_final (Finset.mem_insert_self _ _))) t.2

end EliminationChain
end DukePrimeDegree

end

end OAI
