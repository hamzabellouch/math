import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootCoordinates

namespace OAI

/-! # Simultaneous holonomy for the full Gaussian root induction

One common null set controls every lexicographic elimination step. At
each step the remaining subgroup is normal and the selected root leaf
is constant along its cosets, with the exact root displacement retained.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def InitialRootStep (n : ℕ) :=
  {z : Finset (Fin n × Fin n) × (Fin n × Fin n) //
    InitialRootPattern z.1 ∧ z.2 ∈ allPositiveRoots n \ z.1 ∧
      ∀ q ∈ allPositiveRoots n \ z.1, toLex z.2 ≤ toLex q}

namespace InitialRootStep
variable {n : ℕ}

def processed (s : InitialRootStep n) : Finset (Fin n × Fin n) := s.val.1
def root (s : InitialRootStep n) : Fin n × Fin n := s.val.2
def remaining (s : InitialRootStep n) : Finset (Fin n × Fin n) := allPositiveRoots n \ s.processed

lemma initial (s : InitialRootStep n) : InitialRootPattern s.processed := s.prop.1
lemma mem_remaining (s : InitialRootStep n) : s.root ∈ s.remaining := s.prop.2.1
lemma least (s : InitialRootStep n) : ∀ q ∈ s.remaining, toLex s.root ≤ toLex q := s.prop.2.2
lemma positive (s : InitialRootStep n) : s.root.1 < s.root.2 :=
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp s.mem_remaining).1).2
lemma distinct (s : InitialRootStep n) : s.root.1 ≠ s.root.2 := ne_of_lt s.positive
lemma remaining_positive (s : InitialRootStep n) : ∀ q ∈ s.remaining, q.1 < q.2 :=
  fun _ hq => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
lemma remaining_closed (s : InitialRootStep n) :
    ∀ a b c : Fin n, (a,b) ∈ s.remaining → (b,c) ∈ s.remaining → (a,c) ∈ s.remaining :=
  initialRemaining_roots_closed s.processed s.initial

theorem next_normal (d : ℕ) (s : InitialRootStep (d + 1)) :
    ((positiveRootGeneratedGroup (s.remaining.erase s.root)).comap
      (positiveRootGeneratedGroup s.remaining).subtype).Normal := by
  obtain ⟨ell,hell,hneut,hdecay⟩ := exists_lexicographic_root_weights d s.remaining
    s.positive s.remaining_positive s.least
  exact remaining_roots_normal d s.remaining s.remaining_positive s.remaining_closed
    s.distinct ell hell hneut hdecay

theorem exists_nullset_holonomy (d : ℕ) (s : InitialRootStep (d + 1))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (w₁ w₂ : positiveRootGeneratedGroup (s.remaining.erase s.root))
        (t₁ t₂ : ℝ),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂) ∉ N →
        intrinsicRootLeaf s.distinct μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂)) =
          basedRealMeasure (intrinsicRootLeaf s.distinct μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁))) (t₂-t₁) := by
  obtain ⟨ell,hell,hneut,hdecay⟩ := exists_lexicographic_root_weights d s.remaining
    s.positive s.remaining_positive s.least
  exact exists_nullset_rootFactor_holonomy d s.remaining s.remaining_positive s.remaining_closed
    s.distinct s.mem_remaining ell hell hneut hdecay μ hA

end InitialRootStep

theorem exists_nullset_all_initial_root_holonomy (d : ℕ)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (s : InitialRootStep (d + 1)) (x : X (d + 1))
        (w₁ w₂ : positiveRootGeneratedGroup (s.remaining.erase s.root)) (t₁ t₂ : ℝ),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂) ∉ N →
        intrinsicRootLeaf s.distinct μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂)) =
          basedRealMeasure (intrinsicRootLeaf s.distinct μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁))) (t₂-t₁) := by
  have : Countable (InitialRootStep (d + 1)) := inferInstanceAs
    (Countable {z : Finset (Fin (d+1) × Fin (d+1)) × (Fin (d+1) × Fin (d+1)) // _})
  choose N hNm hN0 hhol using fun s : InitialRootStep (d+1) => s.exists_nullset_holonomy d μ hA
  refine ⟨⋃ s, N s, MeasurableSet.iUnion hNm, measure_iUnion_null hN0, ?_⟩
  intro s x w₁ w₂ t₁ t₂ h₁ h₂
  exact hhol s x w₁ w₂ t₁ t₂
    (fun h => h₁ (mem_iUnion.mpr ⟨s,h⟩)) (fun h => h₂ (mem_iUnion.mpr ⟨s,h⟩))

end DukePrimeDegree

end

end OAI
