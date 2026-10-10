import OAI.Geometry.TranslativeCovering.CellCounts

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5

namespace PoissonMeasureCells

open Set MeasureTheory
open scoped ENNReal

variable {Ω : Type u_1} {C : Type u_2} {I : Type u_3} [MeasurableSpace Ω] [Fintype C] [Fintype I]

structure Partition (Ω : Type u_4) (C : Type u_5) [MeasurableSpace Ω] [Fintype C] where
  cell : C → Set Ω
  measurable : ∀ c, MeasurableSet (cell c)
  disjoint : Pairwise (fun c d => Disjoint (cell c) (cell d))
  cover : (⋃ c, cell c) = univ

omit [Fintype I] in
 def Respects (P : Partition Ω C) (F : Set Ω) : Prop :=
  ∀ c, P.cell c ⊆ F ∨ Disjoint (P.cell c) F

omit [Fintype I] in
lemma respects_inter (P : Partition Ω C) {F G : Set Ω}
    (hF : Respects P F) (hG : Respects P G) : Respects P (F ∩ G) := by
  intro c
  rcases hF c with hF | hF
  · rcases hG c with hG | hG
    · exact Or.inl (Set.subset_inter hF hG)
    · exact Or.inr (hG.mono_right inter_subset_right)
  · exact Or.inr (hF.mono_right inter_subset_left)

omit [Fintype I] in
lemma mass_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ] (P : Partition Ω C)
    {F : Set Ω} (hF : MeasurableSet F) (hr : Respects P F) :
    μ.real F = ∑ c, if P.cell c ⊆ F then μ.real (P.cell c) else 0 := by
  classical
  have heq : (⋃ c, P.cell c ∩ F) = F := by
    rw [← Set.iUnion_inter, P.cover, Set.univ_inter]
  rw [← heq, measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro c _
    rw [heq]
    by_cases hc : P.cell c ⊆ F
    · rw [ite_eq_left hc, Set.inter_eq_left.mpr hc]
    · rw [ite_eq_right hc, Set.disjoint_iff_inter_eq_empty.mp ((hr c).resolve_left hc)]
      exact measureReal_empty
  · intro c d hcd
    exact (P.disjoint hcd).mono inter_subset_left inter_subset_left
  · intro c
    exact (P.measurable c).inter hF

noncomputable def Q (μ : Measure Ω) (P : Partition Ω C) (F : I → Set Ω) : ℝ :=
  CellCounts.injectiveSum (CellCounts.slotWeight (fun i c => P.cell c ⊆ F i)
    (fun c => 1 - Real.exp (- μ.real (P.cell c))))

lemma collision_error (μ : Measure Ω) [IsFiniteMeasure μ] (P : Partition Ω C)
    [LinearOrder I] (F : I → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (hr : ∀ i, Respects P (F i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ c, μ.real (P.cell c) ≤ δ) :
    0 ≤ (∏ i, μ.real (F i)) - Q μ P F ∧
    (∏ i, μ.real (F i)) - Q μ P F ≤ δ *
      ((Fintype.card I : ℝ)/2 * (∏ i, μ.real (F i)) +
        ∑ ij ∈ CellCounts.pairs I, μ.real (F ij.1 ∩ F ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, μ.real (F u)) := by
  classical
  have hmass (i : I) : (∑ c, CellCounts.slotWeight
      (fun i c => P.cell c ⊆ F i) (fun c => μ.real (P.cell c)) i c) = μ.real (F i) :=
    (mass_eq_sum μ P (hF i) (hr i)).symm
  have hinter (i j : I) : (∑ c, if P.cell c ⊆ F i ∧ P.cell c ⊆ F j
      then μ.real (P.cell c) else 0) = μ.real (F i ∩ F j) := by
    simpa only [Set.subset_inter_iff] using
      (mass_eq_sum μ P ((hF i).inter (hF j)) (respects_inter P (hr i) (hr j))).symm
  have h := CellCounts.cell_collision_error (fun i c => P.cell c ⊆ F i)
    (fun c => μ.real (P.cell c)) hδ (fun _ => measureReal_nonneg) hd
  dsimp only at h
  simpa only [hmass, hinter, Q] using h

end PoissonMeasureCells

end OAI
