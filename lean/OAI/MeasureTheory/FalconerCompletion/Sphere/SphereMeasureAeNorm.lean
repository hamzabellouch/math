import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.TestedCellFamily

namespace OAI

/-! Canonical spherical measures and differential identities. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Attempt4FullFar
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma canonicalSphereMeasureND_ae_norm :
    ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)), ‖w‖=1 := by
  unfold canonicalSphereMeasureND
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).2
  exact Filter.Eventually.of_forall fun w => by simp

noncomputable def cellCapEnergy (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (P : CellPath d) (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ) : ℝ :=
  ∫ x in treeCell P, ∫ w, η w * ‖b x w‖^2
    ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin d)) ∂ρ

def ImposesParallelTest (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (W K : ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  ∀ P ∈ dyadicPaths p, ∀ x ∈ treeCell P, ∀ w : EuclideanSpace ℝ (Fin d),
    ‖w‖=1 → b x w ≠ 0 → (fullParallelCount ρ g p P W w : ℝ) ≤ K

noncomputable def eligibleCells (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (a p : ℕ) (X : CellPath d) (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ) : Finset (CellPath d) :=
  (dyadicPaths p).filter fun P => P.take a=X ∧ 0 < cellCapEnergy ρ P η b

lemma cellCapEnergy_pos_witness (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (P : CellPath d) (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (h : 0 < cellCapEnergy ρ P η b) :
    ∃ x ∈ treeCell P, ∃ w : EuclideanSpace ℝ (Fin d),
      ‖w‖=1 ∧ η w ≠ 0 ∧ b x w ≠ 0 := by
  obtain ⟨x,hx,hne⟩ := exists_ne_zero_of_setIntegral_ne_zero (ne_of_gt h)
  refine ⟨x,hx,?_⟩
  by_contra! habs
  apply hne
  apply integral_eq_zero_of_ae
  filter_upwards [canonicalSphereMeasureND_ae_norm (d:=d)] with w hw
  by_cases hη : η w=0
  · simp [hη]
  · simp [habs w hw hη]

lemma cellCapEnergy_pos_occupied (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (P : CellPath d) (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (h : 0 < cellCapEnergy ρ P η b) : 0 < ρ (treeCell P) := by
  by_contra hnot
  have he : ρ (treeCell P)=0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hr : ρ.restrict (treeCell P)=0 := Measure.restrict_eq_zero.mpr he
  simp [cellCapEnergy,hr] at h

theorem eligibleCells_tested (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (a g p : ℕ) (X : CellPath d) (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ)
    (v : EuclideanSpace ℝ (Fin d)) (δ W K : ℝ)
    (hcap : ∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → η w ≠ 0 → dist v w ≤ δ)
    (htest : ImposesParallelTest ρ g p W K b) :
    TestedCellFamily ρ a g p X (eligibleCells ρ a p X η b) v δ W K := by
  classical
  refine ⟨Finset.filter_subset _ _,?_⟩
  intro P hP
  obtain ⟨hdepth,hparent,henergy⟩ := Finset.mem_filter.mp hP
  obtain ⟨x,hx,w,hw,hη,hb⟩ := cellCapEnergy_pos_witness ρ P η b henergy
  exact ⟨hparent,cellCapEnergy_pos_occupied ρ P η b henergy,w,hw,
    hcap w hw hη,htest P hdepth x hx w hw hb⟩

end CurrentFalconer.TreeND
end
end

end OAI
