import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter _root_.OAI.PlanarFalconer
open scoped ContDiff Classical
open GraphLiteralSupport.CurrentFalconer.TreeND
variable {d : ℕ}

lemma literal_dyadicPaths (n : ℕ) :
    GraphLiteralSupport.CurrentFalconer.TreeND.dyadicPaths (d:=d) n = dyadicPaths n := by
  ext p
  simp only [GraphLiteralSupport.CurrentFalconer.TreeND.mem_dyadicPaths,mem_dyadicPaths]

lemma literal_pathIndex (p : CellPath d) :
    GraphLiteralSupport.CurrentFalconer.TreeND.pathIndex p = pathIndex p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    funext i
    simp only [GraphLiteralSupport.CurrentFalconer.TreeND.pathIndex,pathIndex,ih]

lemma literal_treeCell (p : CellPath d) :
    GraphLiteralSupport.CurrentFalconer.TreeND.treeCell p = treeCell p := by
  simp only [GraphLiteralSupport.CurrentFalconer.TreeND.treeCell,treeCell,literal_pathIndex]
  rfl

lemma literal_treeCenter (p : CellPath d) :
    GraphLiteralSupport.CurrentFalconer.TreeND.treeCenter p = treeCenter p := by
  simp only [GraphLiteralSupport.CurrentFalconer.TreeND.treeCenter,treeCenter,literal_pathIndex]
  rfl

lemma literal_fullParallelCount (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    GraphLiteralSupport.CurrentFalconer.TreeND.fullParallelCount ρ g p P W w =
      fullParallelCount ρ g p P W w := by
  simp only [GraphLiteralSupport.CurrentFalconer.TreeND.fullParallelCount,fullParallelCount,
    literal_dyadicPaths,literal_treeCell,literal_treeCenter]
  rfl

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter _root_.OAI.PlanarFalconer
open scoped ContDiff Classical
variable {d : ℕ}

lemma literal_occupiedCenterCells (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (p : ℕ) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    GraphLiteralSupport.CurrentFalconer.TreeND.occupiedCenterCells ρ p x r =
      occupiedCenterCells ρ p x r := by
  simp only [GraphLiteralSupport.CurrentFalconer.TreeND.occupiedCenterCells,
    occupiedCenterCells,literal_dyadicPaths,literal_treeCell,literal_treeCenter]

lemma literal_regularizedProfileData_iff
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (N B : ℕ) (s sig : ℝ) (m : ℝ → ℝ) :
    GraphLiteralSupport.CurrentFalconer.TreeND.RegularizedProfileData ρ N B s sig m ↔
      RegularizedProfileData ρ N B s sig m := by
  constructor
  · intro h
    refine ⟨h.probability,h.continuous,h.zero,h.slope,h.affine,?_,h.envelope,h.adjusted,?_⟩
    · simpa only [literal_treeCell] using h.cells
    · simpa only [literal_occupiedCenterCells] using h.packing
  · intro h
    refine ⟨h.probability,h.continuous,h.zero,h.slope,h.affine,?_,h.envelope,h.adjusted,?_⟩
    · simpa only [literal_treeCell] using h.cells
    · simpa only [literal_occupiedCenterCells] using h.packing

end CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace CurrentFalconer
open Set MeasureTheory Metric
open scoped ContDiff

lemma graph_fixed_radial_budget {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hcompact : HasCompactSupport Ψ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ (∫ u : ℝ, ‖(Ψ u:ℂ)‖) ≤ K ∧
      ∀ j ≤ M, ∀ u, ‖iteratedDeriv j (fun u => (Ψ u:ℂ)) u‖ ≤ K := by
  have hcomp : HasCompactSupport (fun u => (Ψ u:ℂ)) := by
    apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro u hu
    simpa only [Function.mem_support,Complex.ofReal_ne_zero] using hu
  have hcd : ContDiff ℝ ∞ (fun u => (Ψ u:ℂ)) := Complex.ofRealCLM.contDiff.comp hΨ
  have hb (j : ℕ) : ∃ C : ℝ, ∀ u, ‖iteratedDeriv j (fun u => (Ψ u:ℂ)) u‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hcomp.iteratedFDeriv j).exists_bound_of_continuous
      (hcd.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)))
    exact ⟨C,fun u => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC u⟩
  choose C hC using hb
  let D := ∑ j ∈ Finset.range (M+1), max 0 (C j)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => le_max_left _ _)
  have hI : 0 ≤ ∫ u : ℝ, ‖(Ψ u:ℂ)‖ := integral_nonneg (fun u => norm_nonneg _)
  refine ⟨D+(∫ u : ℝ, ‖(Ψ u:ℂ)‖),add_nonneg hD hI,le_add_of_nonneg_left hD,?_⟩
  intro j hj u
  apply (hC j u).trans
  apply (le_max_right 0 (C j)).trans
  exact (Finset.single_le_sum (fun k _ => le_max_left 0 (C k))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans (le_add_of_nonneg_right hI)

end CurrentFalconer
end
end

end OAI
