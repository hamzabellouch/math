import OAI.NumberTheory.CubicMoment.Estimates.CellGeometry
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

namespace OAI

/-! The actual disjoint log-norm partition used in the integrated bilinear
estimate. Its finite fibers preserve both the sum and coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def logNormCell (J A : ℝ) (a : Eisenstein) : ℤ :=
  ⌊J*Real.log (norm a/A)⌋

def logNormCellSupport (S : Finset Eisenstein) (J A : ℝ) (i : ℤ) : Finset Eisenstein :=
  S.filter (fun a => logNormCell J A a = i)

lemma logNormCell_bounds (J A : ℝ) (a : Eisenstein) :
    (logNormCell J A a : ℝ) ≤ J*Real.log (norm a/A) ∧
    J*Real.log (norm a/A) < (logNormCell J A a : ℝ)+1 :=
  ⟨Int.floor_le _,Int.lt_floor_add_one _⟩

lemma logNormCell_mem_range {S : Finset Eisenstein} {J A R : ℝ}
    (hS : ∀ a ∈ S, 0 ≤ J*Real.log (norm a/A) ∧ J*Real.log (norm a/A) ≤ R)
    {a : Eisenstein} (ha : a ∈ S) :
    logNormCell J A a ∈ Finset.Icc 0 ⌊R⌋ := by
  apply Finset.mem_Icc.mpr
  exact ⟨Int.floor_nonneg.mpr (hS a ha).1,Int.floor_mono (hS a ha).2⟩

lemma logNormCell_count {S : Finset Eisenstein} {J A R : ℝ}
    (hS : ∀ a ∈ S, 0 ≤ J*Real.log (norm a/A) ∧ J*Real.log (norm a/A) ≤ R) :
    (S.image (logNormCell J A)).card ≤ (⌊R⌋+1).toNat := by
  have h := Finset.card_le_card (show S.image (logNormCell J A) ⊆ Finset.Icc 0 ⌊R⌋ by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    exact logNormCell_mem_range hS ha)
  simpa only [Int.card_Icc,sub_zero] using h

lemma sum_logNormCells {M : Type*} [AddCommMonoid M]
    (S : Finset Eisenstein) (J A : ℝ) (f : Eisenstein → M) :
    (∑ i ∈ S.image (logNormCell J A), ∑ a ∈ logNormCellSupport S J A i, f a) =
      ∑ a ∈ S, f a := by
  exact Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) f

lemma logNormCell_energy (S : Finset Eisenstein) (J A : ℝ) (α : Eisenstein → ℂ) :
    (∑ i ∈ S.image (logNormCell J A),
      (Real.sqrt (∑ a ∈ logNormCellSupport S J A i, ‖α a‖^2))^2) =
      ∑ a ∈ S, ‖α a‖^2 := by
  simp_rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact sum_logNormCells S J A (fun a => ‖α a‖^2)

lemma logNormCell_bilinear_partition (P S : Finset Eisenstein)
    (J A B : ℝ) (f : Eisenstein → Eisenstein → ℂ) :
    (∑ a ∈ P, ∑ b ∈ S, f a b) =
      ∑ i ∈ P.image (logNormCell J A), ∑ j ∈ S.image (logNormCell J B),
        ∑ a ∈ logNormCellSupport P J A i, ∑ b ∈ logNormCellSupport S J B j, f a b := by
  rw [←sum_logNormCells P J A (fun a => ∑ b ∈ S, f a b)]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑ a ∈ logNormCellSupport P J A i,
        ∑ j ∈ S.image (logNormCell J B), ∑ b ∈ logNormCellSupport S J B j, f a b := by
      exact Finset.sum_congr rfl (fun a _ => (sum_logNormCells S J B (f a)).symm)
    _ = _ := Finset.sum_comm

end CubicFirstMoment

end

end OAI
