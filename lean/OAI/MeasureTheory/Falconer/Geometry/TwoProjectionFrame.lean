import OAI.MeasureTheory.Falconer.Geometry.TwoProjectionCubes
import OAI.MeasureTheory.Falconer.Estimates.DilationNoncharging

namespace OAI

/-! # Normalized auxiliary frame for the odd-dimensional preparation -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

structure TwoProjectionFrame {d : ℕ} (μ : ProbabilityMeasure (Space d)) (m k : ℕ) (s : ℝ) where
  first : Space d →L[ℝ] Space m
  second : Space m →L[ℝ] Space k
  first_contractive : ‖first‖ ≤ 1
  second_contractive : ‖second‖ ≤ 1
  first_root : ∀ x ∈ (μ : Measure (Space d)).support,
    first x ∈ (centeredUnitCube m).carrier
  second_root : ∀ x ∈ (μ : Measure (Space d)).support,
    (second.comp first) x ∈ (centeredUnitCube k).carrier
  noncharging : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
    ((μ : Measure (Space d)).map first) {x | inner ℝ w x = t} = 0
  constant : ℝ
  constant_pos : 0 < constant
  original_frostman : FrostmanBallBound (μ : Measure (Space d)) s constant
  first_frostman : FrostmanBallBound ((μ : Measure (Space d)).map first) s constant
  second_frostman : FrostmanBallBound ((μ : Measure (Space d)).map (second.comp first)) s constant

variable {d m k : ℕ}

private theorem enlarge_frostman {μ : Measure (Space d)} {s C D : ℝ}
    (h : FrostmanBallBound μ s C) (hCD : C ≤ D) : FrostmanBallBound μ s D := by
  intro x r hr
  exact (h x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hr.le _)))

theorem normalize_two_projected_laws (μ : ProbabilityMeasure (Space d))
    (hK : IsCompact (μ : Measure (Space d)).support)
    (P : Space d →L[ℝ] Space m) (Q : Space m →L[ℝ] Space k)
    {s C : ℝ} (hC : 0 < C)
    (hμ : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hP : FrostmanBallBound ((μ : Measure (Space d)).map P) s C)
    (hQ : FrostmanBallBound ((μ : Measure (Space d)).map (Q.comp P)) s C)
    (hnull : ∀ w : Space m, ‖w‖ = 1 → ∀ t : ℝ,
      ((μ : Measure (Space d)).map P) {y | inner ℝ w y = t} = 0) :
    Nonempty (TwoProjectionFrame μ m k s) := by
  obtain ⟨a,b,ha,hb,hPa,hQb,hroot,hroot'⟩ :=
    two_projections_into_unitCubes (μ : Measure (Space d)).support hK P Q
  let C' := max C (max (C*a^(-s)) (C*(a*b)^(-s)))
  have h0 : C ≤ C' := le_max_left _ _
  have h1 : C*a^(-s) ≤ C' := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : C*(a*b)^(-s) ≤ C' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨{
    first := a • P
    second := b • Q
    first_contractive := hPa
    second_contractive := hQb
    first_root := hroot
    second_root := hroot'
    noncharging := dilated_projection_hyperplane_null (μ : Measure (Space d)) P ha hnull
    constant := C'
    constant_pos := hC.trans_le h0
    original_frostman := enlarge_frostman hμ h0
    first_frostman := enlarge_frostman (dilated_projected_frostman _ P ha hP) h1
    second_frostman := ?_ }⟩
  rw [scaled_composite]
  exact enlarge_frostman (dilated_projected_frostman _ (Q.comp P) (mul_pos ha hb) hQ) h2

end Falconer

end OAI
