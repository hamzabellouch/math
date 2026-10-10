import Mathlib
import OAI.Probability.SKValue.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

noncomputable def brownianCoordinates {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) (j : Fin n) : ℝ :=
  (B (((j : ℕ) + 1 : ℕ) * δ) ω - B ((j : ℕ) * δ) ω) / Real.sqrt δ

lemma brownian_grid_variance (δ : ℝ≥0) (j : ℕ) :
    nndist (↑(((j+1 : ℕ) : ℝ≥0)*δ) : ℝ) (↑((j : ℝ≥0)*δ) : ℝ) = δ := by
  apply NNReal.coe_injective
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  rw [Real.dist_eq]
  have heq : ((j : ℝ)+1)*(δ : ℝ)-(j : ℝ)*δ=δ := by ring
  rw [heq]
  exact abs_of_nonneg δ.property

lemma brownian_coordinate_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) (j : Fin n) :
    HasLaw (fun ω ↦ brownianCoordinates B δ n ω j) standardGaussian μ := by
  have h := gaussianReal_div_const (hB.hasLaw_sub (((j : ℕ)+1 : ℕ)*δ) ((j : ℕ)*δ))
    (Real.sqrt δ)
  erw [brownian_grid_variance δ (j : ℕ)] at h
  have hs : (⟨(Real.sqrt δ)^2, sq_nonneg _⟩ : ℝ≥0) = δ := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt δ.property
  have heq : NNReal.mk ((Real.sqrt (δ : ℝ))^2) (sq_nonneg _) = δ := hs
  rw [heq, div_self (ne_of_gt hδ)] at h
  simpa only [brownianCoordinates, standardGaussian, zero_div, Pi.sub_apply] using h

lemma brownian_coordinates_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (δ : ℝ≥0) (n : ℕ) :
    iIndepFun (fun j (ω : Ω) ↦ brownianCoordinates B δ n ω j) μ := by
  have hmono : Monotone (fun j : Fin (n+1) ↦ (j : ℕ)*δ) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have h := (hB.hasIndepIncrements n (fun j : Fin (n+1) ↦ (j : ℕ)*δ) hmono).comp
    (fun (_ : Fin n) (x : ℝ) ↦ x / Real.sqrt δ) (fun _ ↦ measurable_id.div_const _)
  simpa only [brownianCoordinates, Fin.val_succ, Fin.val_castSucc, Function.comp_def] using h

lemma brownian_coordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) :
    HasLaw (brownianCoordinates B δ n) (gaussianProduct (Fin n)) μ := by
  exact iIndepFun.hasLaw_pi (fun j ↦ brownian_coordinate_hasLaw hB hδ n j)
    (brownian_coordinates_independent hB δ n)

lemma brownian_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {δ : ℝ≥0}
    (hδ : 0 < δ) (n : ℕ) (ω : Ω) (j : Fin n) :
    Real.sqrt δ * brownianCoordinates B δ n ω j =
      B (((j : ℕ)+1 : ℕ)*δ) ω-B ((j : ℕ)*δ) ω := by
  have hs : Real.sqrt (δ : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ)
  simp only [brownianCoordinates]
  field_simp

end SKValue

end

end OAI
