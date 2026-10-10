import OAI.Probability.InvariantIsing.Cavity.CavityRDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Uniform scalar resolvent bounds, including the extension at zero.
The comparison uses any alphabet point above the compressed eigenvalue. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (α x : ℝ) : ℝ :=
  x / (1 + x * (finiteR ρ eig hρ hρsum x - α))

lemma cavityScalarResolvent_denominator_pos (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 ≤ x) :
    0 < 1 + x * (finiteR ρ eig hρ hρsum x - α) := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · have hgap : 0 < finiteInverse ρ eig hρ hρsum x - α :=
      sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))
    have he : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
        x * (finiteInverse ρ eig hρ hρsum x - α) := by
      simp only [finiteR, ite_eq_left hx]
      field_simp [hx.ne']
      ring
    rw [he]
    exact mul_pos hx hgap

lemma cavityScalarResolvent_pos_eq (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    cavityScalarResolvent ρ eig hρ hρsum α x =
      (finiteInverse ρ eig hρ hρsum x - α)⁻¹ := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hden : 1 + x * (finiteR ρ eig hρ hρsum x - α) =
      x * (finiteInverse ρ eig hρ hρsum x - α) := by
    simp only [finiteR, ite_eq_left hx]
    field_simp [hx.ne']
    ring
  rw [cavityScalarResolvent, hden, div_mul_eq_div_div, div_self hx.ne', one_div]

lemma continuousOn_cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α : ℝ} (hα : α ≤ eig a) :
    ContinuousOn (cavityScalarResolvent ρ eig hρ hρsum α) (Ici 0) := by
  apply continuousOn_id.div
    (continuousOn_const.add (continuousOn_id.mul
      ((continuous_finiteR ρ eig hρ hρsum).continuousOn.sub continuousOn_const)))
  intro x hx
  exact (cavityScalarResolvent_denominator_pos ρ eig hρ hρsum a hα hx).ne'

lemma hasDerivAt_cavityScalarResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    HasDerivAt (cavityScalarResolvent ρ eig hρ hρsum α)
      (1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2)) x := by
  have hg : finiteInverse ρ eig hρ hρsum x - α ≠ 0 :=
    (sub_pos.mpr (hα.trans_lt ((finiteInverse_spec ρ eig hρ hρsum hx).1 a))).ne'
  have hM := (finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum
    (finiteInverse_spec ρ eig hρ hρsum hx).1).ne'
  have hd := ((hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx).hasDerivAt.sub_const α).inv hg
  have he : (fun y => (finiteInverse ρ eig hρ hρsum y - α)⁻¹) =ᶠ[𝓝 x]
      cavityScalarResolvent ρ eig hρ hρsum α := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (cavityScalarResolvent_pos_eq ρ eig hρ hρsum a hα hy).symm
  convert hd.congr_of_eventuallyEq he.symm using 1
  field_simp [hM, hg]

lemma cavityScalarResolvent_derivative_bound (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α x : ℝ} (hα : α ≤ eig a) (hx : 0 < x) :
    0 ≤ 1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2) ∧
    1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x) *
        (finiteInverse ρ eig hρ hρsum x - α)^2) ≤ (ρ a)⁻¹ := by
  classical
  let b := finiteInverse ρ eig hρ hρsum x
  let M := finiteSecondResolvent ρ eig b
  have hs : ∀ j, eig j < b := (finiteInverse_spec ρ eig hρ hρsum hx).1
  have hM : 0 < M := finiteSecondResolvent_pos (fun j => (hρ j).le) hρsum hs
  have hga : 0 < b - eig a := sub_pos.mpr (hs a)
  have hg : 0 < b - α := sub_pos.mpr (hα.trans_lt (hs a))
  have hpart : ρ a / (b - eig a)^2 ≤ M := by
    exact Finset.single_le_sum (f := fun j => ρ j / (b - eig j)^2)
      (fun j _ => div_nonneg (hρ j).le (sq_nonneg _)) (Finset.mem_univ a)
  have hsq : (b - eig a)^2 ≤ (b - α)^2 := by nlinarith
  have hprod : ρ a ≤ M * (b - α)^2 := by
    calc
      ρ a = (ρ a / (b - eig a)^2) * (b - eig a)^2 := by field_simp
      _ ≤ M * (b - eig a)^2 := mul_le_mul_of_nonneg_right hpart (sq_nonneg _)
      _ ≤ M * (b - α)^2 := mul_le_mul_of_nonneg_left hsq hM.le
  refine ⟨by positivity, ?_⟩
  simpa only [one_div, M, b] using one_div_le_one_div_of_le (hρ a) hprod

theorem cavityScalarResolvent_lipschitz (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {α : ℝ} (hα : α ≤ eig a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) :
    |cavityScalarResolvent ρ eig hρ hρsum α y - cavityScalarResolvent ρ eig hρ hρsum α x| ≤
      (ρ a)⁻¹ * (y - x) := by
  rcases hy.eq_or_lt with rfl | hxy
  · simp
  let D := fun z => 1 / (finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum z) *
    (finiteInverse ρ eig hρ hρsum z - α)^2)
  obtain ⟨z, hz, hd⟩ := exists_hasDerivAt_eq_slope
    (cavityScalarResolvent ρ eig hρ hρsum α) D hxy
    ((continuousOn_cavityScalarResolvent ρ eig hρ hρsum a hα).mono
      (fun t ht => hx.trans ht.1))
    (fun t ht => hasDerivAt_cavityScalarResolvent ρ eig hρ hρsum a hα (hx.trans_lt ht.1))
  have hbound := cavityScalarResolvent_derivative_bound ρ eig hρ hρsum a hα (hx.trans_lt hz.1)
  have he : cavityScalarResolvent ρ eig hρ hρsum α y -
      cavityScalarResolvent ρ eig hρ hρsum α x = D z * (y - x) :=
    ((eq_div_iff (sub_pos.mpr hxy).ne').mp hd).symm
  rw [he, abs_mul, abs_of_nonneg hbound.1, abs_of_pos (sub_pos.mpr hxy)]
  exact mul_le_mul_of_nonneg_right hbound.2 (sub_pos.mpr hxy).le

end InvariantIsing

end

end OAI
