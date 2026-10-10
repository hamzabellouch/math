import Mathlib
import OAI.Analysis.SymmetricDomains.ChartAbsDetOne
import OAI.Analysis.SymmetricDomains.BiHaarInvInvariant

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology MeasureTheory

theorem chartLeftDensity_continuousOn
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph G E) (he1 : 1∈e.source)
    (hdet : Continuous (fun g : G => (fderiv ℝ (chartLeftMap e g) (e 1)).det))
    (hD : ∀ (g : G) y, y∈e.target → g*e.symm y∈e.source →
      (fderiv ℝ (chartLeftMap e g) y).det≠0) :
    ContinuousOn (chartLeftDensity e) e.target := by
  change ContinuousOn (fun x => |(fderiv ℝ (chartLeftMap e (e.symm x)) (e 1)).det|⁻¹) e.target
  apply ((hdet.comp_continuousOn e.symm.continuousOn).abs).inv₀
  intro x hx
  apply abs_ne_zero.mpr
  apply hD _ _ (e.map_source he1)
  simpa only [e.left_inv he1,mul_one] using e.map_target hx

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_chart_unimodular_jacobian :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      (∀ (p' : U) y, y∈e.target →
        ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) y) ∧
      ∀ g : Biholomorph U U,
        |(fderiv ℝ (fun x => e (g*e.symm x*g⁻¹)) (e 1)).det|=1 := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let _ : FiniteDimensional ℝ R := inferInstance
  let _ : ProperSpace R := FiniteDimensional.proper ℝ R
  let _ : LocallyCompactSpace R := inferInstance
  let _ : MeasurableSpace R := borel R
  let _ : BorelSpace R := ⟨rfl⟩
  let _ : LocallyCompactSpace (Biholomorph U U) :=
    bounded_divisible_automorphism_locallyCompact hU hc.isPreconnected hbd Γ hhol p
  let _ : MeasurableSpace (Biholomorph U U) := borel (Biholomorph U U)
  let _ : BorelSpace (Biholomorph U U) := ⟨rfl⟩
  let μ : Measure (Biholomorph U U) := Measure.haar
  let _ : μ.IsMulRightInvariant :=
    bounded_divisible_automorphism_unimodular hU hc.isPreconnected hbd Γ hhol p
  let _ : μ.IsInvInvariant := biHaar_isInvInvariant μ
  obtain ⟨P,e,he,he1,hP,hreg⟩ := exists_actual_aut_firstJet_COne_neighborhood hU hc hbd Γ hhol p
  have hC (g h : Biholomorph U U) (y : R) (hy : y∈e.target) :
      ContDiffAt ℝ 1 (fun t => e (g*e.symm t*h)) y := by
    have hr := firstJet_mul_const_contDiffAt hU p h e.symm y (hreg (h.toHomeomorph p) y hy)
    have hl := firstJet_const_mul_contDiffAt hU p g (fun t => e.symm t*h) y hr
    have hPdiff := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
        (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) P).contDiffAt.comp y hl
    simpa only [Function.comp_def,he,mul_assoc] using hPdiff
  have hCL (g : Biholomorph U U) (y : R) (hy : y∈e.target) :
      ContDiffAt ℝ 1 (chartLeftMap e g) y := by
    change ContDiffAt ℝ 1 (fun t => e (g*e.symm t)) y
    simpa only [mul_one] using hC g 1 y hy
  have hD (g : Biholomorph U U) (y : R) (hy : y∈e.target) (hg : g*e.symm y∈e.source) :
      (fderiv ℝ (chartLeftMap e g) y).det≠0 :=
    openChart_leftTranslate_det_ne_zero e hCL g y hy hg
  have hL := (hreg p (e 1) (e.map_source he1)).hasStrictFDerivAt (by simp)
  have hdet := projected_chart_left_determinant_continuous hU p P e he he1 _ hL
  have hρ := chartLeftDensity_continuousOn e he1 hdet hD
  refine ⟨P,e,he,he1,hP,hreg,?_⟩
  intro g
  let F : (Biholomorph U U) ≃ₜ (Biholomorph U U) :=
    (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  have hF : MeasurePreserving F μ μ :=
    (measurePreserving_mul_right μ g⁻¹).comp (measurePreserving_mul_left μ g)
  have hF1 : F 1=1 := by simp [F]
  exact chart_abs_det_one_of_haar_preserving e he1 μ (Measure.addHaar : Measure R)
    hCL hD hρ F hF hF1 (hC g g⁻¹)
end Biholomorph
end Release061

end

end OAI
