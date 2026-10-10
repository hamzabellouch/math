import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Compact unitary averaging of Hochschild cochains. -/

noncomputable section

namespace BoundedHochschild
open Filter Topology MeasureTheory MeasureTheory.Measure
variable {M : Type*} [CStarAlgebra M]

lemma continuous_translateLast {n : ℕ} (f : Cochain M (n+1)) :
    Continuous (translateLast f) := by
  let A : unitary M → (Fin (n+1) → M →L[ℂ] M) := fun u i =>
    if i=Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u:M)
    else ContinuousLinearMap.id ℂ M
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    by_cases hi : i=Fin.last n
    · simp only [A,ite_eq_left hi]
      fun_prop
    · simp only [A,ite_eq_right hi]
      exact continuous_const
  change Continuous fun u : unitary M =>
    (ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin (n+1) => M) M M)
      ((ContinuousLinearMap.mul ℂ M).flip (star (u:M)))
      ((ContinuousMultilinearMap.compContinuousLinearMapLRight f) (A u))
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℂ (fun _ : Fin (n+1) => M) M M).continuous.comp
    ((ContinuousLinearMap.mul ℂ M).flip.continuous.comp continuous_subtype_val.star)).clm_apply
      ((ContinuousMultilinearMap.compContinuousLinearMapLRight (E:=fun _ : Fin (n+1) => M) f).cont.comp hA)

section Compact
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable (ρ : G →* unitary M) (hρ : Continuous ρ)
variable (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ]

include hρ in
omit [IsTopologicalGroup G] [T2Space G] [IsMulLeftInvariant μ] in
lemma integrable_translateLast {n : ℕ} (f : Cochain M (n+1)) :
    Integrable (fun u => translateLast f (ρ u)) μ :=
  ((continuous_translateLast f).comp hρ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def compactAverage {n : ℕ} (f : Cochain M (n+1)) : Cochain M (n+1) :=
  ∫ u, translateLast f (ρ u) ∂μ

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [IsMulLeftInvariant μ] in
lemma norm_compactAverage_le {n : ℕ} (f : Cochain M (n+1)) :
    ‖compactAverage ρ μ f‖≤‖f‖ := by
  simpa [compactAverage] using norm_integral_le_of_norm_le_const
    (μ:=μ) (ae_of_all _ (fun u => norm_translateLast_le f (ρ u)))

include hρ in
omit [T2Space G] in
lemma compactAverage_fixed {n : ℕ} (f : Cochain M (n+1)) (v : G) :
    translateLast (compactAverage ρ μ f) (ρ v)=compactAverage ρ μ f := by
  change (translateLastCLM (ρ v)) (∫ u, translateLast f (ρ u) ∂μ)=_
  rw [← (translateLastCLM (ρ v)).integral_comp_comm (integrable_translateLast ρ hρ μ f)]
  change (∫ u, translateLast (translateLast f (ρ u)) (ρ v) ∂μ)=_
  simp only [translateLast_mul,← map_mul]
  exact integral_mul_left_eq_self (μ:=μ) (fun u => translateLast f (ρ u)) v

include hρ in
omit [IsTopologicalGroup G] [T2Space G] [IsMulLeftInvariant μ] in
lemma compactAverage_residual {n : ℕ} (F : Cochain M (n+1))
    (c : (Fin (n+1) → M) → M)
    (hr : ∀ v x, residualCLM x (translateLast F v)=c x) :
    ∀ v x, residualCLM x (translateLast (compactAverage ρ μ F) v)=c x := by
  intro v x
  let L : Cochain M (n+1) →L[ℂ] M := (residualCLM x).comp (translateLastCLM v)
  change L (∫ u, translateLast F (ρ u) ∂μ)=c x
  rw [← L.integral_comp_comm (integrable_translateLast ρ hρ μ F)]
  have he (u : G) : L (translateLast F (ρ u))=c x := by
    change residualCLM x (translateLast (translateLast F (ρ u)) v)=c x
    rw [translateLast_mul,hr]
  simp [he]

end Compact
end BoundedHochschild

end

end OAI
