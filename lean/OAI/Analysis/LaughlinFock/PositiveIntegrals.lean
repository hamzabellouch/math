import Mathlib
import OAI.Analysis.LaughlinFock.NormalOrdering

namespace OAI

/-! Positive Integrals. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder BigOperators Matrix.Norms.Elementwise
open MeasureTheory

local instance {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

 
def quadraticEvaluation {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun M := star x ⬝ᵥ (M *ᵥ x)
  map_add' M N := by simp only [Matrix.add_mulVec, dotProduct_add]
  map_smul' c M := by
    simp only [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply]

 
theorem matrixIntegral_apply {G ι κ : Type*} [MeasurableSpace G] [Fintype ι] [Fintype κ]
    (μ : Measure G) {M : G → Matrix ι κ ℂ} (hM : Integrable M μ) (i : ι) (j : κ) :
    (∫ g, M g ∂μ) i j = ∫ g, M g i j ∂μ := by
  let L : Matrix ι κ ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (L.toContinuousLinearMap.integral_comp_comm hM).symm

 

theorem matrixIntegral_isHermitian {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ)
    (hH : ∀ᵐ g ∂μ, (M g).IsHermitian) : (∫ g, M g ∂μ).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [matrixIntegral_apply μ hM, RCLike.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [hH] with g hg
  exact Matrix.IsHermitian.ext_iff.mp hg i j

theorem quadraticEvaluation_integral {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ) (x : ι → ℂ) :
    star x ⬝ᵥ ((∫ g, M g ∂μ) *ᵥ x) = ∫ g, star x ⬝ᵥ (M g *ᵥ x) ∂μ :=
  (LinearMap.toContinuousLinearMap (quadraticEvaluation x)).integral_comp_comm hM |>.symm

 

theorem matrixIntegral_posSemidef {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M : G → Matrix ι ι ℂ} (hM : Integrable M μ)
    (hP : ∀ᵐ g ∂μ, (M g).PosSemidef) : (∫ g, M g ∂μ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (matrixIntegral_isHermitian μ hM (hP.mono (fun _ h => h.isHermitian)))
  intro x
  rw [quadraticEvaluation_integral μ hM]
  apply integral_nonneg_of_ae
  exact hP.mono (fun _ h => h.dotProduct_mulVec_nonneg x)

 
theorem exteriorLift_integral {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (Q k : ℕ) {M : G → Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ}
    (hM : Integrable M μ) :
    exteriorLift Q k (∫ g, M g ∂μ) = ∫ g, exteriorLift Q k (M g) ∂μ :=
  (LinearMap.toContinuousLinearMap (exteriorLiftLinear Q k)).integral_comp_comm hM |>.symm

 
theorem matrixIntegral_relative_bound {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) {M H : G → Matrix ι ι ℂ} (hM : Integrable M μ) (hH : Integrable H μ)
    (r : ℝ) (h : ∀ᵐ g ∂μ, (M g + r • H g).PosSemidef) :
    ((∫ g, M g ∂μ) + r • ∫ g, H g ∂μ).PosSemidef := by
  have hP := matrixIntegral_posSemidef μ (hM.add (hH.smul r)) h
  change (∫ g, M g + r • H g ∂μ).PosSemidef at hP
  have hAdd : (∫ g, M g + r • H g ∂μ) =
      (∫ g, M g ∂μ) + (∫ g, r • H g ∂μ) := integral_add hM (hH.smul r)
  have hS : (∫ g, r • H g ∂μ) = r • ∫ g, H g ∂μ := integral_smul r H
  rw [hAdd, hS] at hP
  exact hP

 

theorem conjugationIntegral_posSemidef {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) (U : G → Matrix ι ι ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : Integrable (fun g => U g * M * (U g)ᴴ) μ) :
    (∫ g, U g * M * (U g)ᴴ ∂μ).PosSemidef :=
  matrixIntegral_posSemidef μ hI (Filter.Eventually.of_forall
    (fun g => hM.mul_mul_conjTranspose_same (U g)))

end LaughlinFock
end

end OAI
