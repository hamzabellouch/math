import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.SurfaceImmersion.Geometry.ModulatedJets

namespace OAI

/-! Phase multiplication is an actual linear operator on supported smooth
fields, with the same fixed support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℂ ℝ F]

def multiplierLM (K : Compacts Base) (a : Base → ℂ) (ha : ContDiff ℝ ∞ a) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) K where
  toFun H := ⟨fun p => a p • H p, ha.smul H.contDiff, fun p hp => by
    change a p • H p = 0
    simp only [H.zero_on_compl hp, Pi.zero_apply, smul_zero]⟩
  map_add' H J := by
    apply DFunLike.ext
    intro p
    exact smul_add (a p) (H p) (J p)
  map_smul' c H := by
    apply DFunLike.ext
    intro p
    exact smul_comm (a p) c (H p)

lemma multiplierLM_apply (K : Compacts Base) (a : Base → ℂ) (ha : ContDiff ℝ ∞ a)
    (H : SupportedField (F := F) K) (p : Base) : multiplierLM K a ha H p = a p • H p := rfl

namespace ModulatedJets

lemma phase_neg_inv (τ : ℝ) (φ : Base → ℝ) (p : Base) :
    phase τ (fun q => -φ q) p = (phase τ φ p)⁻¹ := by
  simp only [phase, Complex.ofReal_neg, mul_neg, Complex.exp_neg]

def phaseLM (K : Compacts Base) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) K :=
  multiplierLM K (phase τ φ) (phase_smooth hφ τ)

def inversePhaseLM (K : Compacts Base) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) K :=
  phaseLM K hφ.neg τ

lemma inversePhaseLM_phaseLM (K : Compacts Base) {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (τ : ℝ) (H : SupportedField (F := F) K) :
    inversePhaseLM K hφ τ (phaseLM K hφ τ H) = H := by
  apply DFunLike.ext
  intro p
  change phase τ (fun q => -φ q) p • (phase τ φ p • H p) = H p
  have hp : phase τ φ p ≠ 0 := Complex.exp_ne_zero _
  rw [phase_neg_inv, smul_smul, inv_mul_cancel₀ hp, one_smul]

end ModulatedJets
end ClosedSurfaceR4.JetPolynomial

end

end OAI
