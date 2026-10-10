import OAI.Analysis.KLS.Sobolev.Witnesses

namespace OAI

/-! Changing an almost-everywhere representative preserves the actual weak
partial derivatives. These bridges do not require pointwise regularity. -/
open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
 theorem HasWeakPartialDeriv.congr_ae {i : Fin d} {f f' g g' : E → ℝ} {U : Set E}
    (h : HasWeakPartialDeriv i g f U)
    (hf : f =ᵐ[volume.restrict U] f') (hg : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDeriv i g' f' U := by
  intro φ hφ hs hsub
  have he := h φ hφ hs hsub
  calc
    _ = ∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -(∫ x in U, g x * φ x) := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

omit [NeZero d] in
 theorem MemW1p.congr_ae {p : ℝ≥0∞} {f g : E → ℝ} {U : Set E}
    (h : MemW1p p f U) (he : f =ᵐ[volume.restrict U] g) : MemW1p p g U := by
  refine ⟨h.1.ae_eq he, ?_⟩
  intro i
  obtain ⟨G, hG, hw⟩ := h.2 i
  exact ⟨G, hG, hw.congr_ae he (Filter.EventuallyEq.rfl)⟩

 def MemW1pWitness.congr_ae {p : ℝ≥0∞} {f g : E → ℝ} {U : Set E}
    (h : MemW1pWitness p f U) (he : f =ᵐ[volume.restrict U] g) :
    MemW1pWitness p g U where
  memLp := h.memLp.ae_eq he
  weakGrad := h.weakGrad
  weakGrad_component_memLp := h.weakGrad_component_memLp
  isWeakGrad i := (h.isWeakGrad i).congr_ae he Filter.EventuallyEq.rfl

end DeGiorgi

end

end OAI
