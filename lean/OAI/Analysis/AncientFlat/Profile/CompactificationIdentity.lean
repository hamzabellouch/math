import OAI.Analysis.AncientFlat.Profile.CompactificationCoeff

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicAnnular
lemma sqrt_compact_argument {r τ : ℝ} (_ : 0<r) (hτ : 0<τ) :
    Real.sqrt (τ/r^4)=Real.sqrt τ/r^2 := by
  rw [Real.sqrt_div hτ.le,show r^4=(r^2)^2 by ring,Real.sqrt_sq (sq_nonneg r)]
lemma compact_argument_inv {r τ : ℝ} (hr : 0<r) (hτ : 0<τ) :
    ((τ/r^4)^(-(1:ℝ)/2))=r^2/Real.sqrt τ := by
  rw [neg_half_rpow (by positivity),sqrt_compact_argument hr hτ,inv_div]
lemma compactPrincipal_eq (G H : ℝ → ℝ)
    (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    {r τ : ℝ} (hr : 0<r) (hτ : 0<τ) :
    compactPrincipal H (r,τ)=G (r^2/Real.sqrt τ)^2/16 := by
  dsimp [compactPrincipal,compactArgument]
  rw [hmatch _ (by positivity),compact_argument_inv hr hτ]
lemma compactPotential_eq (G H : ℝ → ℝ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0))
    (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    {r τ : ℝ} (hr : 0<r) (hτ : 0<τ) :
    compactPotential H (r,τ)= -τ⁻¹*((r^2/Real.sqrt τ)*deriv G (r^2/Real.sqrt τ)/G (r^2/Real.sqrt τ)) := by
  have hq : Real.sqrt τ≠0 := (Real.sqrt_pos.mpr hτ).ne'
  dsimp [compactPotential,compactArgument]
  rw [compactification_deriv G H hG hmatch (by positivity),sqrt_compact_argument hr hτ,
    inv_div,hmatch _ (by positivity),compact_argument_inv hr hτ]
  have he : τ=(Real.sqrt τ)^2 := (Real.sq_sqrt hτ.le).symm
  rw [he]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg τ)]
  field_simp [hr.ne',hq]
end ParabolicAnnular

end

end OAI
