import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.SpectralPowers

namespace OAI

/-! Left and right unitary first variations. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.UnitaryStationarity
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve
open Filter
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem real_inner_le_of_norm_le (v w : E) (h : ‖w‖ ≤ ‖v‖) :
    (inner ℂ v w).re ≤ (inner ℂ v v).re := by
  calc
    (inner ℂ v w).re ≤ ‖inner ℂ v w‖ := Complex.re_le_norm _
    _ ≤ ‖v‖*‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖*‖v‖ := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = (inner ℂ v v).re := by
      change ‖v‖*‖v‖ = RCLike.re (inner ℂ v v)
      rw [← pow_two, norm_sq_eq_re_inner (𝕜 := ℂ)]

theorem left_moment_real (T : Matrix ι ι ℂ →ₗ[ℂ] E) (F : Matrix ι ι ℂ)
    (hb : ∀ V : unitary (Matrix ι ι ℂ), ‖T ((V : Matrix ι ι ℂ)*F)‖ ≤ ‖T F‖)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (inner ℂ (T F) (T (H*F))).im = 0 := by
  let U := hH.eigenvectorUnitary
  let r := hH.eigenvalues
  let l : Matrix ι ι ℂ →L[ℂ] ℂ := (innerSL ℂ (T F)).comp T.toContinuousLinearMap
  have hrep : spectralHom U (fun i => (r i : ℂ)) = H := hH.spectral_theorem.symm
  have hD : HasDerivAt (fun z : ℂ => curve U r (z*Complex.I)*F)
      (Complex.I • (H*F)) 0 := by
    have hz : HasDerivAt (fun z : ℂ => z*Complex.I) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const Complex.I
    have hC := (hasDerivAt_curve_zero U r).scomp_of_eq 0 hz (by simp)
    simpa [hrep,smul_mul_assoc] using hC.mul_const F
  have hDl : HasDerivAt (fun z : ℂ => l (curve U r (z*Complex.I)*F))
      (Complex.I * l (H*F)) 0 := by
    simpa +instances [Function.comp_def] using! l.hasFDerivAt.comp_hasDerivAt 0 hD
  have hm : IsLocalMax (fun t : ℝ => (l (curve U r ((t : ℂ)*Complex.I)*F)).re) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (inner ℂ (T F) (T (curve U r ((t : ℂ)*Complex.I)*F))).re ≤ _
    have h0 : l (curve U r (((0 : ℝ) : ℂ)*Complex.I)*F) = inner ℂ (T F) (T F) := by
      simp [l]
    change _ ≤ (l _).re
    rw [h0]
    exact real_inner_le_of_norm_le _ _ (hb
      ⟨curve U r ((t : ℂ)*Complex.I), curve_mem_unitary U r _ (by simp)⟩)
  have hz := hm.hasDerivAt_eq_zero hDl.real_of_complex
  change (Complex.I * inner ℂ (T F) (T (H*F))).re = 0 at hz
  simpa using hz

theorem right_moment_real (T : Matrix ι ι ℂ →ₗ[ℂ] E) (F : Matrix ι ι ℂ)
    (hb : ∀ V : unitary (Matrix ι ι ℂ), ‖T (F*(V : Matrix ι ι ℂ))‖ ≤ ‖T F‖)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (inner ℂ (T F) (T (F*H))).im = 0 := by
  let U := hH.eigenvectorUnitary
  let r := hH.eigenvalues
  let l : Matrix ι ι ℂ →L[ℂ] ℂ := (innerSL ℂ (T F)).comp T.toContinuousLinearMap
  have hrep : spectralHom U (fun i => (r i : ℂ)) = H := hH.spectral_theorem.symm
  have hD : HasDerivAt (fun z : ℂ => F*curve U r (z*Complex.I))
      (Complex.I • (F*H)) 0 := by
    have hz : HasDerivAt (fun z : ℂ => z*Complex.I) Complex.I 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const Complex.I
    have hC := (hasDerivAt_curve_zero U r).scomp_of_eq 0 hz (by simp)
    simpa [hrep,mul_smul_comm] using hC.const_mul F
  have hDl : HasDerivAt (fun z : ℂ => l (F*curve U r (z*Complex.I)))
      (Complex.I * l (F*H)) 0 := by
    simpa +instances [Function.comp_def] using! l.hasFDerivAt.comp_hasDerivAt 0 hD
  have hm : IsLocalMax (fun t : ℝ => (l (F*curve U r ((t : ℂ)*Complex.I))).re) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (inner ℂ (T F) (T (F*curve U r ((t : ℂ)*Complex.I)))).re ≤ _
    have h0 : l (F*curve U r (((0 : ℝ) : ℂ)*Complex.I)) = inner ℂ (T F) (T F) := by
      simp [l]
    change _ ≤ (l _).re
    rw [h0]
    exact real_inner_le_of_norm_le _ _ (hb
      ⟨curve U r ((t : ℂ)*Complex.I), curve_mem_unitary U r _ (by simp)⟩)
  have hz := hm.hasDerivAt_eq_zero hDl.real_of_complex
  change (Complex.I * inner ℂ (T F) (T (F*H))).re = 0 at hz
  simpa using hz

end PolynomialPEPS.Subvolume.UnitaryStationarity

end

end OAI
