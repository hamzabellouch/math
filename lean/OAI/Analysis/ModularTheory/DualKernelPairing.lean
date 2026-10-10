import OAI.Analysis.OperatorAlgebra.ScalarKernelPairing
import OAI.Analysis.ModularTheory.DualRegularization

namespace OAI

/-! The exact character factor on a convolution-smoothed kernel under the
dual action. This precedes Gaussian integration of that factor. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace WeakPureInfiniteness

lemma modularDual_scalar_integrable (r : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ))
    (hu : Integrable (u : ℝ → ℂ)) :
    Integrable (modularDual volume r u : ℝ → ℂ) := by
  apply hu.norm.mono' (Lp.aestronglyMeasurable _)
  filter_upwards [modularDual_ae volume r u] with t ht
  rw [ht, norm_smul, BoundedRecovery.spectralCharacter_norm, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma modularDual_scalarVector (r : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    modularDual volume r (scalarVectorLp volume u x) =
      scalarVectorLp volume (modularDual volume r u) x := by
  apply Lp.ext
  filter_upwards [modularDual_ae volume r (scalarVectorLp volume u x),
    scalarVectorLp_ae volume u x, scalarVectorLp_ae volume (modularDual volume r u) x,
    modularDual_ae volume r u] with t h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_smul]
  rfl

omit [CompleteSpace H] in
lemma modularDual_inner_left (r : ℝ) (f g : Lp H 2 (volume : Measure ℝ)) :
    inner ℂ (modularDual volume r f) g = inner ℂ f (modularDual volume (-r) g) :=
  (modularDualUnitary volume r).inner_map_eq_flip f g

lemma spectralCharacter_dual_kernel (r s t : ℝ) :
    star (BoundedRecovery.spectralCharacter (-r) t) *
      BoundedRecovery.spectralCharacter (-r) s =
      BoundedRecovery.spectralCharacter (-r) (s - t) := by
  change star (Complex.exp _) * Complex.exp _ = Complex.exp _
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem modularDual_convolutionSmoothed_pairing
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ))
    (hu : Integrable (u : ℝ → ℂ)) (hv : Integrable (v : ℝ → ℂ))
    (r : ℝ) (x y : H) :
    inner ℂ (modularDualConjugation volume r (convolutionSmoothedOperator T f g hf hg)
      (scalarVectorLp volume u x)) (scalarVectorLp volume v y) =
      ∫ t : ℝ, ∫ s : ℝ, BoundedRecovery.spectralCharacter (-r) (s - t) *
        (star (u t) * v s * inner ℂ (modularSliceKernel T f g s t x) y) := by
  change inner ℂ (modularDual volume r
    (convolutionSmoothedOperator T f g hf hg
      (modularDual volume (-r) (scalarVectorLp volume u x)))) _ = _
  rw [modularDual_inner_left, modularDual_scalarVector, modularDual_scalarVector]
  refine (convolutionSmoothedOperator_pairing T f g
    (modularDual volume (-r) u) (modularDual volume (-r) v) hf hg
    (modularDual_scalar_integrable (-r) u hu) (modularDual_scalar_integrable (-r) v hv)
    x y).trans ?_
  apply integral_congr_ae
  filter_upwards [modularDual_ae volume (-r) u] with t ht
  apply integral_congr_ae
  filter_upwards [modularDual_ae volume (-r) v] with s hs
  rw [ht, hs, smul_eq_mul, smul_eq_mul, star_mul]
  calc
    _ = (star (BoundedRecovery.spectralCharacter (-r) t) *
        BoundedRecovery.spectralCharacter (-r) s) *
        (star (u t) * v s * inner ℂ (modularSliceKernel T f g s t x) y) := by ring
    _ = _ := by rw [spectralCharacter_dual_kernel]

end WeakPureInfiniteness

end

end OAI
