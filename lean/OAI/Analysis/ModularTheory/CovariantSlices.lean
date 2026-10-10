import OAI.Analysis.ModularTheory.AmplifiedModularAction

namespace OAI

/-! The scalar slices of a fixed point are actual elements of the original
von Neumann algebra and satisfy its modular covariance equation. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]
  (S : BoundedRecovery.StandardModularData H)

omit [Measure.IsAddRightInvariant μ] in
lemma scalarOperatorSlice_mem_modular (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : T ∈ amplifiedModularAlgebra μ S) (f g : Lp ℂ 2 μ) :
    scalarOperatorSlice μ T f g ∈ S.M := by
  rw [← S.M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  exact (pointwise_commute_iff_slices μ T b).mp
    ((mem_amplifiedModularAlgebra μ S T).mp hT b hb) f g

lemma scalarVectorLp_rightTranslation (s : ℝ) (f : Lp ℂ 2 μ) (x : H) :
    modularRightTranslation μ S.D s (scalarVectorLp μ f x) =
      scalarVectorLp μ (modularLpTranslate μ (-s) f) (S.D.unitary s x) := by
  apply Lp.ext
  filter_upwards [modularRightTranslation_ae μ S.D s (scalarVectorLp μ f x),
    (measurePreserving_add_right μ s).quasiMeasurePreserving.ae (scalarVectorLp_ae μ f x),
    scalarVectorLp_ae μ (modularLpTranslate μ (-s) f) (S.D.unitary s x),
    modularLpTranslate_ae μ (-s) f] with t h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, sub_neg_eq_add, map_smul]

lemma scalarVectorLp_translated (s : ℝ) (f : Lp ℂ 2 μ) (x : H) :
    scalarVectorLp μ (modularLpTranslate μ (-s) f) x =
      modularRightTranslation μ S.D s (scalarVectorLp μ f (S.D.unitary (-s) x)) := by
  rw [scalarVectorLp_rightTranslation]
  have he : S.D.unitary s (S.D.unitary (-s) x) = x := by
    change (S.D.unitary s * S.D.unitary (-s)) x = x
    rw [S.D.unitary_mul_neg]
    rfl
  rw [he]

lemma scalarOperatorSlice_modular_covariance
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ s f, T (modularRightTranslation μ S.D s f) =
      modularRightTranslation μ S.D s (T f))
    (f g : Lp ℂ 2 μ) (s : ℝ) :
    scalarOperatorSlice μ T (modularLpTranslate μ (-s) f) (modularLpTranslate μ (-s) g) =
      S.sigma s (scalarOperatorSlice μ T f g) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [scalarOperatorSlice_inner, scalarVectorLp_translated μ S s g x,
    scalarVectorLp_translated μ S s f y, hT]
  change inner ℂ (modularRightTranslationEquiv μ S.D s _)
      (modularRightTranslationEquiv μ S.D s _) = _
  rw [LinearIsometryEquiv.inner_map_map, ← scalarOperatorSlice_inner]
  change inner ℂ (scalarOperatorSlice μ T f g (S.D.unitary (-s) x)) (S.D.unitary (-s) y) =
    inner ℂ (S.D.unitary s (scalarOperatorSlice μ T f g (S.D.unitary (-s) x))) y
  have he := ContinuousLinearMap.adjoint_inner_right (S.D.unitary s)
    (scalarOperatorSlice μ T f g (S.D.unitary (-s) x)) y
  change inner ℂ (scalarOperatorSlice μ T f g (S.D.unitary (-s) x))
    (star (S.D.unitary s) y) = _ at he
  rw [S.D.unitary_star] at he
  exact he

end WeakPureInfiniteness

end

end OAI
