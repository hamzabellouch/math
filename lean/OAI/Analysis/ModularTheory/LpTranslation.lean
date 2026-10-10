import OAI.Analysis.ModularTheory.LpRepresentation
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! Translation and covariance for the concrete modular representation on
L²(ℝ,H). No property of the von Neumann closure is postulated here. -/

noncomputable section
open Filter MeasureTheory

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ) [Measure.IsAddRightInvariant μ]

def modularLpTranslate (t : ℝ) : Lp H 2 μ →ₗᵢ[ℂ] Lp H 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun s : ℝ => s - t) (measurePreserving_sub_right μ t)

omit [CompleteSpace H] in
lemma modularLpTranslate_ae (t : ℝ) (f : Lp H 2 μ) :
    modularLpTranslate μ t f =ᵐ[μ] fun s => f (s - t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right μ t)

omit [CompleteSpace H] in
lemma modularLpTranslate_comp (t r : ℝ) (f : Lp H 2 μ) :
    modularLpTranslate μ t (modularLpTranslate μ r f) =
      modularLpTranslate μ (t + r) f := by
  apply Lp.ext
  filter_upwards [modularLpTranslate_ae μ t (modularLpTranslate μ r f),
    (measurePreserving_sub_right μ t).quasiMeasurePreserving.ae
      (modularLpTranslate_ae μ r f),
    modularLpTranslate_ae μ (t + r) f] with s ht hr htr
  rw [ht, hr, htr]
  congr 1
  ring

omit [CompleteSpace H] in
@[simp] lemma modularLpTranslate_zero (f : Lp H 2 μ) :
    modularLpTranslate μ 0 f = f := by
  apply Lp.ext
  filter_upwards [modularLpTranslate_ae μ 0 f] with s hs
  simpa only [sub_zero] using hs

def modularLpTranslateEquiv (t : ℝ) : Lp H 2 μ ≃ₗᵢ[ℂ] Lp H 2 μ where
  toFun := modularLpTranslate μ t
  invFun := modularLpTranslate μ (-t)
  left_inv f := by rw [modularLpTranslate_comp, neg_add_cancel, modularLpTranslate_zero]
  right_inv f := by rw [modularLpTranslate_comp, add_neg_cancel, modularLpTranslate_zero]
  map_add' := map_add (modularLpTranslate μ t)
  map_smul' c f := by simp only [map_smul, RingHom.id_apply]
  norm_map' := (modularLpTranslate μ t).norm_map

/-- The regular translation and twisted coefficients obey the actual
covariance equation for the spectral modular group. -/
lemma modularLp_covariance (D : BoundedRecovery.RealSpectralCalculus H)
    (t : ℝ) (T : H →L[ℂ] H) (f : Lp H 2 μ) :
    modularLpTranslate μ t
        (modularLpRepresentation μ D T (modularLpTranslate μ (-t) f)) =
      modularLpRepresentation μ D
        (D.unitary t * T * D.unitary (-t)) f := by
  apply Lp.ext
  filter_upwards [modularLpTranslate_ae μ t
      (modularLpRepresentation μ D T (modularLpTranslate μ (-t) f)),
    (measurePreserving_sub_right μ t).quasiMeasurePreserving.ae
      (modularLpRepresentation_ae μ D T (modularLpTranslate μ (-t) f)),
    (measurePreserving_sub_right μ t).quasiMeasurePreserving.ae
      (modularLpTranslate_ae μ (-t) f),
    modularLpRepresentation_ae μ D (D.unitary t * T * D.unitary (-t)) f]
    with s hshift hT hf hright
  rw [hshift, hT, hf, hright]
  have hs : s - t - -t = s := by ring
  rw [hs]
  have hl : D.unitary (-(s - t)) = D.unitary (-s) * D.unitary t := by
    rw [← D.unitary_add]
    congr 1
    ring
  have hr : D.unitary (s - t) = D.unitary (-t) * D.unitary s := by
    rw [← D.unitary_add]
    congr 1
    ring
  rw [hl, hr]
  simp only [mul_apply_eq_comp]

end WeakPureInfiniteness

end

end OAI
