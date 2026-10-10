import OAI.Analysis.ModularTheory.LpGauge

namespace OAI

/-! The pointwise operator representation, and its modular gauge
conjugate, on the Hilbert space of square-integrable vector-valued functions.
This supplies the coefficient representation for the continuous core. -/

noncomputable section
open Filter MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ)

lemma pointwiseLp_star (T : H →L[ℂ] H) :
    (star T).compLpL 2 μ = star (T.compLpL 2 μ) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(star T).coeFn_compLpL (p := 2) (μ := μ) f,
    T.coeFn_compLpL (p := 2) (μ := μ) g] with t hf hg
  rw [hf, hg]
  exact ContinuousLinearMap.adjoint_inner_left T (g t) (f t)

def pointwiseLpRepresentation :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun T := T.compLpL 2 μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [(0 : H →L[ℂ] H).coeFn_compLpL (p := 2) (μ := μ) f,
      Lp.coeFn_zero (E := H) (p := 2) (μ := μ)] with t hf hz
    simpa only [zero_apply] using hf.trans hz.symm
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [(1 : H →L[ℂ] H).coeFn_compLpL (p := 2) (μ := μ) f] with t hf
    exact hf
  map_add' T R := ContinuousLinearMap.add_compLpL T R
  map_mul' T R := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [(T * R).coeFn_compLpL (p := 2) (μ := μ) f,
      T.coeFn_compLpL (p := 2) (μ := μ) (R.compLpL 2 μ f),
      R.coeFn_compLpL (p := 2) (μ := μ) f] with t hTR hT hR
    change _ = (T.compLpL 2 μ (R.compLpL 2 μ f)) t
    rw [hTR, hT, hR, mul_apply_eq_comp]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [(algebraMap ℂ (H →L[ℂ] H) c).coeFn_compLpL (p := 2) (μ := μ) f,
      Lp.coeFn_smul c f] with t hc hf
    change _ = (c • f) t
    rw [hc, hf, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
    rfl
  map_star' := pointwiseLp_star μ

/-- The actual modularly twisted coefficient representation. -/
def modularLpRepresentation (D : BoundedRecovery.RealSpectralCalculus H) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) :=
  (D.lpGaugeEquiv μ (-1)).conjStarAlgEquiv.toStarAlgHom.comp
    (pointwiseLpRepresentation μ)

lemma modularLpRepresentation_ae (D : BoundedRecovery.RealSpectralCalculus H)
    (T : H →L[ℂ] H) (f : Lp H 2 μ) :
    modularLpRepresentation μ D T f =ᵐ[μ]
      fun t => D.unitary (-t) (T (D.unitary t (f t))) := by
  have hinv : (D.lpGaugeEquiv μ (-1)).symm f = D.lpGauge μ 1 f := by
    change D.lpGauge μ (-(-1)) f = _
    congr 2
    norm_num
  change D.lpGauge μ (-1)
    (T.compLpL 2 μ ((D.lpGaugeEquiv μ (-1)).symm f)) =ᵐ[μ] _
  rw [hinv]
  simpa only [neg_neg, neg_one_mul, one_mul] using
    D.lpGauge_conjugate_constant_ae μ (-1) T f

end WeakPureInfiniteness

end

end OAI
