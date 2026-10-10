import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # Local product rule for arbitrary Sobolev cutoff products

Pointwise locality allows the bounded product rule to be applied on each
finite value strip. No integrability of a third-order product is presumed.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Multiplication by a compactly supported nonnegative Lipschitz function
satisfies the local product rule even when the other factor is unbounded. -/
theorem localGamma_cutoffCLM (f η h : SobolevSpace μ hQ)
    {v : X → ℝ} {L B : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v) :
    localGamma μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f) h =ᵐ[μ]
      fun x => v x*localGamma μ hQ f h x+
        SobolevSpace.toLp μ hQ f x*localGamma μ hQ η h x := by
  let F (i : ℕ) : SobolevSpace μ hQ := SobolevSpace.compContraction μ hQ
    (clipReal_lipschitz i) (clipReal_zero i) f
  have hF (i : ℕ) : SobolevSpace.toLp μ hQ (F i) =ᵐ[μ]
      fun x => clipReal i (SobolevSpace.toLp μ hQ f x) :=
    (clipReal_lipschitz i).coeFn_compLp (clipReal_zero i) _
  have hFb (i : ℕ) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (F i) x| ≤ (i : ℝ≥0) := by
    filter_upwards [hF i] with x hx
    rw [hx]
    exact clipReal_abs_le _ _
  have hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ B := by
    filter_upwards [hrep] with x hx
    rw [hx]
    exact hb x
  have hbounded (i : ℕ) :
      localGamma μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn (F i)) h =ᵐ[μ]
      fun x => v x*localGamma μ hQ (F i) h x+
        SobolevSpace.toLp μ hQ (F i) x*localGamma μ hQ η h x := by
    have heq : SobolevSpace.cutoffCLM μ hQ hv hs hb hn (F i) =
        SobolevSpace.product μ hQ η (F i) B i := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn (F i),
        SobolevSpace.product_coe μ hQ η (F i) B i hη (hFb i),hrep] with x hc hp hr
      exact hc.trans (hp.trans (by rw [hr])).symm
    rw [heq]
    filter_upwards [localGamma_product_left μ hQ η (F i) h B i hη (hFb i),hrep]
      with x hp hr
    simpa only [hr] using hp
  have hlocal (i : ℕ) : ∀ᵐ x ∂μ,
      |SobolevSpace.toLp μ hQ f x| ≤ (i:ℝ) →
      localGamma μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f) h x =
        v x*localGamma μ hQ f h x+SobolevSpace.toLp μ hQ f x*localGamma μ hQ η h x := by
    filter_upwards [hF i,hbounded i,localGamma_eq_on_eq μ hQ (F i) f h,
      SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn (F i),
      SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn f,
      localGamma_eq_on_eq μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn (F i))
        (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f) h] with x hf hp hfg hci hcf hc
    intro hxi
    have hval : SobolevSpace.toLp μ hQ (F i) x = SobolevSpace.toLp μ hQ f x :=
      hf.trans (clipReal_eq_self (i:ℝ≥0) hxi)
    have hcv : SobolevSpace.toLp μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn (F i)) x =
        SobolevSpace.toLp μ hQ (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f) x := by
      rw [hci,hcf,hval]
    rw [← hc hcv,hp,hval,hfg hval]
  filter_upwards [ae_all_iff.mpr hlocal] with x hx
  obtain ⟨i,hi⟩ := exists_nat_ge |SobolevSpace.toLp μ hQ f x|
  exact hx i hi

end RegularPointCoordinates

end

end OAI
