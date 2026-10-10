import OAI.Probability.SLE.Loewner.InitialInverseNormalFamily
import TauCeti.Analysis.Complex.Conformal.Hurwitz

namespace OAI

/-! Limits of initial inverse slit charts remain nondegenerate and univalent. -/
noncomputable section
open Set Filter Function Metric
open scoped Topology

namespace SLEExactGauge

lemma initialInverseChart_im_ge (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane) :
    z.im≤(initialInverseChart p hi h0 hH t z).im := by
  by_cases ht : t=0
  · simp only [ht,initialInverseChart_zero,id_eq,le_refl]
  · rw [initialInverseChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).inverse_im_ge hz

lemma initialInverseChart_injOn (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t : unitInterval) : InjOn (initialInverseChart p hi h0 hH t) upperHalfPlane := by
  by_cases ht : t=0
  · simp only [ht,initialInverseChart_zero]
    exact injective_id.injOn
  · rw [initialInverseChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).inverse_injOn

lemma initialInverse_limit_im_ge (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {z : ℂ} (hz : z∈upperHalfPlane) : z.im≤(F z).im :=
  ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp (hlim.tendsto_at hz))
    (Eventually.of_forall fun n => initialInverseChart_im_ge p hi h0 hH (t n) hz)

lemma initialInverse_limit_injOn (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) : InjOn F upperHalfPlane := by
  rcases TauCeti.hurwitz_injOn isOpen_upperHalfPlane
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
    (Eventually.of_forall fun n => initialInverseChart_differentiableOn p hi h0 hH (t n)) hlim
    (Eventually.of_forall fun n => initialInverseChart_injOn p hi h0 hH (t n)) with hh | ⟨c,hc⟩
  · exact hh
  · let y := max c.im 0+1
    have hy : 0<y := by dsimp [y]; linarith [le_max_right c.im 0]
    have hz : (y:ℂ)*Complex.I∈upperHalfPlane := by simpa [upperHalfPlane] using hy
    have hh := initialInverse_limit_im_ge p hi h0 hH hlim hz
    rw [hc _ hz] at hh
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.ofReal_im,Complex.I_re,mul_zero,add_zero] at hh
    exact False.elim (by dsimp [y] at hh; linarith [le_max_left c.im 0])

lemma initialInverse_limit_displacement (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} {c : ℝ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane)
    (hcap : Tendsto (fun n => initialCapacity p hi h0 hH (t n)) atTop (𝓝 c))
    {z : ℂ} (hz : z∈upperHalfPlane) : ‖F z-z‖≤c/z.im :=
  le_of_tendsto_of_tendsto ((hlim.tendsto_at hz).sub_const z).norm (hcap.div_const z.im)
    (Eventually.of_forall fun n => initialInverseChart_displacement p hi h0 hH (t n) hz)

end SLEExactGauge

end

end OAI
