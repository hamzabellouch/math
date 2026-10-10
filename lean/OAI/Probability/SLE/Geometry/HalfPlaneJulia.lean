import OAI.Probability.SLE.Geometry.HalfPlaneSchwarzPick

namespace OAI

/-! The boundary Schwarz–Pick limit at infinity. Only a normalized
sequence tending vertically to infinity is needed for slit comparisons. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma normSq_div_real (z : ℂ) (y : ℝ) : normSq (z/(y:ℂ))=normSq z/y^2 := by
  simp [normSq_apply,pow_two]

lemma halfPlane_schwarz_pick_scaled {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (hm : MapsTo f upperHalfPlane upperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlane) {y : ℝ} (hy : 0<y) :
    z.im*normSq (f z/(y:ℂ)-conj (f ((y:ℂ)*I)/(y:ℂ))) ≤
      (f z).im*(f ((y:ℂ)*I)/(y:ℂ)).im*normSq (z/(y:ℂ)+I) := by
  have hw : (y:ℂ)*I ∈ upperHalfPlane := by simpa [upperHalfPlane] using hy
  have hh := halfPlane_schwarz_pick_kernel hf hm hz hw
  have h1 : f z/(y:ℂ)-conj (f ((y:ℂ)*I)/(y:ℂ)) =
      (f z-conj (f ((y:ℂ)*I)))/(y:ℂ) := by
    rw [map_div₀,conj_ofReal,sub_div]
  have h2 : z/(y:ℂ)+I = (z-conj ((y:ℂ)*I))/(y:ℂ) := by
    simp only [map_mul,conj_ofReal,conj_I]
    field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
    ring
  rw [h1,h2,normSq_div_real,normSq_div_real,div_ofReal_im]
  have hi : ((y:ℂ)*I).im=y := by simp
  rw [hi] at hh
  have hp : 0<y^3 := pow_pos hy 3
  apply (mul_le_mul_iff_of_pos_right hp).mp
  field_simp
  nlinarith [hh]

theorem halfPlane_julia_at_infinity {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlane) (hm : MapsTo f upperHalfPlane upperHalfPlane)
    (y : ℕ → ℝ) (hy : ∀ n, 0<y n)
    (hinv : Tendsto (fun n => (y n)⁻¹) atTop (𝓝 0))
    (hfn : Tendsto (fun n => f ((y n:ℂ)*I)/(y n:ℂ)) atTop (𝓝 I))
    {z : ℂ} (hz : z ∈ upperHalfPlane) : z.im ≤ (f z).im := by
  have hzero (w : ℂ) : Tendsto (fun n => w/(y n:ℂ)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := w) (f := atTop)).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hinv)
    simpa only [Function.comp_def,ofReal_zero,mul_zero,ofReal_inv,div_eq_mul_inv] using hh
  have hL := (hzero (f z)).sub (Complex.continuous_conj.tendsto I |>.comp hfn)
  have hR := (hzero z).add_const I
  have hIm := Complex.continuous_im.tendsto I |>.comp hfn
  have hnL := (continuous_normSq.tendsto ((0:ℂ)-conj I)).comp hL
  have hnR := (continuous_normSq.tendsto ((0:ℂ)+I)).comp hR
  have hl := (tendsto_const_nhds (x := z.im) (f := atTop)).mul hnL
  have hr := ((tendsto_const_nhds (x := (f z).im) (f := atTop)).mul hIm).mul hnR
  have hh := le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun n => halfPlane_schwarz_pick_scaled hf hm hz (hy n)))
  simpa only [conj_I,zero_sub,neg_neg,zero_add,normSq_I,I_im,mul_one] using hh

end SLEExactGauge

end

end OAI
