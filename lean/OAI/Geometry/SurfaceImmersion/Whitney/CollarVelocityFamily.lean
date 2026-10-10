import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityVector
import OAI.Geometry.SurfaceImmersion.Geometry.FlatExtension

namespace OAI

/-! Smooth parameter families of the actual collar velocity. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open CovarianceCorrector
open VelocityPlane (Space)

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {S : Set A} {R v a : A → ℝ} {e₁ e₂ : A → Space}

lemma vectorLoop_family_smoothOn
    (hR : ContDiffOn ℝ ∞ R S) (hv : ContDiffOn ℝ ∞ v S)
    (ha : ContDiffOn ℝ ∞ a S) (h₁ : ContDiffOn ℝ ∞ e₁ S)
    (h₂ : ContDiffOn ℝ ∞ e₂ S) (hn : ∀ p ∈ S, R p + v p ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : A × ℝ =>
      vectorLoop (e₁ z.1) (e₂ z.1) (R z.1) (v z.1) (a z.1) (z.2 : Period))
      (S ×ˢ Set.univ) := by
  have hRf : ContDiffOn ℝ ∞ (fun z : A × ℝ => R z.1) (S ×ˢ Set.univ) :=
    hR.comp contDiffOn_fst (fun _ hz => hz.1)
  have hvf : ContDiffOn ℝ ∞ (fun z : A × ℝ => v z.1) (S ×ˢ Set.univ) :=
    hv.comp contDiffOn_fst (fun _ hz => hz.1)
  have haf : ContDiffOn ℝ ∞ (fun z : A × ℝ => a z.1) (S ×ˢ Set.univ) :=
    ha.comp contDiffOn_fst (fun _ hz => hz.1)
  have h₁f : ContDiffOn ℝ ∞ (fun z : A × ℝ => e₁ z.1) (S ×ˢ Set.univ) :=
    h₁.comp contDiffOn_fst (fun _ hz => hz.1)
  have h₂f : ContDiffOn ℝ ∞ (fun z : A × ℝ => e₂ z.1) (S ×ˢ Set.univ) :=
    h₂.comp contDiffOn_fst (fun _ hz => hz.1)
  have hAmp : ContDiffOn ℝ ∞ (fun z : A × ℝ => amplitude (R z.1) (v z.1) (a z.1))
      (S ×ˢ Set.univ) :=
    (contDiffOn_const.mul haf).div (hRf.add hvf) (fun z hz => hn z.1 hz.1)
  exact (hRf.mul (unitX_smooth.comp_contDiffOn (hAmp.prodMk contDiffOn_snd))).smul h₁f |>.add
    ((hRf.mul (unitY_smooth.comp_contDiffOn (hAmp.prodMk contDiffOn_snd))).smul h₂f)

lemma vectorLoop_family_smooth
    (hR : ContDiff ℝ ∞ R) (hv : ContDiff ℝ ∞ v) (ha : ContDiff ℝ ∞ a)
    (h₁ : ContDiff ℝ ∞ e₁) (h₂ : ContDiff ℝ ∞ e₂) (hn : ∀ p, R p + v p ≠ 0) :
    ContDiff ℝ ∞ (fun z : A × ℝ =>
      vectorLoop (e₁ z.1) (e₂ z.1) (R z.1) (v z.1) (a z.1) (z.2 : Period)) := by
  rw [← contDiffOn_univ]
  simpa only [Set.univ_prod_univ] using vectorLoop_family_smoothOn (S := Set.univ)
    hR.contDiffOn hv.contDiffOn ha.contDiffOn h₁.contDiffOn h₂.contDiffOn (fun p _ => hn p)

lemma vectorLoop_eq_of_amplitude_zero (e₁ e₂ : Space) {R v a : ℝ}
    (hR : 0 < R) (hv : 0 < v) (hquad : R ^ 2 = v ^ 2 + a ^ 2) (ha : a = 0)
    (t : Period) : vectorLoop e₁ e₂ R v a t = v • e₁ := by
  have hRv : R = v := by nlinarith
  rw [ha, vectorLoop_zero_amplitude, hRv]

/-- Every spatial derivative vanishes on the boundary of a zero-amplitude region. -/
theorem collar_flatness
    (hR : ContDiff ℝ ∞ R) (hv : ContDiff ℝ ∞ v) (ha : ContDiff ℝ ∞ a)
    (h₁ : ContDiff ℝ ∞ e₁) (h₂ : ContDiff ℝ ∞ e₂)
    (hRp : ∀ p, 0 < R p) (hvp : ∀ p, 0 < v p)
    (hq : ∀ p, R p ^ 2 = v p ^ 2 + a p ^ 2)
    {O : Set A} (hO : IsOpen O) (hz : ∀ p ∈ O, a p = 0) (t : ℝ) (n : ℕ) :
    Set.EqOn (iteratedFDeriv ℝ n (fun p =>
      vectorLoop (e₁ p) (e₂ p) (R p) (v p) (a p) (t : Period) - v p • e₁ p))
      (fun _ => 0) (closure O) := by
  have hs := vectorLoop_family_smooth hR hv ha h₁ h₂
    (fun p => (add_pos (hRp p) (hvp p)).ne')
  apply iteratedFDeriv_zero_on_closure
    ((hs.comp (contDiff_id.prodMk contDiff_const)).sub (hv.smul h₁)) hO
  intro p hp
  change vectorLoop (e₁ p) (e₂ p) (R p) (v p) (a p) (t : Period) - v p • e₁ p = 0
  rw [vectorLoop_eq_of_amplitude_zero _ _ (hRp p) (hvp p) (hq p) (hz p hp), sub_self]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
