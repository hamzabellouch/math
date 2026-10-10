import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! The actual inverse/forward capacity charts after translating the driver
to zero and applying the positive waypoint dilation. These supply all
analytic chart hypotheses in the joint guide compactness argument. -/

noncomputable section
open Set
open scoped Topology NNReal

namespace SLEExactGauge

def normalizedForward (G : ℂ → ℂ) (u c : ℝ) (z : ℂ) : ℂ :=
  (G z - (u : ℂ)) / (c : ℂ)

def normalizedInverse (F : ℂ → ℂ) (u c : ℝ) (z : ℂ) : ℂ :=
  F ((u : ℂ) + (c : ℂ) * z)

theorem normalized_capacity_charts
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    let g := normalizedForward (G T) (U T) c
    let f := normalizedInverse (F T) (U T) c
    let D := survivingDomain γ T
    DifferentiableOn ℂ f upperHalfPlane ∧ InjOn f upperHalfPlane ∧
      DifferentiableOn ℂ g D ∧ InjOn g D ∧
      MapsTo f upperHalfPlane D ∧ MapsTo g D upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, g (f z) = z) ∧ (∀ z ∈ D, f (g z) = z) := by
  dsimp only
  let A : ℂ → ℂ := fun z => (U T : ℂ) + (c : ℂ) * z
  have hAH : MapsTo A upperHalfPlane upperHalfPlane := by
    intro z hz
    change 0 < (A z).im
    simpa only [A, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, zero_add] using mul_pos hc hz
  have hAD : Differentiable ℂ A := by dsimp [A]; fun_prop
  have hf : DifferentiableOn ℂ (normalizedInverse (F T) (U T) c) upperHalfPlane :=
    (hw.2.2.2.2.1 T).comp hAD.differentiableOn hAH
  have hg : DifferentiableOn ℂ (normalizedForward (G T) (U T) c) (survivingDomain γ T) :=
    ((hw.2.2.2.1 T).sub_const _).div_const _
  have hfD : MapsTo (normalizedInverse (F T) (U T) c) upperHalfPlane (survivingDomain γ T) :=
    (hw.2.2.2.2.2.2.1 T).comp hAH
  have hgH : MapsTo (normalizedForward (G T) (U T) c) (survivingDomain γ T) upperHalfPlane := by
    intro z hz
    change 0 < ((G T z - (U T : ℂ)) / (c : ℂ)).im
    rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact div_pos (hw.2.2.2.2.2.1 T hz) hc
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hgf : ∀ z ∈ upperHalfPlane,
      normalizedForward (G T) (U T) c (normalizedInverse (F T) (U T) c z) = z := by
    intro z hz
    dsimp only [normalizedForward, normalizedInverse]
    rw [hw.2.2.2.2.2.2.2.2.1 T (A z) (hAH hz)]
    dsimp only [A]
    field_simp
    ring
  have hfg : ∀ z ∈ survivingDomain γ T,
      normalizedInverse (F T) (U T) c (normalizedForward (G T) (U T) c z) = z := by
    intro z hz
    dsimp only [normalizedInverse, normalizedForward]
    have he : (U T : ℂ) + (c : ℂ) * ((G T z - (U T : ℂ)) / (c : ℂ)) = G T z := by
      field_simp
      ring
    rw [he, hw.2.2.2.2.2.2.2.1 T z hz]
  have hfi : InjOn (normalizedInverse (F T) (U T) c) upperHalfPlane := by
    intro z hz w hw he
    calc
      z = normalizedForward (G T) (U T) c (normalizedInverse (F T) (U T) c z) := (hgf z hz).symm
      _ = normalizedForward (G T) (U T) c (normalizedInverse (F T) (U T) c w) := congrArg _ he
      _ = w := hgf w hw
  have hgi : InjOn (normalizedForward (G T) (U T) c) (survivingDomain γ T) := by
    intro z hz w hw he
    calc
      z = normalizedInverse (F T) (U T) c (normalizedForward (G T) (U T) c z) := (hfg z hz).symm
      _ = normalizedInverse (F T) (U T) c (normalizedForward (G T) (U T) c w) := congrArg _ he
      _ = w := hfg w hw
  exact ⟨hf, hfi, hg, hgi, hfD, hgH, hgf, hfg⟩

end SLEExactGauge

end

end OAI
