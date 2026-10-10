import OAI.Probability.SLE.Multipoint.MultipointPhysicalProbability

namespace OAI

/-! The arbitrary-domain multipoint estimate for an ordinary chordal SLE
in its regular Brownian presentation. The constant is fixed by the order
and SLE parameter before choosing any domain, points, caps or targets. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge

def multipointConstant (κ : ℝ) (m : ℕ) : ℝ :=
  (3 : ℝ)^m * Real.exp (Multipoint.uniformDiscountBudget κ (Multipoint.sourceBeta κ)
    (Finset.univ : Finset (Fin m)))

lemma multipointConstant_pos (κ : ℝ) (m : ℕ) : 0 < multipointConstant κ m := by
  unfold multipointConstant
  positivity

/-- The capped estimate of the first paper's multipoint proposition,
for every fixed finite order and arbitrary physical conformal domain.
The input `PublishedDiskUnivalentGrowth` is Duren (1983), §2.3. -/
theorem RegularSLEPresentation.physical_multipoint_main
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hgrowth : PublishedDiskUnivalentGrowth)
    (m : ℕ) (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane) (z : Fin m → ℂ)
    (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (b e : Fin m → ℝ) (hb : ∀ i, 0 < b i) (he : ∀ i, 0 < e i)
    (hbR : ∀ i, b i ≤ 2*(z i).im*‖deriv J (z i)‖)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (J (z i)) (J (z j))) :
    (P.comap (Subtype.val : a.samples → Ω))
      {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
        physicalConformalRadius J (a.G ω) t (z i) ≤ e i} ≤
      ENNReal.ofReal (multipointConstant κ m * ∏ i, min 1 ((e i/b i)^(1-κ/8))) := by
  have hBm : Measurable (Function.uncurry a.B) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  simpa only [multipointConstant,Fintype.card_fin] using
    Multipoint.capped_physical_radius_multipoint_bound a.brownian a.measurable_B hBm
      a.continuous_B a.zero_B hκ hκ8 (fun ω => γ ω) a.G a.F a.witness hgrowth J hJ hJinj
      z hz hne (fun i => 2*(z i).im*‖deriv J (z i)‖) b e he hb hbR (fun _ => rfl) hsep

end SLEExactGauge

end

end OAI
