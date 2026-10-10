import OAI.MathematicalPhysics.Boltzmann.Approximation.CapEntropyMoments
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildLocalAdmissibility

namespace OAI

/-! # A fully admissible strong local solution for the actual cold datum -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_admissible_local_solution
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ F : Evolution, AdmissibleLocal A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) F := by
  obtain ⟨g,S,hfinite,hH,hE⟩ := A.exists_entropy_moment_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have hf₀ := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  exact ⟨_,S.localAdmissible A.time_pos hm hn hf₀ hfinite hH hE⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
