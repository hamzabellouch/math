import OAI.MathematicalPhysics.Boltzmann.Approximation.CapEntropyMoments
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage

namespace OAI

/-! # A strong local solution with the full entropy and moment bounds -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem uniform_entropyMoment_of_entropy_inequality {T : ℝ} {f₀ : Density} {F : Evolution}
    (hf₀ : FiniteEntropyDatum f₀) (hf : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (F t))
    (hH : ∀ t ∈ Icc 0 T, ENNReal.ofReal (relativeEntropy (F t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (F s)) ≤ ENNReal.ofReal (relativeEntropy f₀)) :
    ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ z, entropyMoment (F t) z) ≤ C := by
  refine ⟨(1+4*entropyMomentCoefficient)*relativeEntropy f₀+
    4*entropyMomentCoefficient*(∫ z : Phase, entropyGaussian z.2)+
      (∫ z : Phase, maxwellian z.2),?_⟩
  intro t ht
  have hle : ENNReal.ofReal (relativeEntropy (F t)) ≤ ENNReal.ofReal (relativeEntropy f₀) :=
    (le_add_of_nonneg_right zero_le).trans (hH t ht)
  have hreal : relativeEntropy (F t) ≤ relativeEntropy f₀ := by
    have h := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (relativeEntropy f₀) ≠ ⊤) hle
    simpa only [ENNReal.toReal_ofReal (relativeEntropy_nonneg (hf t ht)),
      ENNReal.toReal_ofReal (relativeEntropy_nonneg hf₀)] using h
  refine (entropyMoment_integral_control (hf t ht)).trans ?_
  have ha : 0 ≤ 1+4*entropyMomentCoefficient := by
    nlinarith [entropyMomentCoefficient_nonneg]
  linarith [mul_le_mul_of_nonneg_left hreal ha]

namespace JetCopyDatum

theorem TightCapFamily.exists_entropy_local_solution
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ F : Evolution, LocalMildSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) F ∧
      (∀ t ∈ Icc 0 A.time, FiniteEntropyDatum (F t)) ∧
      (∀ t ∈ Icc 0 A.time, ENNReal.ofReal (relativeEntropy (F t))+
        (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (F s)) ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀))) ∧
      ∃ C : ℝ, ∀ t ∈ Icc 0 A.time, (∫ z, entropyMoment (F t) z) ≤ C := by
  obtain ⟨g,S,hfinite,hH⟩ := A.exists_finite_entropy_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax hq₁ hq₂
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hdatum := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  exact ⟨_,S.localMildSolution A.time_pos hm hdatum.integrable hn,hfinite,hH,
    uniform_entropyMoment_of_entropy_inequality hdatum hfinite hH⟩

end JetCopyDatum
end BoltzmannNonuniqueness

end

end OAI
