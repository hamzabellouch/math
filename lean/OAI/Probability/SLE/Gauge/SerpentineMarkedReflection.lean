import OAI.Probability.SLE.Gauge.SerpentineMarkedRouteClearance
import OAI.Probability.SLE.Gauge.RibbonGoodPrefix

namespace OAI

/-! Reflection of the concrete experiment and its actual narrow-prefix
certificate. It reduces a marked point on the left to the right-hand layout. -/

noncomputable section
open Set Metric ComplexConjugate
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

@[simp] lemma fitX_mirror (s : ℝ) (w : ℂ) (m : ℕ) :
    fitX s (loewnerMirror w) m = fitX s w m := by simp [fitX]

@[simp] lemma fitY_mirror (s : ℝ) (w : ℂ) (m : ℕ) :
    fitY s (loewnerMirror w) m = fitY s w m := by simp [fitY]

@[simp] lemma fitChart_mirror (s : ℝ) (w : ℂ) (m : ℕ) (z : ℂ) :
    fitChart s (loewnerMirror w) m z = fitChart s w m z := by
  simp only [fitChart, fitSpine, fitTangent, fitX_mirror, fitY_mirror]

@[simp] lemma physicalFitChart_mirror (s : ℝ) (w : ℂ) (m : ℕ) (z : ℂ) :
    physicalFitChart s (loewnerMirror w) m z = physicalFitChart s w m z := by
  simp only [physicalFitChart, fitChart_mirror]

@[simp] lemma fitEntry_mirror (s : ℝ) (w : ℂ) (m : ℕ) :
    fitEntry s (loewnerMirror w) m = fitEntry s w m := by
  simp only [fitEntry, fitX_mirror, fitY_mirror]

@[simp] lemma fitCompletion_mirror (s : ℝ) (w : ℂ) (m : ℕ) :
    fitCompletion s (loewnerMirror w) m = fitCompletion s w m := by
  simp only [fitCompletion, fitEntry_mirror]

@[simp] lemma fitTerminalX_mirror (s : ℝ) (w : ℂ) :
    fitTerminalX s (loewnerMirror w) = fitTerminalX s w := by simp [fitTerminalX]

@[simp] lemma fitTerminalHeight_mirror (s : ℝ) (w : ℂ) (m : ℕ) :
    fitTerminalHeight s (loewnerMirror w) m = fitTerminalHeight s w m := by
  simp only [fitTerminalHeight, fitY_mirror, fitCompletion_mirror, fitEntry_mirror]

@[simp] lemma fitHighTime_mirror (s : ℝ) (w : ℂ) (m : ℕ) :
    fitHighTime s (loewnerMirror w) m = fitHighTime s w m := by
  simp only [fitHighTime, fitTerminalHeight_mirror]

lemma physicalExperimentChart_negative {s : ℝ} {w : ℂ} (hw : w.re < 0) (m : ℕ) :
    physicalExperimentChart s w m = reflectedChart (physicalFitChart s (loewnerMirror w) m) := by
  funext z
  simp only [physicalExperimentChart, ite_eq_right (not_le_of_gt hw), reflectedChart,
    physicalFitChart_mirror]

lemma experimentChart_negative {s : ℝ} {w : ℂ} (hw : w.re < 0) (m : ℕ) :
    experimentChart s w m = reflectedChart (fitChart s (loewnerMirror w) m) := by
  funext z
  simp only [experimentChart, ite_eq_right (not_le_of_gt hw), reflectedChart, fitChart_mirror]

lemma ribbonCore_reflected_iff (P : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    z ∈ ribbonCore (reflectedChart P) ε ↔ loewnerMirror z ∈ ribbonCore P ε := by
  constructor
  · rintro ⟨u, ⟨hu, hε⟩, he⟩
    refine ⟨conj u, ⟨conj_mem_closedRibbon hu, ?_⟩, ?_⟩
    · simpa only [Complex.conj_im, abs_neg] using hε
    · rw [← he]
      simp only [reflectedChart, loewnerMirror_twice]
  · rintro ⟨u, ⟨hu, hε⟩, he⟩
    refine ⟨conj u, ⟨conj_mem_closedRibbon hu, ?_⟩, ?_⟩
    · simpa only [Complex.conj_im, abs_neg] using hε
    · simpa only [reflectedChart, Complex.conj_conj, loewnerMirror_twice] using
        congrArg loewnerMirror he

lemma goodRibbonPrefix_reflected {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (τ : Ω → WithTop ℝ≥0) (P : ℂ → ℂ) (ε : ℝ) :
    GoodRibbonPrefix γ τ (reflectedChart P) ε =
      GoodRibbonPrefix (fun ω t => loewnerMirror (γ ω t)) τ P ε := by
  ext ω
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · rintro ⟨hτ, hp, he⟩
    exact ⟨hτ, fun t ht => (ribbonCore_reflected_iff P ε _).mp (hp ht),
      (ribbonCore_reflected_iff P (ε / 4) _).mp he⟩
  · rintro ⟨hτ, hp, he⟩
    exact ⟨hτ, fun t ht => (ribbonCore_reflected_iff P ε _).mpr (hp ht),
      (ribbonCore_reflected_iff P (ε / 4) _).mpr he⟩

lemma goodRibbonPrefix_physical_negative {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (τ : Ω → WithTop ℝ≥0) {s : ℝ} {w : ℂ} (hw : w.re < 0) (m : ℕ) (ε : ℝ) :
    GoodRibbonPrefix γ τ (physicalExperimentChart s w m) ε =
      GoodRibbonPrefix (fun ω t => loewnerMirror (γ ω t)) τ
        (physicalFitChart s (loewnerMirror w) m) ε := by
  rw [physicalExperimentChart_negative hw m]
  exact goodRibbonPrefix_reflected γ τ _ ε

lemma physicalExperimentChart_reflect_point {s : ℝ} {w : ℂ} (hw : w.re < 0)
    (m : ℕ) (z : ℂ) :
    loewnerMirror (physicalExperimentChart s w m z) =
      physicalFitChart s (loewnerMirror w) m (conj z) := by
  rw [physicalExperimentChart_negative hw m]
  simp only [reflectedChart, loewnerMirror_twice]

def mirroredProgress (g : C(ℂ, ℝ)) : C(ℂ, ℝ) :=
  ⟨fun z => g (loewnerMirror z), g.continuous.comp loewnerMirror.continuous⟩

lemma mirroredProgress_trace (g : C(ℂ, ℝ)) (γ : ℝ≥0 → ℂ) (t : ℝ≥0) :
    mirroredProgress g ((loewnerMirror ∘ γ) t) = g (γ t) := by
  simp [mirroredProgress]

lemma mirroredProgress_chart (g : C(ℂ, ℝ)) (P : ℂ → ℂ)
    (hg : ∀ z ∈ closedRibbon, g (P z) = z.re) :
    ∀ z ∈ closedRibbon, mirroredProgress g (reflectedChart P z) = z.re := by
  intro z hz
  change g (loewnerMirror (loewnerMirror (P (conj z)))) = z.re
  rw [loewnerMirror_twice]
  simpa only [Complex.conj_re] using hg (conj z) (conj_mem_closedRibbon hz)

lemma mirroredProgress_firstFrontTime (g : C(ℂ, ℝ)) (γ : ℝ≥0 → ℂ) (k : ℝ) :
    FirstFrontPassage.firstFrontTime (fun t => mirroredProgress g ((loewnerMirror ∘ γ) t)) k =
      FirstFrontPassage.firstFrontTime (fun t => g (γ t)) k := by
  congr 1
  funext t
  exact mirroredProgress_trace g γ t

end SLEExactGauge.Serpentine

end

end OAI
