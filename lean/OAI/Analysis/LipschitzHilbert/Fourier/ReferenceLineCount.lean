import OAI.Analysis.LipschitzHilbert.Phase.AngularLineCounting
import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceException

namespace OAI

/-! One list-independent angular count and exceptional set per reference top. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

def referenceSlope (R : SlopeBox) (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u (R.referenceChart (p.2, p.1))

theorem measurable_referenceSlope (R : SlopeBox) (u : ℝ × ℝ → ℝ) (hu : Measurable u) :
    Measurable (R.referenceSlope u) :=
  hu.comp (R.referenceChart.measurable.comp measurable_swap)

theorem referenceBinFunction_eq (R : SlopeBox) (u : ℝ × ℝ → ℝ) (c : ℝ)
    {M : ℕ} (b : AngularBins.Bin M) (z : ℝ × ℝ) (x : ℝ) :
    AngularBins.binFunction R.slope c (R.referenceSlope u) b
        ((R.referenceChart.symm z).2, x) =
      (LipschitzHilbert.lineBinSet u R.slope z (AngularBins.enlargedBin R.slope c b)).indicator
        (fun _ => (1 : ℝ)) x := by
  unfold AngularBins.binFunction referenceSlope
  rw [R.referenceChart_linePoint]
  classical
  by_cases h : u (linePoint R.slope z x) ∈ AngularBins.enlargedBin R.slope c b
  · have h' : x ∈ lineBinSet u R.slope z (AngularBins.enlargedBin R.slope c b) := h
    rw [indicator_of_mem h, indicator_of_mem h']
    rfl
  · have h' : x ∉ lineBinSet u R.slope z (AngularBins.enlargedBin R.slope c b) := h
    rw [indicator_of_notMem h, indicator_of_notMem h']

def ReferencePopularCount (R : SlopeBox) (u : ℝ × ℝ → ℝ) (c P θ : ℝ) (M : ℕ)
    (N : ℝ × ℝ → ℝ≥0∞) : Prop :=
  ∀ (p : ℝ × ℝ) (bins : Finset (AngularBins.Bin M)),
    (∀ b ∈ bins, ∃ a d : ℝ, a < d ∧ d - a ≤ 2 * P * R.length ∧ p.2 ∈ Icc a d ∧
      θ * (d - a) ≤ ∫ x in Icc a d,
        AngularBins.binFunction R.slope c (R.referenceSlope u) b (p.1, x)) →
    (bins.card : ℝ≥0∞) ≤ N p

/-- The actual angular bins on a reference line admit a common count and
exponentially small planar exceptional set, independently of any list. -/
theorem reference_count_setup (R : SlopeBox) (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    {M : ℕ} (hM : 0 < M) {c K P θ : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M)
    (hK : 0 ≤ K) (hP : 0 < P) (hθ : 0 < θ) :
    ∃ N : ℝ × ℝ → ℝ≥0∞, Measurable N ∧
      R.ReferencePopularCount u c P θ M N ∧
      ∀ lambda : ℝ, 0 ≤ lambda →
        (volume.prod volume).real (R.referenceException N K lambda) ≤
          384 * K * (K + P) * R.length * R.width *
            Real.exp (-θ * lambda / (240 * (1 + c))) := by
  have hl := R.length_pos
  have hw := R.width_pos
  obtain ⟨N, hN, hpopular, htail⟩ := AngularBins.angular_line_counting R.slope hM hc hcM
    (R.referenceSlope u) (R.measurable_referenceSlope u hu)
    (show 0 < 2 * P * R.length by positivity) hθ
  refine ⟨N, hN, hpopular, ?_⟩
  intro lambda hlambda
  let e := Real.exp (-θ * lambda / (240 * (1 + c)))
  have he : 0 < e := Real.exp_pos _
  have hbound : (volume.prod volume).real (R.referenceException N K lambda) ≤
      (96 * (2 * K * R.length + 2 * P * R.length) * e) * (2 * K * R.width) := by
    apply R.referenceException_measure_bound N hN hK (by positivity)
    intro v _
    have h := htail v (R.x - K * R.length) (R.x + K * R.length)
      (by nlinarith) lambda hlambda
    have heq : R.x + K * R.length - (R.x - K * R.length) = 2 * K * R.length := by ring
    simpa only [witnessInterval, heq] using h
  calc
    _ ≤ _ := hbound
    _ = _ := by dsimp only [e]; ring

end LipschitzHilbert.SlopeBox

end

end OAI
