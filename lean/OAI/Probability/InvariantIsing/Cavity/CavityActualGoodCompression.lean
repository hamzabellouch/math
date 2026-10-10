import OAI.Probability.InvariantIsing.Cavity.CavityGoodCompression
import OAI.Probability.InvariantIsing.Cavity.CavityOrientation
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionRank

namespace OAI

/-! Good compression events for the actual cavity columns, after the
orientation correction used by the full-model comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_actual_compression_good_probability {n m : ℕ}
    (N : ℕ → ℕ) (hNpos : ∀ k, 0 < N k + n)
    (g : (k : ℕ) → Fin (N k + n) → Fin m)
    (l u : Fin m → ℕ → ℕ)
    (hg : ∀ a k i, g k i = a ↔ l a k ≤ i.val ∧ i.val < u a k)
    (hN : Tendsto (fun k => N k + n) atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k) (hle : ∀ a k, l a k ≤ N k + n)
    (hue : ∀ a k, u a k ≤ N k + n)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 < ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / (N k + n)) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / (N k + n)) atTop (𝓝 (ρu a)))
    (μ : (k : ℕ) → Measure (Orthogonal (N k + n)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant] :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun k =>
      ((μ k).map (cavityOrientationLift (hNpos k))).real {U | ∀ a,
        ‖(CFC.sqrt (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L})
      atTop (𝓝 1) := by
  obtain ⟨L, hL, hlim⟩ := cavityHaarWindow_correction_all (fun k => N k + n)
    l u hN hu hl hlu hle hue ρl ρu hρ
    (fun a => by simpa only [Nat.cast_add] using hρl a)
    (fun a => by simpa only [Nat.cast_add] using hρu a) μ
    (fun k => cavityColumns (1 : Orthogonal (N k + n)))
    (fun _ => cavityColumns_gram _)
  refine ⟨L, hL, hlim.congr fun k => ?_⟩
  rw [cavityOrientationLift_compression_event]
  have hgram (U : Orthogonal (N k + n)) (a : Fin m) :
      cavityCompressionGrams (g k) U a = cavityWindowGram
        ((U : Matrix (Fin (N k + n)) (Fin (N k + n)) ℝ) *
          cavityColumns (1 : Orthogonal (N k + n))) (l a k) (u a k) := by
    rw [cavityCompressionGrams_eq_window (g k) a (l a k) (u a k)
      (hlu a k) (hg a k) U, cavityColumns_eq_mul U]
  have he : {U : Orthogonal (N k + n) | ∀ a,
      ‖(CFC.sqrt (cavityCompressionGrams (g k) U a))⁻¹‖ ≤ L} =
      {U : Orthogonal (N k + n) | ∀ a, ‖(CFC.sqrt (cavityWindowGram
        ((U : Matrix (Fin (N k + n)) (Fin (N k + n)) ℝ) *
          cavityColumns (1 : Orthogonal (N k + n))) (l a k) (u a k)))⁻¹‖ ≤ L} := by
    ext U
    simp only [mem_ofPred_eq, hgram]
  rw [he]

end InvariantIsing

end

end OAI
