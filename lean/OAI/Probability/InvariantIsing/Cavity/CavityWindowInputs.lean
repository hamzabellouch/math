import OAI.Probability.InvariantIsing.Cavity.CavityActualGoodCompression
import OAI.Probability.InvariantIsing.Cavity.CavityActualFactorLimit

namespace OAI

/-! The two probabilistic compression premises follow from the actual
contiguous spectral windows and their positive limiting masses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

def cavityCompressionGoodEvent {N n m : ℕ} (g : Fin (N+n) → Fin m) (L : ℝ) :
    Set (SpecialOrthogonal (N+n)) :=
  {U | ∀ a, ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖ ≤ L}

lemma measurableSet_cavityCompressionGoodEvent {N n m : ℕ}
    (g : Fin (N+n) → Fin m) (L : ℝ) : MeasurableSet (cavityCompressionGoodEvent g L) := by
  have hmO : Measurable (cavitySpecialOrthogonal : SpecialOrthogonal (N+n) → Orthogonal (N+n)) := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe
  have hm a : Measurable (fun U : SpecialOrthogonal (N+n) =>
      ‖(CFC.sqrt (cavityCompressionGrams g (cavitySpecialOrthogonal U) a))⁻¹‖) :=
    ((cavity_matrix_inverse_measurable.comp CFC.measurable_sqrt).norm).comp
      (((measurable_pi_apply a).comp (measurable_cavityCompressionGrams g)).comp hmO)
  simpa only [cavityCompressionGoodEvent, ofPred_forall] using
    MeasurableSet.iInter (fun a => measurableSet_le (hm a) (measurable_const (a := L)))

theorem cavity_window_inputs {m n d : ℕ}
    (es : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose*B₀=1)
    (N : ℕ → ℕ) (hNpos : ∀ r, 0<N r+n) (l w : Fin m → ℕ → ℕ)
    (g : (r : ℕ) → Fin (N r+n) → Fin m)
    (hg : ∀ a r i, g r i=a ↔ l a r ≤ i.val ∧ i.val<w a r)
    (hN : Tendsto (fun r => N r+n) atTop atTop)
    (hw : ∀ a, Tendsto (w a) atTop atTop)
    (hl : ∀ a, (∀ r, l a r=0) ∨ Tendsto (l a) atTop atTop)
    (hlw : ∀ a r, l a r≤w a r) (hle : ∀ a r, l a r≤N r+n)
    (hwe : ∀ a r, w a r≤N r+n)
    (ρl ρw : Fin m → ℝ) (hρ : ∀ a, 0<ρw a-ρl a)
    (hsum : ∑ a, (ρw a-ρl a)=1)
    (hρl : ∀ a, Tendsto (fun r => (l a r : ℝ)/(N r+n)) atTop (𝓝 (ρl a)))
    (hρw : ∀ a, Tendsto (fun r => (w a r : ℝ)/(N r+n)) atTop (𝓝 (ρw a)))
    (hperp : (cavityReindexedStack es (fun a => (ρw a-ρl a) • 1)).transpose*B₀=0)
    (μ : (r : ℕ) → Measure (Orthogonal (N r+n)))
    [∀ r, IsProbabilityMeasure (μ r)] [∀ r, (μ r).IsMulRightInvariant] :
    let ρ := fun a => ρw a-ρl a
    let B := cavityCompressionLimitFrame es B₀
    let A : CavityFactorBlocks d n :=
      (B.transpose*cavityRepeatedSpectrum (n := n) lam*B-Matrix.diagonal (fun j => lam (a₀ j)),
       B.transpose*cavityRepeatedSpectrum (n := n) lam*cavityLimitingStack (n := n) ρ,
       (finiteR ρ lam hρ hsum 0) • 1)
    (∃ L : ℝ, 0<L ∧ Tendsto (fun r =>
      ((μ r).map (cavityOrientationLift (hNpos r))).real (cavityCompressionGoodEvent (g r) L))
      atTop (𝓝 1)) ∧
    (∀ ε>0, Tendsto (fun r => (μ r).real {U | ε<cavityFactorDeviation
      (cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
        (cavityCompressionGrams (g r) U)) A}) atTop (𝓝 0)) := by
  intro ρ B A
  exact ⟨cavity_actual_compression_good_probability N hNpos g l w hg hN hw hl hlw hle hwe
      ρl ρw hρ hρl hρw μ,
    cavity_actual_factor_probability es lam a₀ B₀ hB₀ N l w g hg hN hw hl hlw hle hwe
      ρl ρw hρ hsum hρl hρw hperp μ⟩

end InvariantIsing

end

end OAI
