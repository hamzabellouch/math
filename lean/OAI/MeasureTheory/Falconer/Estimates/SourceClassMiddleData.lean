import OAI.MeasureTheory.Falconer.Geometry.CellNormalization

namespace OAI

/-! # Actual conditional source data for either middle-interval angular theorem -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem source_class_middle_data (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b K : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hsmall : b*Real.sqrt d ≤ 1/4)
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t M : ℕ} (hpt : p ≤ t) (htN : t ≤ N) (hM : M ≤ t-p)
    {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)) ≤ K) :
    (∀ z ∈ (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p))) ∧
    (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p))) ∧
    (∀ x : Space d, ∀ j : ℕ, j ≤ M →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
        (Metric.ball x ((1/(2:ℝ)^j)/(b*(2:ℝ)^p))) ≤
          ENNReal.ofReal (K*(1/(2:ℝ)^j)^s)) := by
  have hpoint : ∀ z ∈ (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p)) := by
    intro z hz
    simpa only [hP] using cell_normalization_quarter_point Q hQ P hb hsmall hz
  refine ⟨hpoint,ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable hpoint,?_⟩
  exact sourceClass_scaled_dyadic_ball Q hQ μ hN hB hs hE hlam hb hb1 hwidth hlarge
    hp₀ hpt htN hM hP hPpos hinc hcoef

end Falconer.Regularization

end OAI
