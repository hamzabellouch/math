import OAI.Geometry.SurfaceImmersion.Correction.PolynomialChartedMeanFamily
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanIteration

namespace OAI

/-! Assemble the actual finite metric mean from one common bound on its
seven local budgets. The envelope records the derivative shift explicitly. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

def meanGeometryEnvelope (q : ℕ) (H B : ℕ → ℝ) (m : ℕ) : ℝ :=
  1+H m+B (m+q+2)+B m

lemma meanGeometryEnvelope_growth (q : ℕ) (H B : ℕ → ℝ → ℝ)
    (hH : ∀ m, HasPolynomialBound (H m)) (hB : ∀ m, HasPolynomialBound (B m))
    (m : ℕ) : HasPolynomialBound (fun x =>
      meanGeometryEnvelope q (fun k => H k x) (fun k => B k x) m) :=
  (((polynomialBound_const zero_le_one).add (hH m)).add (hB (m+q+2))).add (hB m)

theorem polynomial_mean_family_from_budgets (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {ι : Type*} [Fintype ι] {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
      {K : ι → Compacts Base} {s : ℝ≥0}
      (c : ∀ i, PolynomialSolveData P 0 G hG (φ i) (K i) τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ H B : ℕ → ℝ, (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ B m) →
      (∀ m, (Fintype.card ι : ℝ) ≤ H m ∧ ρ⁻¹ ≤ H m) →
      (∀ i m, (d i).budgets.inv m ≤ B m ∧ (d i).budgets.chi m ≤ B m ∧
        (d i).budgets.forms m ≤ B m ∧ (d i).budgets.pull m ≤ B m ∧
        (d i).budgets.psi m ≤ B m ∧ (d i).budgets.normal m ≤ B m ∧
        (d i).budgets.mode m ≤ B m) →
      ∀ δ : ℝ, 0 < δ → MeanBounds univ s reference r (q+2)
        (rescaledMean (τ/s) (chartedFamilyMean d hρ δ q))
        (polynomialMeanProfile p C (meanGeometryEnvelope q H B))
        (polynomialMeanProfile p C (meanGeometryEnvelope q H B)) := by
  obtain ⟨p,C,hC,hmean⟩ := polynomial_charted_metric_mean_family q
  refine ⟨p,C,hC,?_⟩
  intro ι _ n P τ G hG φ K s c r ρ R reference d hρ hτ hs hτs hs1 H B hH hB hHB hb δ hδ
  have henv (m : ℕ) : 1 ≤ meanGeometryEnvelope q H B m ∧
      H m ≤ meanGeometryEnvelope q H B m ∧
      B (m+q+2) ≤ meanGeometryEnvelope q H B m ∧
      B m ≤ meanGeometryEnvelope q H B m := by
    dsimp [meanGeometryEnvelope]
    have h₀ := hB m
    have h₁ := hB (m+q+2)
    have h₂ := hH m
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  apply hmean c d hρ hτ hs hτs hs1 (meanGeometryEnvelope q H B)
    (fun m => (henv m).1) (fun m => (hHB m).1.trans (henv m).2.1) _ δ hδ
  intro i m
  obtain ⟨hi,hχ,hQ,hpull,hψ,hn,hm⟩ := hb i (m+q+2)
  obtain ⟨_,hχ₀,_,hpull₀,_,_,_⟩ := hb i m
  exact ⟨(hHB m).2.trans (henv m).2.1,
    hi.trans (henv m).2.2.1,hQ.trans (henv m).2.2.1,
    hψ.trans (henv m).2.2.1,hm.trans (henv m).2.2.1,
    hn.trans (henv m).2.2.1,hχ₀.trans (henv m).2.2.2,hpull₀.trans (henv m).2.2.2⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
