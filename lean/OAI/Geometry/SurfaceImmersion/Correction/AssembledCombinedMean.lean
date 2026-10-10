import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanChart
import OAI.Geometry.SurfaceImmersion.Correction.FiniteMeanFamily

namespace OAI

/-! Assemble the actual local mean corrections and perform a finite number
of substitutions with one common scale threshold and derivative loss. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.PhaseMean
open SmallModes WeightedEstimates FiniteMean
variable {ι : Type*} {s r ρ R₀ : ℝ} {reference : Base → Tensor} {n L : ℕ}

def assembledCombinedMean (a : Finset ι) (c : ι → CombinedMeanChart s r ρ R₀ reference n L)
    (hρ : 0 < ρ) (δ τ ε : ℝ) (R : ∀ i, (c i).Operator) (q : ℕ) :
    (Base → Tensor) → Base → Tensor :=
  fun A x => ∑ i ∈ a, (c i).mean hρ δ τ ε (R i) q A x

theorem finite_assembled_combined_mean (a : Finset ι)
    (c : ι → CombinedMeanChart s r ρ R₀ reference n L)
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (q steps : ℕ)
    {H : Base → Tensor} {r₀ : ℝ} (hgap : r₀ < r)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiff ℝ ∞ H)
    (hH0 : ∀ x, ‖H x - reference x‖ ≤ r₀)
    (hbH : ∀ m, WeightedBound Set.univ s m (C m) H) :
    let ℓ := a.sup (fun i => (c i).loss q)
    let p₀ := a.sup (fun i => (c i).exponent)
    ∃ B K : ℕ → ℝ → ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (δ τ ε : ℝ) (p : ℕ), 0 < δ → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      p₀ ≤ p → τ / s + ε / τ ^ p ≤ η₀ →
      ∀ R : ∀ i, (c i).Operator,
      (∀ i ∈ a, (c i).OperatorBound hs τ ε p (R i)) →
      let T := assembledCombinedMean a c hρ δ τ ε R q
      ∀ j ≤ steps, ContDiff ℝ ∞ (fixedTrial H T j) ∧
        InTrialBall Set.univ reference r (fixedTrial H T j) ∧
        (∀ m, WeightedBound Set.univ s m (sizeBound ℓ C B j m) (fixedTrial H T j)) ∧
        (∀ m, WeightedBound Set.univ s m (differenceBound ℓ C B K j m * (τ / s + ε / τ ^ p) ^ (j + 1))
          (fixedTrial H T j + T (fixedTrial H T j) - H)) := by
  classical
  have hex (i : ι) := (c i).majorants hs hs1 hρ q
  choose B K hB using hex
  have hL (i : ι) (hi : i ∈ a) : (c i).loss q ≤ a.sup (fun j => (c j).loss q) := Finset.le_sup (f := fun j => (c j).loss q) hi
  obtain ⟨η₀, hη₀, hη₁, ht⟩ := finite_mean_family isOpen_univ.uniqueDiffOn hs.le hgap a
    (fun i => (c i).loss q) (a.sup (fun i => (c i).loss q)) hL B K hC hH.contDiffOn
    (fun x _ => hH0 x) hbH steps
  refine ⟨(fun m C => 1 + ∑ i ∈ a, B i m C), (fun m C => 1 + ∑ i ∈ a, K i m C), η₀, hη₀, hη₁, ?_⟩
  intro δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR
  have hη : 0 < τ / s + ε / τ ^ p :=
    add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
  have hm (i : ι) (hi : i ∈ a) :
      MeanBounds Set.univ s reference r ((c i).loss q)
        (rescaledMean (τ / s + ε / τ ^ p) ((c i).mean hρ δ τ ε (R i) q)) (B i) (K i) :=
    hB i δ τ ε p hδ hτ hτs hε hε1 ((Finset.le_sup (f := fun j => (c j).exponent) hi).trans hp) (hsmall.trans hη₁) (R i) (hR i hi)
  dsimp only
  intro j hj
  obtain ⟨ha, hb, hc, hd⟩ := ht _ hη hsmall (fun i => (c i).mean hρ δ τ ε (R i) q) hm j hj
  exact ⟨contDiffOn_univ.mp ha, hb, hc, hd⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
