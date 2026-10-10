import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotInitial
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions

namespace OAI

section

/-! # Spatial covariance of clipped cold limits and dominated representatives -/

noncomputable section

open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedColdPicard_pull (q b L T : ℝ) (y : JetPrototype.Space)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : JetPrototype.Phase → ℝ) (n : ℕ) :
    clippedColdPicard q b L T (pull y F) (fun p => c₀ (shift y p)) n =
      pull y (clippedColdPicard q b L T F c₀ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [clippedColdPicard,ih,coldForcing_pull,value_pull,pull]
    rfl

theorem clippedColdLimit_pull (q b L T : ℝ) (y : JetPrototype.Space)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : JetPrototype.Phase → ℝ) :
    clippedColdLimit q b L T (pull y F) (fun p => c₀ (shift y p)) =
      pull y (clippedColdLimit q b L T F c₀) := by
  funext u
  simp only [clippedColdLimit,clippedColdPicard_pull,pull]

theorem normalizedFamily_reindex {I : Type*} (e : I ≃ I)
    (F : ℝ × JetPrototype.Phase → ℝ) (c : I → ℝ × JetPrototype.Phase → ℝ) (i : I) :
    normalizedFamily F (fun j => c (e j)) i = normalizedFamily F c (e i) := by
  classical
  funext u
  have he : (∀ s : Finset I, (∑ j ∈ s, c (e j) u) ≤ F u) ↔
      ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u := by
    constructor
    · intro h s
      simpa only [Finset.sum_map,Equiv.coe_toEmbedding,Equiv.apply_symm_apply] using
        h (s.map e.symm.toEmbedding)
    · intro h s
      simpa only [Finset.sum_map,Equiv.coe_toEmbedding] using h (s.map e.toEmbedding)
  simp only [normalizedFamily,he]

theorem rebuiltColdFamily_pull {I : Type*} (q b L T : ℝ) (y : JetPrototype.Space)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : I → JetPrototype.Phase → ℝ) (i : I) :
    rebuiltColdFamily q b L T (pull y F) (fun j p => c₀ j (shift y p)) i =
      pull y (rebuiltColdFamily q b L T F c₀ i) := by
  unfold rebuiltColdFamily
  simp only [clippedColdLimit_pull]
  rfl

theorem rebuiltColdFamily_reindex {I : Type*} (e : I ≃ I) (q b L T : ℝ)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : I → JetPrototype.Phase → ℝ) (i : I) :
    rebuiltColdFamily q b L T F (fun j => c₀ (e j)) i =
      rebuiltColdFamily q b L T F c₀ (e i) :=
  normalizedFamily_reindex e F (fun j => clippedColdLimit q b L T F (c₀ j)) i

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Time clamping of the reconstructed cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedColdPicard_time_clamp {T : ℝ} (hT : 0 ≤ T) (q b L : ℝ)
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (c₀ : JetPrototype.Phase → ℝ) (n : ℕ) (u : ℝ × JetPrototype.Phase) :
    clippedColdPicard q b L T F c₀ n (PositiveIntegral.time T u.1,u.2) =
      clippedColdPicard q b L T F c₀ n u := by
  cases n with
  | zero => rfl
  | succ n =>
    change min (F (PositiveIntegral.time T u.1,u.2)) _ = min (F u) _
    rw [hF u,PositiveIntegral.value_time_clamp hT]

theorem clippedColdLimit_time_clamp {T : ℝ} (hT : 0 ≤ T) (q b L : ℝ)
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (c₀ : JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    clippedColdLimit q b L T F c₀ (PositiveIntegral.time T u.1,u.2) =
      clippedColdLimit q b L T F c₀ u := by
  unfold clippedColdLimit
  simp only [clippedColdPicard_time_clamp hT q b L hF]

theorem rebuiltColdFamily_time_clamp {I : Type*} {T : ℝ} (hT : 0 ≤ T) (q b L : ℝ)
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (c₀ : I → JetPrototype.Phase → ℝ) (i : I) (u : ℝ × JetPrototype.Phase) :
    rebuiltColdFamily q b L T F c₀ i (PositiveIntegral.time T u.1,u.2) =
      rebuiltColdFamily q b L T F c₀ i u := by
  classical
  simp only [rebuiltColdFamily,normalizedFamily,hF,
    clippedColdLimit_time_clamp hT q b L hF]

theorem mild_all_of_time_clamp {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    {f : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {g : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ u, f (PositiveIntegral.time T u.1,u.2) = f u)
    (he : ∀ t ∈ Set.Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ t, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) := by
  intro t
  filter_upwards [he (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)] with p hp
  rw [hf (t,p)] at hp
  exact hp.trans (PositiveIntegral.value_time_clamp hT L f₀ g (t,p))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
