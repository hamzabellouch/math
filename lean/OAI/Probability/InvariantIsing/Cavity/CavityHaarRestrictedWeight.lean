import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactor

namespace OAI

/-! The bounded restricted factor as a measurable function of the
original disorder, fresh group rotation, base state and cavity spin. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityHaarRestrictedWeight {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) : ℝ :=
  cavityRestrictedFactor K L C T B
    (cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2.1) p.2.2

lemma measurable_cavityHaarRestrictedWeight {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ) :
    Measurable (cavityHaarRestrictedWeight e v A₀ K L C T B) := by
  apply measurable_from_prod_countable_left
  intro x
  have hy : Measurable (fun z : Ω × ((a : Fin m) → Orthogonal (N a)) =>
      cavitySelectedSiteProjection e (v z.1) (cavityGroupHaarFrames A₀ z.2) x.1) :=
    (measurable_cavitySelectedSiteProjection e v hv A₀).comp
      (measurable_id.prodMk (show Measurable (fun _ => x.1) from measurable_const))
  exact measurable_cavityRestrictedFactor_comp K L C T B _ hy (fun _ => x.2) measurable_const

lemma cavityHaarRestrictedWeight_mem {m q d k : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    (e : Fin d → Fin m × Fin q) (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (T B : ℝ)
    (p : (Ω × ((a : Fin m) → Orthogonal (N a))) × (X × Spin k)) :
    cavityHaarRestrictedWeight e v A₀ K L C T B p ∈ Set.Icc 0 (Real.exp T) :=
  cavityRestrictedFactor_mem K L C T B _ _

end InvariantIsing

end

end OAI
