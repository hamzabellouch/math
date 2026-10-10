import OAI.Probability.InvariantIsing.Cavity.CavityHaarNumeratorAverage
import OAI.Probability.InvariantIsing.Cavity.CavityHaarModelNumerator

namespace OAI

/-! Spectral arrays and finite blocks sampled from the same original
Gibbs configurations, with their disorder retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavitySampledEntryArray {m : ℕ} {Ω X : Type*}
    (B : Ω → X → X → SpectralEntry (m + 1)) (p : Ω × (ℕ → X)) :
    SpectralArray (m + 1) := fun ij => B p.1 (p.2 ij.1) (p.2 ij.2)

def cavitySampledGroupBlock {m r : ℕ} {Ω X : Type*}
    (B : Ω → X → X → SpectralEntry (m + 1)) (ω : Ω) (σ : Fin r → X) :
    SpectralBlock m r := fun i j a => B ω (σ i) (σ j) a.castSucc

lemma measurable_cavitySampledEntryArray {m : ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (B : Ω → X → X → SpectralEntry (m + 1))
    (hB : ∀ x y, Measurable (fun ω => B ω x y)) :
    Measurable (cavitySampledEntryArray B) := by
  have hb : Measurable (fun p : Ω × (X × X) => B p.1 p.2.1 p.2.2) := by
    apply measurable_from_prod_countable_left
    intro xy
    exact hB xy.1 xy.2
  apply Measurable.of_eval
  intro ij
  have hp : Measurable (fun p : Ω × (ℕ → X) => (p.1, (p.2 ij.1, p.2 ij.2))) := by fun_prop
  exact hb.comp hp

lemma measurable_cavitySampledGroupBlock {m r : ℕ} {Ω X : Type*}
    [MeasurableSpace Ω]
    (B : Ω → X → X → SpectralEntry (m + 1))
    (hB : ∀ x y, Measurable (fun ω => B ω x y)) (σ : Fin r → X) :
    Measurable (fun ω => cavitySampledGroupBlock B ω σ) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.castSucc).comp (hB (σ i) (σ j))

lemma cavitySampledGroupBlock_prefix {m r : ℕ} {Ω X : Type*}
    (B : Ω → X → X → SpectralEntry (m + 1)) (p : Ω × (ℕ → X)) :
    cavitySpectralGroupBlock m r (cavitySampledEntryArray B p) =
      cavitySampledGroupBlock B p.1 (fun i : Fin r => p.2 i) := rfl

lemma measurable_cavitySampledGroupVectors {m r : ℕ} {N : Fin m → ℕ} {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x)) :
    Measurable (fun p : Ω × (ℕ → X) => fun a (i : Fin r) => v p.1 a (p.2 i)) := by
  have hvj : Measurable (fun p : Ω × X => fun a => v p.1 a p.2) := by
    apply measurable_from_prod_countable_left
    exact hv
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply a).comp hvj).comp
    (measurable_fst.prodMk ((measurable_pi_apply (i : ℕ)).comp measurable_snd))

end InvariantIsing

end

end OAI
