import OAI.Probability.MatroidSecretary.Secretary.ProbabilityModel
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-!
# Reindexing a secretary rule's complete initial seed

An arbitrary finite predrawn kernel table is represented by a single finite
index. This is a measurable bijection of the complete seed, not a statistic of it.
The rule continues to read only its initial seed and the available history.
-/

open MeasureTheory
namespace MatroidProphet

/-- Reindex a secretary rule through any measurable decoding map. -/
def reindexSecretarySeed {n : ℕ} {Q Q' : Type*}
    [MeasurableSpace Q] [MeasurableSpace Q']
    (A : SecretaryRule n Q) (f : Q' → Q) (hf : Measurable f) : SecretaryRule n Q' where
  prefixLength q := A.prefixLength (f q)
  measurable_prefixLength := A.measurable_prefixLength.comp hf
  decide k q h := A.decide k (f q) h
  measurable_decide k := (A.measurable_decide k).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

/-- Canonical finite-index representation, with no nonemptiness restriction. -/
noncomputable def secretaryFinSeed {n : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] (A : SecretaryRule n Q) :
    SecretaryRule n (Fin (Fintype.card Q)) :=
  reindexSecretarySeed A (Fintype.equivFin Q).symm (measurable_of_finite _)

/-- Push the complete finite seed law forward along the same canonical bijection. -/
noncomputable def secretaryFinSeedLaw {Q : Type*} [Fintype Q] [MeasurableSpace Q]
    (ν : Measure Q) : Measure (Fin (Fintype.card Q)) :=
  ν.map (Fintype.equivFin Q)

/-- Performance against every full-seed-aware suffix adversary, on an arbitrary
ambient probability space. The seed law is fixed before the weight vector. -/
def SecretaryGuarantee.{u} {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (M : Matroid (Fin n)) (A : SecretaryRule n Q) (ν : Measure Q) (c : ℝ) : Prop :=
  ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Q) (σ π : Ω → ArrivalOrder n),
    Measurable R → Measurable σ → Measurable π →
    μ.map R = ν → μ.map σ = Secretary.uniformArrivalLaw n →
    ProbabilityTheory.IndepFun R σ μ →
    (∀ᵐ ω ∂μ, SamePrefix (A.prefixLength (R ω)).val (σ ω) (π ω)) →
    Integrable (fun ω => secretaryReward A (R ω) w (π ω)) μ ∧
      c * optimum M w ≤ ∫ ω, secretaryReward A (R ω) w (π ω) ∂μ

end MatroidProphet

end OAI
