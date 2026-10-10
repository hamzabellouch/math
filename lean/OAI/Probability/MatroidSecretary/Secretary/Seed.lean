import OAI.Probability.MatroidSecretary.Secretary.SeedModel
import OAI.Probability.MatroidSecretary.Secretary.Specification
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

namespace OAI

/-! Pointwise and probabilistic preservation of the complete secretary seed. -/

open MeasureTheory ProbabilityTheory
namespace MatroidProphet

section Reindex
variable {n : ℕ} {Q Q' : Type*} [MeasurableSpace Q] [MeasurableSpace Q']
    (A : SecretaryRule n Q) (f : Q' → Q) (hf : Measurable f)

@[simp] theorem reindexSecretarySeed_prefixLength (q : Q') :
    (reindexSecretarySeed A f hf).prefixLength q = A.prefixLength (f q) := rfl

@[simp] theorem reindexSecretarySeed_decisionAt (q : Q') (w : Weights n)
    (π : ArrivalOrder n) (k : Fin n) :
    secretaryDecisionAt (reindexSecretarySeed A f hf) q w π k =
      secretaryDecisionAt A (f q) w π k := rfl

@[simp] theorem reindexSecretarySeed_acceptedThrough (q : Q') (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    secretaryAcceptedThrough (reindexSecretarySeed A f hf) q w π t =
      secretaryAcceptedThrough A (f q) w π t := rfl

@[simp] theorem reindexSecretarySeed_reward (q : Q') (w : Weights n)
    (π : ArrivalOrder n) :
    secretaryReward (reindexSecretarySeed A f hf) q w π =
      secretaryReward A (f q) w π := rfl

/-- Feasibility remains pointwise on all seeds, not merely almost everywhere. -/
theorem reindexSecretarySeed_feasible (M : Matroid (Fin n)) (hA : SecretaryFeasible M A) :
    SecretaryFeasible M (reindexSecretarySeed A f hf) := by
  intro q w hw π t
  exact hA (f q) w hw π t

end Reindex

section Finite
variable {n : ℕ} {Q : Type*} [Fintype Q] [MeasurableSpace Q]
    (A : SecretaryRule n Q)

@[simp] theorem secretaryFinSeed_prefixLength (q : Q) :
    (secretaryFinSeed A).prefixLength ((Fintype.equivFin Q) q) = A.prefixLength q := by
  simp [secretaryFinSeed, reindexSecretarySeed]

@[simp] theorem secretaryFinSeed_decisionAt (q : Q) (w : Weights n)
    (π : ArrivalOrder n) (k : Fin n) :
    secretaryDecisionAt (secretaryFinSeed A) ((Fintype.equivFin Q) q) w π k =
      secretaryDecisionAt A q w π k := by
  simp [secretaryFinSeed, reindexSecretarySeed_decisionAt]

@[simp] theorem secretaryFinSeed_acceptedThrough (q : Q) (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    secretaryAcceptedThrough (secretaryFinSeed A) ((Fintype.equivFin Q) q) w π t =
      secretaryAcceptedThrough A q w π t := by
  simp [secretaryFinSeed, reindexSecretarySeed_acceptedThrough]

@[simp] theorem secretaryFinSeed_reward (q : Q) (w : Weights n) (π : ArrivalOrder n) :
    secretaryReward (secretaryFinSeed A) ((Fintype.equivFin Q) q) w π =
      secretaryReward A q w π := by
  simp [secretaryFinSeed, reindexSecretarySeed_reward]

theorem secretaryFinSeed_feasible (M : Matroid (Fin n)) (hA : SecretaryFeasible M A) :
    SecretaryFeasible M (secretaryFinSeed A) :=
  reindexSecretarySeed_feasible A _ _ M hA

variable [MeasurableSingletonClass Q]

instance secretaryFinSeedLaw_isProbability (ν : Measure Q) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (secretaryFinSeedLaw ν) := by
  unfold secretaryFinSeedLaw
  infer_instance

/-- Decoding recovers the full predrawn table law, including every unused entry. -/
theorem secretaryFinSeedLaw_decode (ν : Measure Q) :
    (secretaryFinSeedLaw ν).map (Fintype.equivFin Q).symm = ν := by
  rw [secretaryFinSeedLaw, Measure.map_map (measurable_of_finite _)
    (measurable_of_finite _)]
  simp only [Function.comp_def, Equiv.symm_apply_apply]
  exact Measure.map_id

/-- The law roundtrip holds for an arbitrary externally realized finite seed. -/
theorem secretaryFinSeed_random_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ν : Measure Q) (R : Ω → Fin (Fintype.card Q))
    (hR : Measurable R) (hlaw : μ.map R = secretaryFinSeedLaw ν) :
    μ.map ((Fintype.equivFin Q).symm ∘ R) = ν := by
  rw [← Measure.map_map (measurable_of_finite (Fintype.equivFin Q).symm) hR,
    hlaw, secretaryFinSeedLaw_decode]

/-- Arrival randomization remains independent after the complete-seed bijection. -/
theorem secretaryFinSeed_indepFun_iff {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω)
    (X : Ω → β) (R : Ω → Q) :
    IndepFun X ((Fintype.equivFin Q) ∘ R) μ ↔ IndepFun X R μ := by
  constructor
  · intro h
    have hd := h.comp measurable_id (measurable_of_finite (Fintype.equivFin Q).symm)
    simpa only [Function.comp_def, id_eq, Equiv.symm_apply_apply] using hd
  · intro h
    simpa only [Function.comp_def, id_eq] using
      h.comp measurable_id (measurable_of_finite (Fintype.equivFin Q))

/-- An adversary seeing the finite index can see exactly the original complete seed. -/
theorem secretaryFinSeed_integral (ν : Measure Q) (w : Weights n)
    (π : Fin (Fintype.card Q) → ArrivalOrder n) :
    (∫ q, secretaryReward (secretaryFinSeed A) q w (π q) ∂secretaryFinSeedLaw ν) =
      ∫ q, secretaryReward A q w (π ((Fintype.equivFin Q) q)) ∂ν := by
  rw [secretaryFinSeedLaw]
  have h := integral_map_of_stronglyMeasurable (μ := ν)
    (measurable_of_finite (Fintype.equivFin Q))
    (measurable_of_finite (fun q => secretaryReward (secretaryFinSeed A) q w (π q))).stronglyMeasurable
  simpa only [secretaryFinSeed_reward] using h

/-- Reindexing preserves the complete adversary quantifier, not just orders that
are deterministic functions of the original seed. Additional ambient randomness
is arbitrary and no independence from the executed order is assumed. -/
theorem secretaryFinSeed_guarantee.{u} (M : Matroid (Fin n)) (ν : Measure Q) (c : ℝ)
    (h : SecretaryGuarantee.{u} M A ν c) :
    SecretaryGuarantee.{u} M (secretaryFinSeed A) (secretaryFinSeedLaw ν) c := by
  intro w hw Ω mΩ μ hμ R σ π hR hσ hπ hRlaw hσlaw hind hprefix
  have hd : Measurable (Fintype.equivFin Q).symm := measurable_of_finite _
  have hlaw := secretaryFinSeed_random_law μ ν R hR hRlaw
  have hi : IndepFun ((Fintype.equivFin Q).symm ∘ R) σ μ := by
    simpa only [Function.comp_def, id_eq] using hind.comp hd measurable_id
  have hp : ∀ᵐ ω ∂μ, SamePrefix
      (A.prefixLength ((Fintype.equivFin Q).symm (R ω))).val (σ ω) (π ω) := hprefix
  exact h w hw μ ((Fintype.equivFin Q).symm ∘ R) σ π
    (hd.comp hR) hσ hπ hlaw hσlaw hi hp

/-- A concrete finite-seed construction fills the finite-index existential used
by the public secretary specification, without adding a transport premise there. -/
theorem secretaryFinSeed_witness.{u} (M : Matroid (Fin n)) (ν : Measure Q)
    [IsProbabilityMeasure ν] (c : ℝ) (hA : SecretaryFeasible M A)
    (h : SecretaryGuarantee.{u} M A ν c) :
    ∃ (q : ℕ) (ν' : Measure (Fin q)), IsProbabilityMeasure ν' ∧
      ∃ (A' : SecretaryRule n (Fin q)), SecretaryFeasible M A' ∧
        SecretaryGuarantee.{u} M A' ν' c := by
  refine ⟨Fintype.card Q, secretaryFinSeedLaw ν, inferInstance,
    secretaryFinSeed A, secretaryFinSeed_feasible A M hA, ?_⟩
  exact secretaryFinSeed_guarantee A M ν c h

end Finite

/-- Final packaging of an already constructed family of finite secretary rules.
All probability and adversary obligations are unchanged under seed enumeration. -/
theorem secretaryChallenge_of_finiteRules.{u, v}
    (Q : ℕ → Type v) [∀ n, Fintype (Q n)] [∀ n, MeasurableSpace (Q n)]
    [∀ n, MeasurableSingletonClass (Q n)] (ν : (n : ℕ) → Measure (Q n))
    [∀ n, IsProbabilityMeasure (ν n)]
    (h : ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
      ∃ A : SecretaryRule n (Q n), SecretaryFeasible M A ∧
        SecretaryGuarantee.{u} M A (ν n) (((2 : ℝ) ^ 293)⁻¹)) :
    SecretaryChallenge.{u} := by
  intro n M hE
  obtain ⟨A, hA, hG⟩ := h n M hE
  exact secretaryFinSeed_witness A M (ν n) (((2 : ℝ) ^ 293)⁻¹) hA hG

end MatroidProphet

end OAI
