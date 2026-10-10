import OAI.Computability.PerfectCompleteness.Algebra.AffineLinearHeavyWitness
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.TensorBucketEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Algebra.TensorSliceDimension
import OAI.Computability.PerfectCompleteness.Foundations.OutputAnnihilator
import OAI.Computability.PerfectCompleteness.Sampling.OwnLawHeavyList

namespace OAI

section

namespace PerfectCompleteness.TensorAffineHeavyWitness

open scoped TensorProduct Classical
open QuarterBalance (F2)
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]
  [Finite H] [FiniteDimensional F2 H]

local instance dualFintype {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V] :
    Fintype (Module.Dual F2 V) :=
  Fintype.ofInjective (fun f : Module.Dual F2 V => (f : V → F2)) DFunLike.coe_injective

def heavyList (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution (W ⊗[F2] H)) (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (τ : ℝ) (σ : Module.Dual F2 (Fin ℓ → F2)) :
    Finset (Module.Dual F2 (W ⊗[F2] H)) :=
  OwnLawHeavyList.heavyList μ (fun X => QuarterBalance.sign (σ (G X))) τ

omit [FiniteDimensional F2 H] in
theorem heavyList_card_le (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution (W ⊗[F2] H)) (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (τ biasBound : ℝ) (hτ : 0 < τ) (hbiasBound : 0 ≤ biasBound) (hsmall : biasBound ≤ τ ^ 2 / 2)
    (hbias : ∀ Φ : Module.Dual F2 (W ⊗[F2] H), Φ ≠ 0 →
      |μ.expectation (fun X => QuarterBalance.sign (Φ X))| ≤ biasBound)
    (σ : Module.Dual F2 (Fin ℓ → F2)) :
    ((heavyList W μ G τ σ).card : ℝ) ≤ 2 / τ ^ 2 := by
  apply OwnLawHeavyList.heavyList_card_le μ _ τ biasBound hτ hbiasBound hsmall
  · intro X
    exact (OwnLawHeavyList.character_sq σ (G X)).le
  · exact hbias

def conditionalMatch (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution (W ⊗[F2] H)) (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (Q : Submodule F2 (Module.Dual F2 H)) (target : Q →ₗ[F2] W)
    (z : Module.Dual F2 H) (offset : Fin ℓ → F2) : ℝ :=
  AffineLinearHeavyWitness.conditionalMatch μ (TensorRestriction.restrictionMap Q)
    target G (TensorBucketEvaluation.tensorOutputLinear W z) offset

theorem exists_heavy_candidate (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution (W ⊗[F2] H)) (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (ρ h₀ biasBound : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀) (hbiasBound : 0 ≤ biasBound)
    (hsmall : biasBound ≤ h₀ / 2)
    (hbias : ∀ Φ : Module.Dual F2 (W ⊗[F2] H), Φ ≠ 0 →
      |μ.expectation (fun X => QuarterBalance.sign (Φ X))| ≤ biasBound)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 H))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 H) (offset : Fin ℓ → F2)
    (hmatch : ρ ≤ conditionalMatch W μ G Q target z offset) :
    ∃ σ : Module.Dual F2 (Fin ℓ → F2), σ.comp W.subtype ≠ 0 ∧
      ∃ Φ ∈ heavyList W μ G (ρ * h₀ / 4) σ,
        ∀ w : W, σ w = 1 → TensorCosetEvaluation.scalarRestriction Φ w - z ∈ Q := by
  let : Module.Free F2 (Q →ₗ[F2] W) := Module.Free.of_divisionRing F2 (Q →ₗ[F2] W)
  let : Fintype (Module.Dual F2 (W ⊗[F2] H)) :=
    Fintype.ofInjective (fun functional : Module.Dual F2 (W ⊗[F2] H) =>
      (functional : (W ⊗[F2] H) → F2)) DFunLike.coe_injective
  let b := Module.finBasis F2 (Q →ₗ[F2] W)
  let c := Module.finBasis F2 (Fin ℓ → F2)
  have hsize' : h₀ ≤ 1 / (Fintype.card
      (Fin (Module.finrank F2 (Q →ₗ[F2] W)) → Bool) : ℝ) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat] using hsize
  have hbad : ((OutputAnnihilator.bad W).card : ℝ) /
      Fintype.card (Module.Dual F2 (Fin ℓ → F2)) < ρ / 8 := by
    rw [OutputAnnihilator.bad_fraction]
    exact hexcluded
  unfold conditionalMatch at hmatch
  have candidateBasis :=
    AffineLinearHeavyWitness.exists_heavy_in_dual_coset
      (U := W ⊗[F2] H) (V := Q →ₗ[F2] W) (K := Fin ℓ → F2) μ b c
  have candidateRestriction := candidateBasis
      (TensorRestriction.restrictionMap Q)
      (TensorRestriction.restrictionMap_surjective (W := W) Q)
  have candidateData := candidateRestriction
      target G (TensorBucketEvaluation.tensorOutputLinear W z) offset
      (OutputAnnihilator.bad W) ρ h₀ biasBound
  have candidateBounds := candidateData hρ hh₀ hsize' hbiasBound hsmall hbias hbad
  have candidateWitness := candidateBounds hmatch
  obtain ⟨σ, hσ, ψ, hψ, hheavy⟩ := candidateWitness
  refine ⟨σ, (OutputAnnihilator.not_mem_bad_iff W σ).mp hσ,
    σ.comp (TensorBucketEvaluation.tensorOutputLinear W z) + ψ, ?_, ?_⟩
  · simp only [heavyList, OwnLawHeavyList.heavyList, SmallBias.heavySet,
      Finset.mem_filter, Finset.mem_univ, true_and] at hheavy ⊢
    simpa only [OwnLawHeavyList.character, BinaryDualCoordinates.character] using hheavy
  · intro w hw
    have hψ' : TensorCosetEvaluation.scalarRestriction ψ w ∈ Q :=
      TensorCosetEvaluation.scalarRestriction_mem_of_vanishes Q ψ
        (TensorRestriction.dualImage_vanishes Q ψ hψ) w
    rw [TensorTargetCharacter.comp_tensorOutputLinear,
      TensorCosetEvaluation.scalarRestriction_add,
      TensorCosetEvaluation.scalarRestriction_pure]
    have hw' : (σ.comp W.subtype) w = 1 := hw
    rw [hw', one_smul, add_sub_cancel_left]
    exact hψ'

theorem lemma53 (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution (W ⊗[F2] H)) (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (r : Nat) (hcodim : Module.finrank F2 ((Fin ℓ → F2) ⧸ W) ≤ r)
    (ρ biasBound : ℝ) (hρ : 0 < ρ) (hbiasBound : 0 ≤ biasBound)
    (hgap : 1 / (2 : ℝ) ^ (ℓ - r) < ρ / 8)
    (hsmall : biasBound ≤ min ((1 / (2 : ℝ) ^ (r * ℓ)) / 2)
      ((ρ * (1 / (2 : ℝ) ^ (r * ℓ)) / 4) ^ 2 / 2))
    (hbias : ∀ Φ : Module.Dual F2 (W ⊗[F2] H), Φ ≠ 0 →
      |μ.expectation (fun X => QuarterBalance.sign (Φ X))| ≤ biasBound) :
    (∀ σ : Module.Dual F2 (Fin ℓ → F2),
      ((heavyList W μ G (ρ * (1 / (2 : ℝ) ^ (r * ℓ)) / 4) σ).card : ℝ) ≤
        2 / (ρ * (1 / (2 : ℝ) ^ (r * ℓ)) / 4) ^ 2) ∧
    ∀ (Q : Submodule F2 (Module.Dual F2 H)), Module.finrank F2 Q ≤ r →
      ∀ (target : Q →ₗ[F2] W) (z : Module.Dual F2 H) (offset : Fin ℓ → F2),
        ρ ≤ conditionalMatch W μ G Q target z offset →
        ∃ σ : Module.Dual F2 (Fin ℓ → F2), σ.comp W.subtype ≠ 0 ∧
          ∃ Φ ∈ heavyList W μ G (ρ * (1 / (2 : ℝ) ^ (r * ℓ)) / 4) σ,
            ∀ w : W, σ w = 1 →
              TensorCosetEvaluation.scalarRestriction Φ w - z ∈ Q := by
  have hh₀ : 0 < 1 / (2 : ℝ) ^ (r * ℓ) := by positivity
  have hτ : 0 < ρ * (1 / (2 : ℝ) ^ (r * ℓ)) / 4 := by positivity
  have hsmall' := le_min_iff.mp hsmall
  constructor
  · intro σ
    exact heavyList_card_le W μ G _ biasBound hτ hbiasBound hsmall'.2 hbias σ
  · intro Q hQ target z offset hmatch
    have hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8 := by
      rw [← OutputAnnihilator.bad_fraction W]
      apply OutputAnnihilator.bad_fraction_lt_of_codim_le W r ρ hcodim
      simpa only [Module.finrank_fin_fun] using hgap
    have hsize : 1 / (2 : ℝ) ^ (r * ℓ) ≤
        1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W) := by
      simpa only [TensorSliceDimension.mask_card, Nat.cast_pow, Nat.cast_ofNat] using
        TensorSliceDimension.reciprocal_equation_mask_card_ge W Q hQ
    exact exists_heavy_candidate W μ G ρ _ biasBound hρ hh₀ hbiasBound hsmall'.1 hbias hexcluded
      Q hsize target z offset hmatch

end
end PerfectCompleteness.TensorAffineHeavyWitness

end

end OAI
