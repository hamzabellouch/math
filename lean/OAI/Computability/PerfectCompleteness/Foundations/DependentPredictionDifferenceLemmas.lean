import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.DependentPredictionDifference

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

variable {O : Type*}

abbrev Sample (Ω A : O → Type*) := (o : O) × (Ω o × A o)

abbrev Observation (P A : O → Type*) := (o : O) × (P o × A o)

variable [Fintype O] {Ω P A : O → Type*}
  [∀ o, Fintype (Ω o)] [∀ o, Fintype (P o)] [∀ o, Fintype (A o)]

def law (outer : FiniteDistribution O)
    (original : ∀ o, FiniteDistribution (Ω o))
    (advice : ∀ o, FiniteDistribution (A o)) : FiniteDistribution (Sample Ω A) :=
  CompletionSoundness.sigmaLaw outer (fun o => (original o).product (advice o))

def observe (p : ∀ o, Ω o → P o) (x : Sample Ω A) : Observation P A :=
  ⟨x.1, (p x.1 x.2.1, x.2.2)⟩

theorem original_usefulness_predicts
    (outer : FiniteDistribution O)
    (original : ∀ o, FiniteDistribution (Ω o))
    (advice : ∀ o, FiniteDistribution (A o))
    (p : ∀ o, Ω o → P o) (lower : ∀ o, Ω o → Bool)
    (I : Observation P A → Bool) (prediction : Sample Ω A → Bool) (κ : ℝ)
    (hmarked : ∀ o z a, I ⟨o, (z, a)⟩ = true →
      UsefulMark.useful (original o) (p o) (lower o) κ z = true)
    (hprediction : ∀ o x a, lower o x = true → I ⟨o, (p o x, a)⟩ = true →
      prediction ⟨o, (x, a)⟩ = true) :
    κ * (law outer original advice).probability (fun x => I (observe p x)) ≤
      (law outer original advice).probability prediction := by
  unfold law
  rw [CompletionSoundness.sigmaLaw_probability, CompletionSoundness.sigmaLaw_probability,
    ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro o
  exact UsefulAdvice.independent_advice_predicts (original o) (advice o) (p o) (lower o) κ
    (fun z => I ⟨o, z⟩) (fun x => prediction ⟨o, x⟩) (hmarked o) (hprediction o)

theorem of_original_usefulness {Γ : Type*} [Fintype Γ]
    (outer : FiniteDistribution O)
    (original : ∀ o, FiniteDistribution (Ω o))
    (advice : ∀ o, FiniteDistribution (A o))
    (reference : FiniteDistribution Γ)
    (p : ∀ o, Ω o → P o) (referenceObserve : Γ → Observation P A)
    (lower : ∀ o, Ω o → Bool)
    (I J : Observation P A → Bool) (prediction : Sample Ω A → Bool)
    (κ ρ q₀ v : ℝ) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq₀ : 0 ≤ q₀) (hv : 0 ≤ v) (hsmall : v ≤ ρ * q₀ / 16)
    (hmarked : ∀ o z a, I ⟨o, (z, a)⟩ = true →
      UsefulMark.useful (original o) (p o) (lower o) κ z = true)
    (hprediction : ∀ o x a, lower o x = true → I ⟨o, (p o x, a)⟩ = true →
      prediction ⟨o, (x, a)⟩ = true)
    (hvariation : ((law outer original advice).pushforward (observe p)).totalVariation
      (reference.pushforward referenceObserve) ≤ v)
    (hmass : q₀ ≤ reference.probability (fun x => J (referenceObserve x)))
    (hdensity : ρ * reference.probability (fun x => J (referenceObserve x)) ≤
      reference.probability (fun x => I (referenceObserve x))) :
    κ * ρ * q₀ / 4 ≤ (law outer original advice).probability prediction -
      (κ * ρ / 4) * (law outer original advice).probability (fun x => J (observe p x)) := by
  apply PredictionDifference.of_observed_variation
    (law outer original advice) reference (observe p) referenceObserve I J prediction
    κ ρ q₀ v hκ hρ hρ1 hq₀ hv hsmall hvariation hmass hdensity
  exact original_usefulness_predicts outer original advice p lower I prediction κ
    hmarked hprediction

end
end PerfectCompleteness.DependentPredictionDifference


namespace PerfectCompleteness.LegalEnumeration

open scoped Classical
open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

section Reindex
variable {E E' Q₁ Q₂ Q₁' Q₂' : Type*}
  {L : Q₁ → Type*} {R : Q₂ → Type*}
  {L' : Q₁' → Type*} {R' : Q₂' → Type*}
  [Fintype E] [Fintype E']
  (G : LegalProjectionGame E Q₁ Q₂ L R)
  (ee : E ≃ E') (el : Q₁ ≃ Q₁') (er : Q₂ ≃ Q₂')
  (al : ∀ x, L x ≃ L' (el x)) (ar : ∀ y, R y ≃ R' (er y))

def reindex : LegalProjectionGame E' Q₁' Q₂' L' R' where
  occurrences := G.occurrences.transport ee
  left i := el (G.left (ee.symm i))
  right i := er (G.right (ee.symm i))
  projection i a := ar (G.right (ee.symm i))
    (G.projection (ee.symm i) ((al (G.left (ee.symm i))).symm a))

def strategies : LegalStrategy L R ≃ LegalStrategy L' R' :=
  (el.piCongr al).prodCongr (er.piCongr ar)

theorem reindex_wins (s : LegalStrategy L R) (e : E) :
    (reindex G ee el er al ar).wins (strategies el er al ar s) (ee e) = G.wins s e := by
  simp only [LegalProjectionGame.wins, reindex]
  apply decide_eq_decide.mpr
  change ar (G.right (ee.symm (ee e)))
      (G.projection (ee.symm (ee e))
        ((al (G.left (ee.symm (ee e)))).symm
          ((el.piCongr al) s.1 (el (G.left (ee.symm (ee e))))))) =
        (er.piCongr ar) s.2 (er (G.right (ee.symm (ee e)))) ↔
      G.projection e (s.1 (G.left e)) = s.2 (G.right e)
  rw [ee.symm_apply_apply e]
  rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply, Equiv.symm_apply_apply]
  exact (ar (G.right e)).injective.eq_iff

theorem reindex_success (s : LegalStrategy L R) :
    (reindex G ee el er al ar).success (strategies el er al ar s) = G.success s := by
  unfold LegalProjectionGame.success
  change (G.occurrences.transport ee).probability _ = _
  rw [FiniteDistribution.probability_transport]
  congr 1
  funext e
  exact reindex_wins G ee el er al ar s e

section Fibers
variable [∀ x, Fintype (L x)] [∀ x, Fintype (L' x)]

theorem reindex_fiber_card (i : E')
    (b : R' ((reindex G ee el er al ar).right i)) :
    Fintype.card {a : L' ((reindex G ee el er al ar).left i) //
        (reindex G ee el er al ar).projection i a = b} =
      Fintype.card {a : L (G.left (ee.symm i)) //
        G.projection (ee.symm i) a = (ar (G.right (ee.symm i))).symm b} := by
  apply Fintype.card_congr
  apply (al (G.left (ee.symm i))).symm.subtypeEquiv
  intro a
  change ar (G.right (ee.symm i))
      (G.projection (ee.symm i) ((al (G.left (ee.symm i))).symm a)) = b ↔ _
  constructor
  · intro h
    have h' := congrArg (ar (G.right (ee.symm i))).symm h
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    have h' := congrArg (ar (G.right (ee.symm i))) h
    exact h'.trans ((ar (G.right (ee.symm i))).apply_symm_apply b)

theorem reindex_at_most_two
    (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)
    (i : E') (b : R' ((reindex G ee el er al ar).right i)) :
    Fintype.card {a : L' ((reindex G ee el er al ar).left i) //
      (reindex G ee el er al ar).projection i a = b} ≤ 2 := by
  rw [reindex_fiber_card]
  exact hsmall _ _

end Fibers

variable [Fintype Q₁] [Fintype Q₂] [Fintype Q₁'] [Fintype Q₂']
  [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
  [∀ x, Fintype (L' x)] [∀ y, Fintype (R' y)]
  [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
  [∀ x, Nonempty (L' x)] [∀ y, Nonempty (R' y)]

theorem reindex_value : (reindex G ee el er al ar).value = G.value := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (reindex G ee el er al ar).exists_optimal_strategy
    have h := reindex_success G ee el er al ar ((strategies el er al ar).symm s)
    rw [Equiv.apply_symm_apply] at h
    rw [← hs, h]
    exact G.success_le_value _
  · obtain ⟨s, hs⟩ := G.exists_optimal_strategy
    rw [← hs, ← reindex_success G ee el er al ar s]
    exact (reindex G ee el er al ar).success_le_value _

end Reindex

variable {E Q₁ Q₂ : Type*} [Fintype E] [Fintype Q₁] [Fintype Q₂]
  {L : Q₁ → Type*} {R : Q₂ → Type*}

abbrev NumberedLabels (P : Q₁ → Type*) (i : Fin (Fintype.card Q₁)) :=
  P ((Fintype.equivFin Q₁).symm i)

def numberedLabelEquiv (P : Q₁ → Type*) (x : Q₁) :
    P x ≃ NumberedLabels P (Fintype.equivFin Q₁ x) :=
  Equiv.cast (congrArg P ((Fintype.equivFin Q₁).symm_apply_apply x).symm)

def numbered (G : LegalProjectionGame E Q₁ Q₂ L R) :
    LegalProjectionGame (Fin (Fintype.card E))
      (Fin (Fintype.card Q₁)) (Fin (Fintype.card Q₂))
      (NumberedLabels L) (NumberedLabels R) :=
  reindex G (Fintype.equivFin E) (Fintype.equivFin Q₁) (Fintype.equivFin Q₂)
    (numberedLabelEquiv L) (numberedLabelEquiv R)

theorem numbered_at_most_two [∀ x, Fintype (L x)]
    (G : LegalProjectionGame E Q₁ Q₂ L R)
    (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)
    (i : Fin (Fintype.card E)) (b : NumberedLabels R ((numbered G).right i)) :
    Fintype.card {a : NumberedLabels L ((numbered G).left i) //
      (numbered G).projection i a = b} ≤ 2 :=
  reindex_at_most_two G (Fintype.equivFin E) (Fintype.equivFin Q₁) (Fintype.equivFin Q₂)
    (numberedLabelEquiv L) (numberedLabelEquiv R) hsmall i b

theorem numbered_value [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
    [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
    (G : LegalProjectionGame E Q₁ Q₂ L R) : (numbered G).value = G.value :=
  reindex_value G (Fintype.equivFin E) (Fintype.equivFin Q₁) (Fintype.equivFin Q₂)
    (numberedLabelEquiv L) (numberedLabelEquiv R)

end
end PerfectCompleteness.LegalEnumeration


namespace PerfectCompleteness.SigmaObservation

open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

theorem eq_of_probability_eq {X : Type*} [Fintype X]
    (μ ν : FiniteDistribution X)
    (h : ∀ event : X → Bool, μ.probability event = ν.probability event) : μ = ν := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simpa [FiniteDistribution.probability] using h (fun y => decide (y = x))

theorem pushforward_fiber {S : Type*} [Fintype S] {X Y : S → Type*}
    [∀ s, Fintype (X s)] [∀ s, Fintype (Y s)]
    (μ : FiniteDistribution S) (P : (s : S) → FiniteDistribution (X s))
    (f : (s : S) → X s → Y s) :
    (sigmaLaw μ P).pushforward (fun x => (⟨x.1, f x.1 x.2⟩ : Σ s, Y s)) =
      sigmaLaw μ (fun s => (P s).pushforward (f s)) := by
  apply eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, sigmaLaw_probability, sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro s
  rw [FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.SigmaObservation

end OAI
