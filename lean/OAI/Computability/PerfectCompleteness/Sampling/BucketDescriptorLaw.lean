import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.BucketDescriptorLaw

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

abbrev Buckets (D V : Type*) := D → V

abbrev Record (E D V : Type*) := Σ _ : E, D × (Buckets D V × V)

variable {D E T V : Type*} [Fintype D] [Fintype E] [Fintype T] [Fintype V]

def bucketLaw (D : Type*) [Fintype D] (ρ : FiniteDistribution V) :
    FiniteDistribution (Buckets D V) :=
  FiniteProduct.law (fun _ : D => ρ)

def sampleLaw (δ : FiniteDistribution D) (ρ : FiniteDistribution V) :
    FiniteDistribution (D × (Buckets D V × V)) :=
  δ.product ((bucketLaw D ρ).product ρ)

def observe (read : T → E × Buckets D V) (z : D × (T × V)) : Record E D V :=
  ⟨(read z.2.1).1, (z.1, ((read z.2.1).2, z.2.2))⟩

private def reorder (D E B V : Type*) :
    D × ((E × B) × V) ≃ Σ _ : E, D × (B × V) where
  toFun z := ⟨z.2.1.1, (z.1, (z.2.1.2, z.2.2))⟩
  invFun z := (z.2.1, ((z.1, z.2.2.1), z.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem reorder_law {B : Type*} [Fintype B]
    (δ : FiniteDistribution D) (ν : FiniteDistribution E)
    (κ : FiniteDistribution B) (ρ : FiniteDistribution V) :
    (δ.product ((ν.product κ).product ρ)).pushforward
        (fun z => (⟨z.2.1.1, (z.1, (z.2.1.2, z.2.2))⟩ : Σ _ : E, D × (B × V))) =
      CompletionSoundness.sigmaLaw ν (fun _ => δ.product (κ.product ρ)) := by
  change (δ.product ((ν.product κ).product ρ)).pushforward (reorder D E B V) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change δ.weight z.2.1 * ((ν.weight z.1 * κ.weight z.2.2.1) * ρ.weight z.2.2.2) =
    ν.weight z.1 * (δ.weight z.2.1 * (κ.weight z.2.2.1 * ρ.weight z.2.2.2))
  rw [mul_assoc]
  exact mul_left_comm _ _ _

theorem observe_law (μ : FiniteDistribution T) (ν : FiniteDistribution E)
    (ρ : FiniteDistribution V) (δ : FiniteDistribution D)
    (read : T → E × Buckets D V)
    (hread : μ.pushforward read = ν.product (bucketLaw D ρ)) :
    (δ.product (μ.product ρ)).pushforward (observe read) =
      CompletionSoundness.sigmaLaw ν (fun _ => sampleLaw δ ρ) := by
  have hinner : (μ.product ρ).pushforward (fun z => (read z.1, z.2)) =
      (ν.product (bucketLaw D ρ)).product ρ := by
    simpa only [id_eq, FiniteDistribution.pushforward_id, hread] using
      FiniteDistribution.product_pushforward μ ρ read (id : V → V)
  have houter : (δ.product (μ.product ρ)).pushforward
      (fun z => (z.1, (read z.2.1, z.2.2))) =
      δ.product ((ν.product (bucketLaw D ρ)).product ρ) := by
    simpa only [id_eq, FiniteDistribution.pushforward_id, hinner] using
      FiniteDistribution.product_pushforward δ (μ.product ρ) (id : D → D)
        (fun z : T × V => (read z.1, z.2))
  calc
    _ = ((δ.product (μ.product ρ)).pushforward
        (fun z => (z.1, (read z.2.1, z.2.2)))).pushforward
          (reorder D E (Buckets D V) V) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (δ.product ((ν.product (bucketLaw D ρ)).product ρ)).pushforward
        (reorder D E (Buckets D V) V) :=
      congrArg (fun η : FiniteDistribution (D × ((E × Buckets D V) × V)) =>
        η.pushforward (reorder D E (Buckets D V) V)) houter
    _ = _ := reorder_law δ ν (bucketLaw D ρ) ρ

variable {D' V' : Type*} [Fintype D'] [Fintype V']

def sampleEquiv (eD : D ≃ D') (eV : V ≃ V') :
    (D × (Buckets D V × V)) ≃ (D' × (Buckets D' V' × V')) :=
  Equiv.prodCongr eD (Equiv.prodCongr (Equiv.arrowCongr eD eV) eV)

def recordEquiv (eD : D ≃ D') (eV : V ≃ V') : Record E D V ≃ Record E D' V' :=
  Equiv.sigmaCongrRight (fun _ => sampleEquiv eD eV)

theorem bucketLaw_equiv (ρ : FiniteDistribution V) (eD : D ≃ D') (eV : V ≃ V') :
    (bucketLaw D ρ).pushforward (Equiv.arrowCongr eD eV) =
      bucketLaw D' (ρ.pushforward eV) := by
  rw [← FiniteDistribution.transport_eq_pushforward (bucketLaw D ρ) (Equiv.arrowCongr eD eV),
    ← FiniteDistribution.transport_eq_pushforward ρ eV]
  apply FiniteDistribution.eq_of_weight_eq
  intro buckets
  change (∏ d : D, ρ.weight (eV.symm (buckets (eD d)))) =
    ∏ d : D', ρ.weight (eV.symm (buckets d))
  exact eD.prod_comp (fun d => ρ.weight (eV.symm (buckets d)))

theorem sampleLaw_equiv (δ : FiniteDistribution D) (ρ : FiniteDistribution V)
    (eD : D ≃ D') (eV : V ≃ V') :
    (sampleLaw δ ρ).pushforward (sampleEquiv eD eV) =
      sampleLaw (δ.pushforward eD) (ρ.pushforward eV) := by
  have hinner : ((bucketLaw D ρ).product ρ).pushforward
      (Equiv.prodCongr (Equiv.arrowCongr eD eV) eV) =
      (bucketLaw D' (ρ.pushforward eV)).product (ρ.pushforward eV) := by
    exact (FiniteDistribution.product_pushforward (bucketLaw D ρ) ρ
      (Equiv.arrowCongr eD eV) eV).trans
        (congrArg (fun η : FiniteDistribution (Buckets D' V') => η.product (ρ.pushforward eV))
          (bucketLaw_equiv ρ eD eV))
  exact (FiniteDistribution.product_pushforward δ ((bucketLaw D ρ).product ρ)
    eD (Equiv.prodCongr (Equiv.arrowCongr eD eV) eV)).trans
      (congrArg (fun η : FiniteDistribution (Buckets D' V' × V') =>
        (δ.pushforward eD).product η) hinner)

theorem reference_equiv (ν : FiniteDistribution E) (δ : FiniteDistribution D)
    (ρ : FiniteDistribution V) (eD : D ≃ D') (eV : V ≃ V') :
    (CompletionSoundness.sigmaLaw ν (fun _ => sampleLaw δ ρ)).pushforward
        (recordEquiv (E := E) eD eV) =
      CompletionSoundness.sigmaLaw ν
        (fun _ => sampleLaw (δ.pushforward eD) (ρ.pushforward eV)) := by
  have hmap : (⇑(recordEquiv (E := E) eD eV) : Record E D V → Record E D' V') =
      (fun z => ⟨z.1, sampleEquiv eD eV z.2⟩) := by
    funext z
    cases z
    rfl
  rw [hmap]
  have h := SigmaObservation.pushforward_fiber ν (fun _ => sampleLaw δ ρ)
    (fun _ => ⇑(sampleEquiv eD eV))
  simpa only [sampleLaw_equiv] using h

theorem observe_equiv_law (μ : FiniteDistribution T) (ν : FiniteDistribution E)
    (ρ : FiniteDistribution V) (δ : FiniteDistribution D)
    (read : T → E × Buckets D V)
    (hread : μ.pushforward read = ν.product (bucketLaw D ρ))
    (eD : D ≃ D') (eV : V ≃ V') :
    (δ.product (μ.product ρ)).pushforward
        (fun z => recordEquiv (E := E) eD eV (observe read z)) =
      CompletionSoundness.sigmaLaw ν
        (fun _ => sampleLaw (δ.pushforward eD) (ρ.pushforward eV)) := by
  calc
    _ = ((δ.product (μ.product ρ)).pushforward (observe read)).pushforward
        (recordEquiv (E := E) eD eV) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (CompletionSoundness.sigmaLaw ν (fun _ => sampleLaw δ ρ)).pushforward
        (recordEquiv (E := E) eD eV) :=
      congrArg (fun η : FiniteDistribution (Record E D V) =>
        η.pushforward (recordEquiv (E := E) eD eV)) (observe_law μ ν ρ δ read hread)
    _ = _ := reference_equiv ν δ ρ eD eV

end
end PerfectCompleteness.BucketDescriptorLaw

end

end OAI
