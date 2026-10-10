import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BestFallback
import OAI.Combinatorics.KMedianRecovery.Geometry.MetricCost2

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open Completion FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma realCost_le_self (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (xs : List (Finset (Fin n)))
    (hxs : ∀ U∈xs,U.Nonempty) : realCost D (best δ D S xs)≤realCost D S := by
  rw [←BinaryMetricCost.cost_cast δ hδ D S hS,
    ←BinaryMetricCost.cost_cast δ hδ D (best δ D S xs) (best_property δ D S xs Finset.Nonempty hS hxs)]
  exact_mod_cast cost_le_self δ D S xs
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
omit [Fintype Ω] [Nonempty Ω] in
lemma cost_le_reference (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (trial : Ω→Finset (Fin n))
    (htrial : ∀ s,(trial s).Nonempty) (t : ℕ) (seed : Fin t→Ω) :
    realCost D (best δ D S (List.ofFn (fun i=>trial (seed i))))≤
      realCost D (bestWithFallback (realCost D) S trial t seed) := by
  have hxs : ∀ U∈List.ofFn (fun i=>trial (seed i)),U.Nonempty := by
    intro U hU
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
    exact htrial _
  rcases bestWithFallback_mem (realCost D) S trial t seed with h|⟨i,h⟩
  · rw [h]
    exact realCost_le_self δ hδ D S hS _ hxs
  · rw [h]
    exact realCost_le_mem δ hδ D S hS _ hxs _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
lemma amplified (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (trial : Ω→Finset (Fin n))
    (htrial : ∀ s,(trial s).Nonempty) {B M p ζ : ℝ} (hB : 0≤B) (hM : 0≤M)
    (hfall : realCost D S≤M) (hp : 0<p)
    (hsuccess : p≤probability (fun s=>realCost D (trial s)≤B)) (hζ : 0<ζ)
    (t : ℕ) (ht : Real.log (1/ζ)/p≤(t:ℝ)) :
    (∀ seed:Fin t→Ω,realCost D (best δ D S (List.ofFn (fun i:Fin t=>trial (seed i))))≤M) ∧
    1-ζ≤probability (fun seed:Fin t→Ω=>realCost D (best δ D S (List.ofFn (fun i=>trial (seed i))))≤B) ∧
    average (fun seed:Fin t→Ω=>realCost D (best δ D S (List.ofFn (fun i=>trial (seed i)))))≤B+M*ζ := by
  obtain ⟨hh,hprob,hexp⟩:=amplified_output (realCost D) S trial hB hM hfall hp hsuccess hζ t ht
  have hdom:=cost_le_reference δ hδ D S hS trial htrial t
  exact ⟨fun seed=>(hdom seed).trans (hh seed),hprob.trans (probability_mono (fun seed h=>(hdom seed).trans h)),
    (average_mono hdom).trans hexp⟩
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
