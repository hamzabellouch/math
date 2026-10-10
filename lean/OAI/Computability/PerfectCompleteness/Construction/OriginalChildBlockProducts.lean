import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlockProducts

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

universe uC uI uΩ uΓ uΔ

theorem transpose_law {C : Type uC} {I : Type uI}
    [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
    {Ω : C → I → Type uΩ} [∀ c i, Fintype (Ω c i)]
    (P : (c : C) → (i : I) → FiniteDistribution (Ω c i)) :
    (FiniteProduct.law (fun c => FiniteProduct.law (P c))).pushforward
        (fun x i c => x c i) =
      FiniteProduct.law (fun i => FiniteProduct.law (fun c => P c i)) := by
  change (FiniteProduct.law (fun c => FiniteProduct.law (P c))).pushforward
      (Equiv.piComm Ω) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ c, ∏ i, (P c i).weight (y i c)) =
    ∏ i, ∏ c, (P c i).weight (y i c)
  exact Finset.prod_comm

def pairEquiv {I : Type uI} (Ω : I → Type uΩ) (Γ : I → Type uΓ) :
    ((i : I) → Ω i) × ((i : I) → Γ i) ≃ ((i : I) → Ω i × Γ i) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem pair_law {I : Type uI} [Fintype I] [DecidableEq I]
    {Ω : I → Type uΩ} {Γ : I → Type uΓ}
    [∀ i, Fintype (Ω i)] [∀ i, Fintype (Γ i)]
    (μ : (i : I) → FiniteDistribution (Ω i))
    (ν : (i : I) → FiniteDistribution (Γ i)) :
    ((FiniteProduct.law μ).product (FiniteProduct.law ν)).pushforward
        (fun z i => (z.1 i, z.2 i)) =
      FiniteProduct.law (fun i => (μ i).product (ν i)) := by
  change ((FiniteProduct.law μ).product (FiniteProduct.law ν)).pushforward
      (pairEquiv Ω Γ) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ i, (μ i).weight (y i).1) * (∏ i, (ν i).weight (y i).2) =
    ∏ i, (μ i).weight (y i).1 * (ν i).weight (y i).2
  exact (Finset.prod_mul_distrib).symm

theorem pair_transport_law {I : Type uI} [Fintype I] [DecidableEq I]
    {Ω : I → Type uΩ} {Γ : I → Type uΓ} {Δ : I → Type uΔ}
    [∀ i, Fintype (Ω i)] [∀ i, Fintype (Γ i)] [∀ i, Fintype (Δ i)]
    (e : (i : I) → Ω i × Γ i ≃ Δ i)
    (μ : (i : I) → FiniteDistribution (Ω i))
    (ν : (i : I) → FiniteDistribution (Γ i)) :
    ((FiniteProduct.law μ).product (FiniteProduct.law ν)).pushforward
        (fun z i => e i (z.1 i, z.2 i)) =
      FiniteProduct.law (fun i => ((μ i).product (ν i)).transport (e i)) := by
  calc
    _ = (((FiniteProduct.law μ).product (FiniteProduct.law ν)).pushforward
          (fun z i => (z.1 i, z.2 i))).pushforward (fun x i => e i (x i)) :=
      (FiniteDistribution.pushforward_comp
        ((FiniteProduct.law μ).product (FiniteProduct.law ν))
        (fun z i => (z.1 i, z.2 i)) (fun x i => e i (x i))).symm
    _ = (FiniteProduct.law (fun i => (μ i).product (ν i))).pushforward
          (fun x i => e i (x i)) :=
      congrArg (fun ρ : FiniteDistribution ((i : I) → Ω i × Γ i) =>
        ρ.pushforward (fun x i => e i (x i))) (pair_law μ ν)
    _ = FiniteProduct.law (fun i => ((μ i).product (ν i)).pushforward (e i)) :=
      FiniteProduct.pushforward_map (fun i => (μ i).product (ν i)) (fun i => e i)
    _ = _ := by
      apply congrArg (fun laws : (i : I) → FiniteDistribution (Δ i) =>
        FiniteProduct.law laws)
      funext i
      exact (FiniteDistribution.transport_eq_pushforward
        ((μ i).product (ν i)) (e i)).symm

theorem merge_law {I : Type uI} [Fintype I] [DecidableEq I]
    {Ω : I → Type uΩ} [∀ i, Fintype (Ω i)]
    (P : (i : I) → FiniteDistribution (Ω i)) (chosen : I) :
    ((P chosen).product (FiniteProductSplit.otherLaw P chosen)).pushforward
        (Equiv.piSplitAt chosen Ω).symm =
      FiniteProduct.law P := by
  rw [← FiniteProductSplit.split_law P chosen, FiniteDistribution.pushforward_comp]
  have hmap : (fun x => (Equiv.piSplitAt chosen Ω).symm
      ((Equiv.piSplitAt chosen Ω) x)) = id := by
    funext x
    exact (Equiv.piSplitAt chosen Ω).symm_apply_apply x
  rw [hmap, FiniteDistribution.pushforward_id]

end
end PerfectCompleteness.OriginalChildBlockProducts

end

end OAI
