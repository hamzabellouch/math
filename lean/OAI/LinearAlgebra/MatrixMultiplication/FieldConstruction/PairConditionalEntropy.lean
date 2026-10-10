import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.PairMarginals

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldPairConditionalEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldPairMarginals
open scoped BigOperators

theorem entropy_sub_eq_conditional_sum
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (q : FiniteLaw B) (m : FiniteLaw C)
    (f : A → C) (g : B → C) (hp : p.map f = m) (hq : q.map g = m) :
    finiteEntropy p.mass - finiteEntropy q.mass =
      ∑ k, m.mass k * (finiteEntropy (p.conditional f k).mass -
        finiteEntropy (q.conditional g k).mass) := by
  rw [p.entropy_eq_map_add_conditional f, q.entropy_eq_map_add_conditional g, hp, hq]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

def stageASplitWeight (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    Fin (below g).length → Fin 17 :=
  fun j => ⟨(below g).get j side,
    Nat.lt_succ_of_le ((below_le (List.get_mem _ _) side).trans
      ((positiveInitial_shape_spec g hg).1 side))⟩

def stageBSplitWeight (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    Fin (below t).length → Fin 17 :=
  fun j => ⟨(below t).get j side,
    Nat.lt_succ_of_le ((below_le (List.get_mem _ _) side).trans
      ((positiveSecond_shape_spec t ht).1 side))⟩

theorem stageASplitLaw_ownWeight_marginal (g : Shape) (hg : g ∈ positiveInitial)
    (side : Fin 3) :
    (stageASplitLaw g hg).map (stageASplitWeight g hg side) =
      stageAMarginalLaw g hg side := rfl

theorem stageBSplitLaw_ownWeight_marginal (t : Shape) (ht : t ∈ positiveSecond)
    (side : Fin 3) :
    (stageBSplitLaw t ht).map (stageBSplitWeight t ht side) =
      stageBMarginalLaw t ht side := rfl

theorem stageA_entropy_sub_pair_eq_conditional_sum
    (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) :
    finiteEntropy (stageASplitLaw g hg).mass -
      finiteEntropy (stageAPairLaw g hg side).mass =
      ∑ k, (stageAMarginalLaw g hg side).mass k *
        (finiteEntropy ((stageASplitLaw g hg).conditional
            (stageASplitWeight g hg side) k).mass -
          finiteEntropy ((stageAPairLaw g hg side).conditional
            (fun ij => halfWeightCode ij.1) k).mass) :=
  entropy_sub_eq_conditional_sum _ _ _ _ _
    (stageASplitLaw_ownWeight_marginal g hg side)
    (stageAPairLaw_leftWeight_marginal g hg side)

theorem stageB_entropy_sub_pair_eq_conditional_sum
    (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) :
    finiteEntropy (stageBSplitLaw t ht).mass -
      finiteEntropy (stageBPairLaw t ht side).mass =
      ∑ k, (stageBMarginalLaw t ht side).mass k *
        (finiteEntropy ((stageBSplitLaw t ht).conditional
            (stageBSplitWeight t ht side) k).mass -
          finiteEntropy ((stageBPairLaw t ht side).conditional
            (fun ij => statisticWeightCode ij.1) k).mass) :=
  entropy_sub_eq_conditional_sum _ _ _ _ _
    (stageBSplitLaw_ownWeight_marginal t ht side)
    (stageBPairLaw_leftWeight_marginal t ht side)

end MatrixMultiplication.AllFieldPairConditionalEntropy

end

end OAI
