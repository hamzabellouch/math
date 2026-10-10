import OAI.Probability.SignedSweeps.TensorAngle
import OAI.Probability.SignedSweeps.HullDensityComparison
import OAI.Probability.SignedSweeps.GroupedCommute
import OAI.Probability.SignedSweeps.EvenBoard

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
local instance (priority := 2000) signedTypeAngleWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) signedTypeAngleSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

theorem signed_word_type_angle {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    {q : ℕ} (hq : 0 < q) (W : Finset (A × B))
    (e : Fin W.card ≃ {x // x ∈ W})
    {kH uH vH : B → ℕ} {kK uK vK : A → ℕ}
    (eH : (Σ j, Fin (kH j)) ≃ Fin W.card)
    (hHroute : ∀ k, (eH.symm k).1 = (e k).1.2)
    (eK : (Σ i, Fin (kK i)) ≃ Fin W.card)
    (hKroute : ∀ k, (eK.symm k).1 = (e k).1.1)
    (hH : ∀ j, uH j+vH j=kH j) (αH : ∀ j, Partition (uH j)) (βH : ∀ j, Partition (vH j))
    (hαH : ∀ j, (αH j).1.colLen 0 ≤ q) (hβH : ∀ j, (βH j).1.colLen 0 ≤ q)
    (hK : ∀ i, uK i+vK i=kK i) (αK : ∀ i, Partition (uK i)) (βK : ∀ i, Partition (vK i))
    (hαK : ∀ i, (αK i).1.colLen 0 ≤ q) (hβK : ∀ i, (βK i).1.colLen 0 ≤ q)
    {u v : ℕ} (h : u+v=W.card) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    ‖(groupedPairTypeProjection (C := Fin q) eH hH αH βH *
      groupedPairTypeProjection (C := Fin q) eK hK αK βK * pairTypeProjection h α β (Fin q)).toContinuousLinearMap‖^2 ≤
      min 1 ((∏ j, pairCarrierCost (Fin q) (αH j) (βH j)) *
        (∏ i, pairCarrierCost (Fin q) (αK i) (βK i)) *
        Real.exp (-signedEntropy α β) * missingCellFactor W) := by
  let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  obtain ⟨M,hM,hMp,hMd⟩ := grouped_even_density_domination (C := Fin q) eH hH αH βH
    (by simpa only [Fintype.card_fin] using hαH) (by simpa only [Fintype.card_fin] using hβH)
  obtain ⟨N,hN,hNp,hNd⟩ := grouped_even_density_domination (C := Fin q) eK hK αK βK
    (by simpa only [Fintype.card_fin] using hαK) (by simpa only [Fintype.card_fin] using hβK)
  apply one_sided_hull_density_comparison
    (groupedPairTypeProjection (C := Fin q) eH hH αH βH) (groupedPairTypeProjection (C := Fin q) eK hK αK βK)
    (pairTypeProjection h α β (Fin q))
    (groupedPairTypeProjection_positive (C := Fin q) eH hH αH βH).isSymmetric
    (groupedPairTypeProjection_idempotent (C := Fin q) eH hH αH βH)
    (groupedPairTypeProjection_positive (C := Fin q) eK hK αK βK).isSymmetric
    (groupedPairTypeProjection_idempotent (C := Fin q) eK hK αK βK)
    (pairTypeProjection_positive h α β (Fin q)).isSymmetric
    (pairTypeProjection_idempotent h α β (Fin q))
    (groupedEvenTensor (C := Fin q) eH) (groupedEvenTensor_positive (C := Fin q) eH)
    (groupedEvenTensor (C := Fin q) eK) (groupedEvenTensor_positive (C := Fin q) eK) M N hM hN
    (fun R => (EvenColorDensity.mean R).tensor W.card)
    (fun R => (EvenColorDensity.mean R).tensor_positive W.card)
    _ (fun R => groupedPairTypeProjection_even_commute (C := Fin q) eK hK αK βK (EvenColorDensity.mean R))
    (fun R => (EvenColorDensity.mean R).tensor_commute h α β)
    (Finset.prod_nonneg (fun j _ => (pairCarrierCost_pos (Fin q) (αH j) (βH j)).le))
    (Finset.prod_nonneg (fun i _ => (pairCarrierCost_pos (Fin q) (αK i) (βK i)).le))
    (Real.exp_pos _).le (missingCellFactor_nonneg W) hMd hNd
    (fun R => (EvenColorDensity.mean R).tensor_entropy_upper h α β hα hβ)
  · intro R S
    simpa only [groupedEvenTensor, hHroute, hKroute] using word_density_cell_bound W e R S
  · intro R
    simpa only [groupedEvenTensor, hHroute] using word_density_right_support W e R

end SignedSweeps
end

end OAI
