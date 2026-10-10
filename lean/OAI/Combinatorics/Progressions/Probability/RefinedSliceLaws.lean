import OAI.Combinatorics.Progressions.Lattices.ResidueRefinementBudgets

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteCubeSlice

theorem retained_refineResidues_total_pos {q : ℕ} (s : FiniteCubeSlice q) [Nonempty s.Domain]
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (w : (Option (Fin q) → ℤ) → ℝ) {η : ℝ} (hη : 0 < η)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.coordinates x)) η) :
    0 < ∑ x : (s.refineResidues n r).Domain, w ((s.refineResidues n r).coordinates x) :=
  FiniteProbabilityWeights.sum_pos_of_expect_pos _
    (hη.trans_le (s.retained_refineResidues_mean_ge n hdvd r w η hr))

theorem refineResidues_complexMean {q : ℕ} (s : FiniteCubeSlice q)
    (n : Option (Fin q) → ℕ) (hdvd : ∀ i, s.modulus i ∣ n i) (r : s.ResidueLabel n)
    (w : (Option (Fin q) → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hmass : 0 < ∑ x : (s.refineResidues n r).Domain, w ((s.refineResidues n r).coordinates x))
    (f : (Option (Fin q) → ℤ) → ℂ) :
    (FiniteProbabilityWeights.conditionAlongEmbedding (fun x : s.Domain => w (s.coordinates x))
      (fun x => hw (s.coordinates x)) (s.refineResiduesEmbedding n hdvd r) hmass).complexMean
        (fun x => f (s.coordinates x)) =
      (FiniteProbabilityWeights.ofPositiveWeights
        (fun x : (s.refineResidues n r).Domain => w ((s.refineResidues n r).coordinates x))
        (fun x => hw ((s.refineResidues n r).coordinates x)) hmass).complexMean
        (fun x => f ((s.refineResidues n r).coordinates x)) :=
  FiniteProbabilityWeights.conditionAlongEmbedding_complexMean _ _
    (s.refineResiduesEmbedding n hdvd r) hmass _

theorem residueLabelMap_coordinate_mod {q : ℕ} (s : FiniteCubeSlice q)
    (n : Option (Fin q) → ℕ) (M : ℕ) (hM : ∀ i, M ∣ n i) (x : s.Domain) (i : Option (Fin q)) :
    (s.coordinates x i : ZMod M) =
      ZMod.castHom (hM i) (ZMod M) ((s.residueLabelMap n x).val i) := by
  change (s.coordinates x i : ZMod M) =
    ZMod.castHom (hM i) (ZMod M) (s.coordinates x i : ZMod (n i))
  rw [map_intCast]

end FiniteCubeSlice

namespace FiniteCoefficientSlice

theorem retained_refineResidues_total_pos (s : FiniteCoefficientSlice) [Nonempty s.Domain]
    (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (w : ℤ → ℝ) {η : ℝ} (hη : 0 < η)
    (hr : r ∉ (FiniteProbabilityWeights.uniform s.Domain).lowWeightFibers
      (s.residueLabelMap n) (fun x => w (s.value x)) η) :
    0 < ∑ x : (s.refineResidues n r).Domain, w ((s.refineResidues n r).value x) :=
  FiniteProbabilityWeights.sum_pos_of_expect_pos _
    (hη.trans_le (s.retained_refineResidues_mean_ge n hdvd r w η hr))

theorem refineResidues_complexMean (s : FiniteCoefficientSlice)
    (n : ℕ) (hdvd : s.modulus ∣ n) (r : s.ResidueLabel n) (w : ℤ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hmass : 0 < ∑ x : (s.refineResidues n r).Domain, w ((s.refineResidues n r).value x))
    (f : ℤ → ℂ) :
    (FiniteProbabilityWeights.conditionAlongEmbedding (fun x : s.Domain => w (s.value x))
      (fun x => hw (s.value x)) (s.refineResiduesEmbedding n hdvd r) hmass).complexMean
        (fun x => f (s.value x)) =
      (FiniteProbabilityWeights.ofPositiveWeights
        (fun x : (s.refineResidues n r).Domain => w ((s.refineResidues n r).value x))
        (fun x => hw ((s.refineResidues n r).value x)) hmass).complexMean
        (fun x => f ((s.refineResidues n r).value x)) :=
  FiniteProbabilityWeights.conditionAlongEmbedding_complexMean _ _
    (s.refineResiduesEmbedding n hdvd r) hmass _

end FiniteCoefficientSlice

end Erdos3

end

end OAI
