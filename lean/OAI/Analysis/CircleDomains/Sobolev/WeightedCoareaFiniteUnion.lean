import OAI.Analysis.CircleDomains.Sobolev.WeightedCoareaUnion

namespace OAI

/-! Disjoint finite assembly of exact weighted scalar coarea. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma weighted_coarea_union {f : ℂ → ℝ} (hf : Continuous f)
    {A B : Set ℂ} (hB : MeasurableSet B) (hd : Disjoint A B) (q : ℂ → ℝ≥0∞)
    (hAco : WeightedScalarCoareaIdentity A f q)
    (hBco : WeightedScalarCoareaIdentity B f q) :
    WeightedScalarCoareaIdentity (A ∪ B) f q := by
  have hsplit : weightedScalarLevelLength (A ∪ B) f q =
      fun t => weightedScalarLevelLength A f q t + weightedScalarLevelLength B f q t := by
    funext t
    unfold weightedScalarLevelLength
    rw [union_inter_distrib_right]
    apply lintegral_union
    · exact hB.inter (measurableSet_eq_fun hf.measurable measurable_const)
    · exact hd.mono inter_subset_left inter_subset_left
  refine ⟨by rw [hsplit]; exact hAco.1.add hBco.1, ?_⟩
  rw [hsplit, lintegral_add_left' hAco.1, hAco.2, hBco.2, lintegral_union hB hd]

end CircleDomainRigidity

end

end OAI
