import OAI.Probability.FreeIsing.Estimates.FairSpin
import OAI.Probability.FreeIsing.Trees.Cardinality

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

lemma freeCylinderWeight_zero_of_card {d : ℕ} (D : Finset (TreeVertex d))
    (hcard : (inducedEdges D).card + 1 = D.card) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight 0 D eta = (1 / 2 : ENNReal) ^ D.card := by
  simp only [freeCylinderWeight, neg_zero, ite_self, add_zero, Finset.prod_const]
  rw [← pow_succ', hcard, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpinFactor_hasFreeIsingLaw_of_card {d : ℕ}
    (hcard : ∀ D : Finset (TreeVertex d), ConnectedFinset D →
      (inducedEdges D).card + 1 = D.card) :
    HasFreeIsingLaw 0 (Measure.map (fairSpinFactor d) (labelMeasure d)) := by
  intro D hD eta
  rw [fairSpinFactor_cylinder, freeCylinderWeight_zero_of_card D (hcard D hD)]

lemma isFactorOfIID_zero_of_card (d : ℕ)
    (hcard : ∀ D : Finset (TreeVertex d), ConnectedFinset D →
      (inducedEdges D).card + 1 = D.card) : IsFactorOfIID d 0 := by
  refine ⟨fairSpinFactor d, measurable_fairSpinFactor d,
    fairSpinFactor_hasFreeIsingLaw_of_card hcard, ?_⟩
  intro g
  exact Filter.Eventually.of_forall (fairSpinFactor_relabel d g)

theorem isFactorOfIID_zero (d : ℕ) : IsFactorOfIID d 0 := by
  exact isFactorOfIID_zero_of_card d (fun _ hD => hD.inducedEdges_card_add_one)

theorem free_ising_factor_beta_zero (d : ℕ) : IsFactorOfIID d (Real.tanh 0) := by
  simpa only [Real.tanh_zero] using isFactorOfIID_zero d

end Problem367

end

end OAI
