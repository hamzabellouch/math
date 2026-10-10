import OAI.Probability.InvariantIsing.Cavity.CavityRotationVectors
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinNumerator

namespace OAI

/-! The actual base-model group vectors satisfy the size bound required
by logarithmic coefficient replacement. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_rotation_vectors_norm_bound {N m depth : ℕ} (hN : 0<N)
    (dims : Fin m → ℕ) (hgroups : ∀ a, 0<dims a)
    (E : ((a : Fin m) × Fin (dims a)) ≃ Fin N)
    {c : ℝ} (hc : 0<c) (hfrac : ∀ a, c ≤ (dims a : ℝ)/N)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ))
    (x : Spin N × LabeledLeaf depth) :
    ∀ a, ‖(WithLp.toLp 2 (cavityRotationVectors dims E p a x) :
      EuclideanSpace ℝ (Fin (dims a)))‖^2 ≤ (1/c)*dims a := by
  have h := cavityRotationVectors_gram_bound (r := 1) hN dims E
    (p,fun _ => x) hc hfrac
  exact cavity_group_gram_diagonal_norm hgroups
    (fun a => cavityRotationVectors dims E p a x) (fun a => h a 0 0)

end InvariantIsing

end

end OAI
