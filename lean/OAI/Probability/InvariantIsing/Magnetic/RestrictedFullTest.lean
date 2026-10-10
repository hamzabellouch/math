import OAI.Probability.InvariantIsing.Magnetic.RestrictedTreeFullRegular

namespace OAI

/-! The full constrained two-replica test with a rotation-independent observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def restrictedFullTest {N m depth : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (SpecialOrthogonal N)) (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : (Fin 2 → Spin N × LabeledLeaf depth) → ℝ) : ℝ :=
  restrictedCavityFullDisorderTest S hS μ T eig I u (fun _ => F)

end InvariantIsing

end

end OAI
