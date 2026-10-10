import OAI.Probability.SLE.Loewner.TargetDriverContinuation
import OAI.Probability.SLE.Mass.CanonicalMassCompensator
import OAI.Probability.SLE.Mass.MassPotentialCompensator

namespace OAI

/-! The exact fresh-driver average in the source's potential difference
is a conditional expectation, including its finite-value convention. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma mesh_eq_compensatorMeshTime (n i : ℕ) :
    (i:ℝ)*mesh n=(compensatorMeshTime n i:ℝ) := by
  simp [compensatorMeshTime,mesh]

lemma potentialDifference_eq_current_sub_condExp
    (κ θ : ℝ) (W : WienerLaw) (hW : IsWiener W) (n i : ℕ)
    (hm : ∀ j, Measurable (fun b => potential κ θ b (compensatorMeshTime n j)))
    (hfin : ∀ j, (∫⁻ b, potential κ θ b (compensatorMeshTime n j) ∂W) ≠ ∞) :
    (fun b => potentialDifference κ θ W b n i) =ᵐ[W]
      (fun b => (potential κ θ b (compensatorMeshTime n i)).toReal -
        condExp (driverFiltration (compensatorMeshTime n i)) W
          (fun b => (potential κ θ b (compensatorMeshTime n (i+1))).toReal) b) := by
  have h := continuationMean_finite_condExp W hW (compensatorMeshTime n i)
    (fun b => potential κ θ b (compensatorMeshTime n (i+1))) (hm (i+1)) (hfin (i+1))
  filter_upwards [ae_lt_top (hm i) (hfin i),h.1,h.2] with b hb hc he
  have hnext : ((i:ℝ)+1)*mesh n=(compensatorMeshTime n (i+1):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using mesh_eq_compensatorMeshTime n (i+1)
  simp only [potentialDifference,mesh_eq_compensatorMeshTime,hnext]
  change (if potential κ θ b (compensatorMeshTime n i)<∞ ∧
      continuationMean W (compensatorMeshTime n i)
        (fun b => potential κ θ b (compensatorMeshTime n (i+1))) b<∞ then _ else _)=_
  rw [ite_eq_left ⟨hb,hc⟩]
  dsimp only [continuationMean] at he
  rw [he]

theorem potentialDifference_eq_mass_increment
    (κ θ : ℝ) (W : WienerLaw) (hW : IsWiener W) (n : ℕ)
    (A : ℕ → Driver → ℝ) (L : Driver → ℝ)
    (hA : StronglyAdapted (compensatorMeshFiltration driverFiltration n) A)
    (hAI : ∀ i, Integrable (A i) W) (hLI : Integrable L W)
    (hm : ∀ i, Measurable (fun b => potential κ θ b (compensatorMeshTime n i)))
    (hfin : ∀ i, (∫⁻ b, potential κ θ b (compensatorMeshTime n i) ∂W) ≠ ∞)
    (hV : ∀ i, (fun b => (potential κ θ b (compensatorMeshTime n i)).toReal) =ᵐ[W]
      W[L-A i|compensatorMeshFiltration driverFiltration n i]) (i : ℕ) :
    (fun b => potentialDifference κ θ W b n i) =ᵐ[W]
      W[A (i+1)-A i|compensatorMeshFiltration driverFiltration n i] := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  exact (potentialDifference_eq_current_sub_condExp κ θ W hW n i hm hfin).trans
    (remainingPotential_increment W (compensatorMeshFiltration driverFiltration n) A
      (fun i b => (potential κ θ b (compensatorMeshTime n i)).toReal) L hA hAI hLI hV i)

end SLEExactGauge.Target

end

end OAI
