import OAI.MeasureTheory.Falconer.Recursion.TwoProfileEnergy
import OAI.MeasureTheory.Falconer.Estimates.PolicyRootApplication

namespace OAI

/-! # Separating the exact left and right policy symbols

Each self energy retains its own original regularized measure, descriptor
list, mask family and scalar normalization.
-/

namespace Falconer
open Set MeasureTheory

namespace PolicyJetData
variable {m K L : ℕ}

def diagonal (P : PolicyJetData m) (X : List (Fin (m+3) → Bool))
    (hX : X.length = P.a) : PolicyJetData m :=
  { P with X := X, Y := X, X_length := hX, Y_length := hX }

noncomputable def endpoint (P : PolicyJetData m)
    (X : List (Fin (m+3) → Bool)) (f : DescriptorJetSymbol (m+1) K L P.list 1)
    (z : ℝ × Sphere (m+3)) : ℂ :=
  endpointTransform (P.ρ.restrict (P.Q.descendant X).carrier)
    (profileModelMass P.profile P.N P.a)
    (f.value P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2

theorem endpoint_measurable (P : PolicyJetData m)
    (X : List (Fin (m+3) → Bool)) (f : DescriptorJetSymbol (m+1) K L P.list 1) :
    Measurable (P.endpoint X f) := by
  let := P.regular.probability
  exact measurable_endpointTransform _ _ _
    (f.value_measurable P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z)

noncomputable def endpointBound (P : PolicyJetData m) (K : ℕ)
    (X : List (Fin (m+3) → Bool)) : ℝ :=
  ((descriptorJetBound (m+3) K)^K*P.Z⁻¹)*
    (P.ρ.restrict (P.Q.descendant X).carrier).real univ /
    profileModelMass P.profile P.N P.a

theorem endpointBound_nonneg (P : PolicyJetData m) (K : ℕ)
    (X : List (Fin (m+3) → Bool)) : 0 ≤ P.endpointBound K X := by
  unfold endpointBound profileModelMass
  have hZ := P.Z_pos
  have hB := descriptorJetBound_one_le (m+3) K
  positivity

theorem endpoint_norm_le (P : PolicyJetData m)
    (X : List (Fin (m+3) → Bool)) (f : DescriptorJetSymbol (m+1) K L P.list 1)
    (z : ℝ × Sphere (m+3)) : ‖P.endpoint X f z‖ ≤ P.endpointBound K X := by
  let := P.regular.probability
  exact endpointTransform_norm_le _ (by unfold profileModelMass; positivity) _
    (f.value_norm_le P.Q P.ρ (fun t => P.profile (t/P.N))
      P.N P.σ P.J P.i P.masks P.separated P.Z_pos) z.1 z.2

theorem endpoint_self_energy_le (P : PolicyJetData m)
    (X : List (Fin (m+3) → Bool)) (hX : X.length = P.a)
    (f : DescriptorJetSymbol (m+1) K L P.list 1) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ)] :
    independentAngularEnergy P.a P.t Ψ (P.endpoint X f) (P.endpoint X f) ≤
      (P.diagonal X hX).envelope K L Ψ := by
  let := P.regular.probability
  exact jetStateEnergy_le_envelope P.Q P.ρ (fun t => P.profile (t/P.N))
    P.N P.σ P.J P.i P.masks P.separated P.separated P.Z_pos _ _
    (by unfold profileModelMass; positivity) (by unfold profileModelMass; positivity)
    P.a P.t Ψ f f

end PolicyJetData

theorem two_policy_energy_le {m K L : ℕ} (P Q : PolicyJetData m)
    (ha : P.a = Q.a) (ht : P.t = Q.t)
    (X Y : List (Fin (m+3) → Bool)) (hX : X.length = P.a) (hY : Y.length = Q.a)
    (f : DescriptorJetSymbol (m+1) K L P.list 1)
    (g : DescriptorJetSymbol (m+1) K L Q.list 1) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ)] :
    independentAngularEnergy P.a P.t Ψ (P.endpoint X f) (Q.endpoint Y g) ≤
      Real.sqrt ((P.diagonal X hX).envelope K L Ψ)*
        Real.sqrt ((Q.diagonal Y hY).envelope K L Ψ) := by
  have hfinite : IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure (Q.t:ℝ) Ψ) := by
    rw [← ht]
    infer_instance
  let := hfinite
  have hP := P.endpoint_self_energy_le X hX f Ψ
  have hQ := Q.endpoint_self_energy_le Y hY g Ψ
  rw [← ha,← ht] at hQ
  exact (independentAngularEnergy_le_self_sqrt P.a P.t Ψ _ _
    (P.endpoint_measurable X f) (Q.endpoint_measurable Y g)
    (P.endpointBound_nonneg K X) (Q.endpointBound_nonneg K Y)
    (P.endpoint_norm_le X f) (Q.endpoint_norm_le Y g)).trans
    (mul_le_mul (Real.sqrt_le_sqrt hP) (Real.sqrt_le_sqrt hQ)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Falconer

end OAI
