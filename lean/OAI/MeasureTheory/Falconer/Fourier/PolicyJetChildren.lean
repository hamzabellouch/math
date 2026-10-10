import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphStep
import OAI.MeasureTheory.Falconer.Estimates.PolicyFarStep

namespace OAI

/-! # Actual policy states at the child cells of an angular step -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

def child (P : PolicyJetData m) (p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) : PolicyJetData m where
  Q := P.Q
  unit := P.unit
  ρ := P.ρ
  profile := P.profile
  N := P.N
  s := P.s
  lam := P.lam
  regular := P.regular
  N_pos := P.N_pos
  σ := P.σ
  J := P.J
  i := P.i
  q := P.q
  q_pos := P.q_pos
  policy := P.policy
  a₀ := P.a₀
  t₀ := P.t₀
  a := p
  t := P.t
  base_left := P.base_left.trans hap
  base_right := P.base_right
  base_N := P.base_N
  X := P.X++row.1
  Y := P.Y++row.2
  X_length := by
    rw [List.length_append,P.X_length]
    have hh := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hrow).1).1
    omega
  Y_length := by
    rw [List.length_append,P.Y_length]
    have hh := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hrow).2).1
    omega
  masks := P.masks
  separated := fun b hb => P.separated b
    (PlanarFalconer.remainingPolicyDescriptors_mono P.policy P.N P.q P.a₀ P.t₀ hap hb)
  Z := P.Z
  Z_pos := P.Z_pos

theorem child_envelope (P : PolicyJetData m) (K L p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) (Ψ : ℝ → ℝ) :
    (P.child p hap row hrow).envelope K L Ψ =
      jetStateEnvelope (m+1) K L 1
        (P.list.filter (fun b => p < PlanarFalconer.descriptorAnchor b))
        (P.list.filter (fun b => p < PlanarFalconer.descriptorAnchor b))
        P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z
        (P.ρ.restrict ((P.Q.descendant P.X).descendant row.1).carrier)
        (P.ρ.restrict ((P.Q.descendant P.Y).descendant row.2).carrier)
        (profileModelMass P.profile P.N p) (profileModelMass P.profile P.N p) p P.t Ψ := by
  simp only [envelope,child,list,DyadicCube.descendant_append,
    PlanarFalconer.remainingPolicyDescriptors_drop P.policy P.N P.q P.a₀ P.t₀ hap]

theorem graphChild_le (P : PolicyJetData m) (K L p : ℕ) (hap : P.a ≤ p)
    (Ψ : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hchild : ∀ row, ∀ hrow : row ∈
      (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
      (P.child p hap row hrow).envelope K L Ψ ≤ M) :
    P.graphChild K L p Ψ ≤ M := by
  apply finiteEnvelopeMaximum_le _ _ hM
  intro row hrow
  simpa only [child_envelope] using hchild row hrow

theorem nearBound_eq (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) :
    P.nearBound K L Ψ =
      ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
        ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
          profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          P.graphChild K L P.splitDepth Ψ) := rfl

end PolicyJetData
end Falconer

end OAI
