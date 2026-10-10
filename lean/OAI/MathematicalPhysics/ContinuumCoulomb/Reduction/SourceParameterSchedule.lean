import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SlowLogarithmicExtent

namespace OAI

/-! A simultaneous exponent choice for the actual source construction.
The spatial extent depends on the chosen calibration exponent, but only
through its hundredth; all numerical precisions are chosen afterwards. -/

namespace ContinuumCoulomb

theorem exists_source_exponent_threshold
    (qCloud qNonedge qGap qLeak qScale r s v B : ℕ) :
    ∃ kmin : ℕ, 1100 ≤ kmin ∧ ∀ k : ℕ, kmin ≤ k →
      let extent := s+k/100+13
      let p := 60*B+s+14
      qCloud+9*r+72*extent+v+p ≤ k ∧
      qNonedge+extent+(2*r+p+8) ≤ 5*k ∧
      qGap+2*B+s ≤ k ∧ qLeak ≤ k ∧ qScale ≤ k := by
  let C := qCloud+qNonedge+qGap+qLeak+qScale+9*r+72*(s+13)+v+
    (60*B+s+14)+2*B+8
  refine ⟨4*C+1100,by omega,fun k hk => ?_⟩
  have hC : 4*C ≤ k := by omega
  have hslow := ContactMediator.slow_extent_parameter_closure C k hC
  dsimp only
  dsimp only [C] at hslow
  omega

end ContinuumCoulomb

end OAI
