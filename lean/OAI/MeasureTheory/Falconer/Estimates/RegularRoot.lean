import OAI.MeasureTheory.Falconer.Shells.RegularOuterShell
import OAI.MeasureTheory.Falconer.Angular.CapNet

namespace OAI

/-! # Actual regularized classes as initial policy states -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor sourcePolicyBlock sourceSmoothingLevels)

noncomputable def descriptorNets (d N : ℕ) (σ : ℝ) : PolicyDescriptor → Finset (Sphere d) :=
  fun b => Classical.choose (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))

 theorem descriptorNets_cover (d N : ℕ) (σ : ℝ) (b : PolicyDescriptor) (w : Sphere d) :
    ∃ c ∈ descriptorNets d N σ b, dist w c ≤ descriptorMaskRadius N σ b/2 :=
  (Classical.choose_spec (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))).2.1 w

 theorem descriptorNets_separated (d N : ℕ) (σ : ℝ) (b : PolicyDescriptor) :
    ∀ w ∈ descriptorNets d N σ b, ∀ z ∈ descriptorNets d N σ b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z :=
  fun w hw z hz hne =>
    ((Classical.choose_spec (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))).1 w hw z hz hne).le

noncomputable def regularRoot {m N : ℕ} (Q : DyadicCube (m+3)) (hQ : Q.side = 1)
    (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ) {s lam σ κ Z : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile)
    (hN : 0 < N) (hκ : 0 < κ) (hZ : 0 < Z) : PolicyJetData m where
  Q := Q
  unit := hQ
  ρ := ρ
  profile := profile
  N := N
  s := s
  lam := lam
  regular := hreg
  N_pos := hN
  σ := σ
  J := sourceSmoothingLevels σ κ
  i := 0
  q := sourcePolicyBlock N κ
  q_pos := PlanarFalconer.sourcePolicyBlock_pos hN hκ
  policy := profileExcess (d := m+3) profile N
  a₀ := 0
  t₀ := N
  a := 0
  t := N
  base_left := le_rfl
  base_right := le_rfl
  base_N := le_rfl
  X := []
  Y := []
  X_length := rfl
  Y_length := rfl
  masks := descriptorNets (m+3) N σ
  separated := fun b _ => descriptorNets_separated (m+3) N σ b
  Z := Z
  Z_pos := hZ

noncomputable def regularOuterList {d : ℕ} (profile : ℝ → ℝ) (N : ℕ) (κ : ℝ) (c : ℕ) :
    Finset PolicyDescriptor :=
  insert (.parallel 0 c) (PlanarFalconer.remainingPolicyDescriptors
    (profileExcess (d := d) profile N) N (sourcePolicyBlock N κ) 0 N 0)

 theorem regularRoot_outerList {m N : ℕ} (Q : DyadicCube (m+3)) (hQ : Q.side = 1)
    (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ) {s lam σ κ Z : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile)
    (hN : 0 < N) (hκ : 0 < κ) (hZ : 0 < Z) (c : ℕ) :
    (regularRoot Q hQ ρ profile (σ := σ) hreg hN hκ hZ).outerList c =
      regularOuterList (d := m+3) profile N κ c := rfl

end Falconer

end OAI
