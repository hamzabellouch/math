import OAI.MeasureTheory.Falconer.Estimates.FarPolicyScales
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer

namespace OAI

/-! # The actual retained policy list supplies the far analytic data -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor remainingPolicyDescriptors descriptorLength)

/-- Data retained during an angular episode. Its descriptor list and split
are computed from the inherited positive interval. -/
structure PolicyJetData (m : ℕ) where
  Q : DyadicCube (m+3)
  unit : Q.side = 1
  ρ : Measure (Space (m+3))
  profile : ℝ → ℝ
  N : ℕ
  s : ℝ
  lam : ℝ
  regular : Regularization.RegularizedProfileData Q ρ N s lam profile
  N_pos : 0 < N
  σ : ℝ
  J : ℕ
  i : ℕ
  q : ℕ
  q_pos : 0 < q
  policy : ℕ → ℝ
  a₀ : ℕ
  t₀ : ℕ
  a : ℕ
  t : ℕ
  base_left : a₀ ≤ a
  base_right : t ≤ t₀
  base_N : t₀ ≤ N
  X : List (Fin (m+3) → Bool)
  Y : List (Fin (m+3) → Bool)
  X_length : X.length = a
  Y_length : Y.length = a
  masks : PolicyDescriptor → Finset (Sphere (m+3))
  separated : ∀ b ∈ remainingPolicyDescriptors policy N q a₀ t₀ a,
    ∀ w ∈ masks b, ∀ z ∈ masks b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z
  Z : ℝ
  Z_pos : 0 < Z

namespace PolicyJetData
variable {m : ℕ}

noncomputable def list (P : PolicyJetData m) :=
  remainingPolicyDescriptors P.policy P.N P.q P.a₀ P.t₀ P.a

noncomputable def longest (P : PolicyJetData m) := P.list.sup descriptorLength

noncomputable def splitDepth (P : PolicyJetData m) :=
  P.t-2*PlanarFalconer.sourceFarBuffer P.N P.longest P.σ

theorem list_card (P : PolicyJetData m) : P.list.card ≤ (P.N+1)^3 :=
  PlanarFalconer.remainingPolicyDescriptors_card P.policy P.q_pos

theorem longest_le_N (P : PolicyJetData m) : P.longest ≤ P.N := by
  apply Finset.sup_le
  intro b hb
  have hbase := (Finset.mem_filter.mp hb).1
  have hh := PlanarFalconer.policyDescriptor_twice_length P.policy P.q_pos hbase
  have := P.base_N
  omega

theorem split_gap (P : PolicyJetData m) (hfar : P.a < P.splitDepth) :
    20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.splitDepth ∧
      2*(P.longest:ℝ) ≤ (P.t:ℝ)-P.splitDepth := by
  have ht : 2*PlanarFalconer.sourceFarBuffer P.N P.longest P.σ ≤ P.t := by
    change P.a < P.t-2*PlanarFalconer.sourceFarBuffer P.N P.longest P.σ at hfar
    omega
  have he : (P.t:ℝ)-P.splitDepth =
      2*(PlanarFalconer.sourceFarBuffer P.N P.longest P.σ:ℝ) := by
    rw [splitDepth,Nat.cast_sub ht,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [he]
  have hs := PlanarFalconer.sourceFarBuffer_ge_slack P.N P.longest P.σ
  have hl : (P.longest:ℝ) ≤ (PlanarFalconer.sourceFarBuffer P.N P.longest P.σ:ℝ) :=
    Nat.cast_le.mpr (PlanarFalconer.sourceFarBuffer_ge_length P.N P.longest P.σ)
  constructor <;> linarith

noncomputable def farThreshold (B σ : ℝ) (hB : 1 ≤ B) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (m : ℕ) : ℕ :=
  max (Classical.choose (eventual_descriptor_list_scale 3 hB hσ))
    (Classical.choose (eventual_far_split_scales (m+3) hσ hσ1))

/-- The retained list and prescribed split determine the analytic data.
No frequency assumption is supplied by the caller. -/
noncomputable def farData (P : PolicyJetData m) (B : ℝ)
    (hB : 1 ≤ B) (hσ : 0 < P.σ) (hσ1 : P.σ ≤ 1)
    (hN : farThreshold B P.σ hB hσ hσ1 m ≤ P.N)
    (hfar : P.a < P.splitDepth) (loss : ℝ) (hloss : 0 ≤ loss) : JetStateFarData m B := by
  let Dmask := 8*max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ))
  let E := descriptorListScale B P.N P.σ P.longest P.list
  have hlist := (Classical.choose_spec (eventual_descriptor_list_scale 3 hB hσ)) P.N
    ((le_max_left _ _).trans hN) P.longest P.list P.list_card
  have hE : 0 ≤ E := by dsimp [E,descriptorListScale]; positivity
  have hD : 1 ≤ 2*(E+1) := by linarith
  have hs := (Classical.choose_spec (eventual_far_split_scales (m+3) hσ hσ1)) P.N
    ((le_max_right _ _).trans hN) P.longest P.splitDepth P.t P.longest_le_N
    (Nat.sub_le _ _) (P.split_gap hfar).1 (P.split_gap hfar).2 (2*(E+1)) hD hlist.2
  refine {
    Q := P.Q, unit := P.unit, ρ := P.ρ, profile := P.profile, N := P.N,
    s := P.s, lam := P.lam, regular := P.regular, N_pos := P.N_pos,
    a := P.a, h := P.splitDepth, t := P.t, ah := hfar.le, ht := hs.1,
    tN := P.base_right.trans P.base_N, σ := P.σ, J := P.J, i := P.i,
    q := P.q, policy := P.policy, X := P.X, Y := P.Y,
    X_length := P.X_length, Y_length := P.Y_length,
    F := P.list, masks := P.masks, separated := P.separated,
    child_list := ?_, Dq := 1, Dmask := Dmask, E := E, Z := P.Z,
    Dq_nonneg := by norm_num, Dmask_one := ?_, Z_pos := P.Z_pos,
    scale_one := hD, mask_scale := ?_, list_scale := le_rfl,
    κ := 16*P.σ, loss := loss, loss_nonneg := hloss,
    scale_upper := hs.2.1, band_scale := hs.2.2.1,
    large_scale := hs.2.2.2.1, large_frequency := hs.2.2.2.2.1,
    shell_one := hs.2.2.2.2.2.1,
    shell_scale := by simpa only [neg_mul] using hs.2.2.2.2.2.2 }
  · intro b hb
    have hab : P.a ≤ b := by have := (Finset.mem_Icc.mp hb).1; omega
    exact PlanarFalconer.minimal_policy_list_survives P.policy P.q_pos
      (P.base_left.trans hab) P.base_right hab
  · have hh : 1 ≤ max 1 ((2:ℝ)^P.longest*((2:ℝ)^P.N)^(-50*P.σ)) := le_max_left _ _
    dsimp [Dmask]
    linarith
  · intro b hb
    exact descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)

end PolicyJetData
end Falconer

end OAI
