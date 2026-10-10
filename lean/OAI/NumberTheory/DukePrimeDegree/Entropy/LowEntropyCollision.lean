import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSelectionData
import OAI.NumberTheory.DukePrimeDegree.Dynamics.EqualLeafReturnWindows
import OAI.NumberTheory.DukePrimeDegree.Dynamics.CompactShearingSequence
import OAI.NumberTheory.DukePrimeDegree.Dynamics.IntrinsicShearingCollision

namespace OAI

/-!
# Actual equal-leaf horospherical collisions

All sets, return pairs, recurrence times and annular translations are
constructed from diagonal invariance and nontrivial root leaves. No
horospherical separation premise is used here. The resulting distinct
points avoid any prescribed null set.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem RootPairSelectionData.exists_equal_leaf_collision
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0)
    (N : Set (X (d + 1))) (S : RootPairSelectionData d hij μ hfree N) :
    ∃ x ∈ S.K, ∃ h : PrimeDegreePackets.G (d + 1),
      RootHorosphereShape i j h ∧ rightAction x h ∈ S.K ∧
      rightAction x h ≠ x ∧ intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ (rightAction x h) := by
  let C : ℝ := 16 / S.ρ ^ 2
  have hρ := S.rho_pos
  have hρone : S.ρ ≤ 1 := by linarith [S.rho_small]
  have hC : 1 ≤ C := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith [S.rho_small]
  have hsecond : 16 / S.ρ ≤ S.ρ * C := by
    have he : S.ρ * C = 16 / S.ρ := by
      dsimp only [C]
      field_simp [hρ.ne']
    exact he.ge
  obtain ⟨x, y, g, hg, hp⟩ := exists_equal_leaf_return_sequence_with_windows
    d hd hij μ hA S.Z S.source_measurable S.source_positive (max 1 (Real.log C))
  let z : ℕ → Fin 2 → X (d + 1) := fun m => ![x m, y m]
  have hz (m : ℕ) (k : Fin 2) : z m k ∈ S.Z := by
    fin_cases k
    · exact (hp m).1
    · exact (hp m).2.1
  have hreg (m : ℕ) (k : Fin 2) := S.source_regular (z m k) (hz m k)
  have hinit (m : ℕ) : intrinsicRootKernel hij μ hfree (z m 0) =
      intrinsicRootKernel hij μ hfree (z m 1) := by
    rw [(hreg m 0).1, (hreg m 1).1]
    exact (hp m).2.2.2.2.1
  obtain ⟨γ, p, t, hγ, hret⟩ := exists_compact_equal_leaf_shearing_sequence d hij μ hfree g hg
    (fun m => (hp m).2.2.2.1) (fun m => (hp m).2.2.2.2.2.1)
    (fun m => (le_max_left _ _).trans (hp m).2.2.2.2.2.2) C hC
    (fun m => (le_max_right _ _).trans (hp m).2.2.2.2.2.2)
    S.K S.G S.H z (fun m => (hp m).2.2.1) S.ρ (1 / 100)
    (ENNReal.ofReal (1 / 8)) (1 / 2) (by norm_num) hsecond
    (by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),
        ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num)
    (fun x hx => ⟨(S.good_regular x hx).1, (S.good_regular x hx).2.1,
      (S.good_regular x hx).2.2.2⟩)
    S.good_returns S.small_ball
    (fun m k r hr => by rw [(hreg m k).1]; exact (hreg m k).2.2.1 r hr)
    hinit (fun m k => S.source_covariance (z m k) (hz m k))
    (fun m k => S.source_returns (z m k) (hz m k))
  have hlo (m : ℕ) (b : Fin 2) : S.ρ ≤ |rootShearingKappa i j (γ m) * t m b| := by
    rcases hret m with ⟨_, _, _, hlo, _, hsecond', _⟩
    fin_cases b
    · exact hlo
    · have hr : S.ρ ≤ 16 / S.ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
      exact hr.trans hsecond'
  have hupp (m : ℕ) (b : Fin 2) : |rootShearingKappa i j (γ m) * t m b| ≤ C := by
    rcases hret m with ⟨_, _, _, _, hfirst, _, hsecond'⟩
    fin_cases b
    · exact hfirst.trans hC
    · exact hsecond'
  exact two_annular_equal_leaves_force_collision hij μ hfree S.K S.compact S.continuous
    (fun x hx => (S.compact_regular x hx).1) S.coordinates γ hγ
    (fun m => (hret m).1) (fun m => (hret m).2.1) p t S.ρ C hρ hρone hlo
    (fun m => (hret m).2.2.2.2.1) (fun m => (hret m).2.2.2.2.2.1) hupp
    (fun m b => ((hret m).2.2.1 b).1)
    (fun m b => ((hret m).2.2.1 b).2.1)
    (fun m b => ((hret m).2.2.1 b).2.2)

theorem exists_distinct_equal_leaf_horospherical_pair
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ x ∉ N, ∃ h : G (d + 1), RootHorosphereShape i j h ∧ rightAction x h ∉ N ∧
      rightAction x h ≠ x ∧ intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ (rightAction x h) := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨S⟩ := nonempty_rootPairSelectionData d hij μ hA hfree hnontrivial N hN hNzero
  obtain ⟨x, hx, h, hshape, hy, hne, heq⟩ :=
    S.exists_equal_leaf_collision d hd hij μ hA hfree N
  exact ⟨x, S.outside hx, h, hshape, S.outside hy, hne, heq⟩

end DukePrimeDegree

end

end OAI
