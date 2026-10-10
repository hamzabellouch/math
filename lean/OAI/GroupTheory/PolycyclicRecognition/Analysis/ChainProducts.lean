import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedPathGrowth
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # Polynomial coordinates for nilpotent chains

Every bounded-step chain is an actual product of its group increments.
Compactness bounds the increment logarithms in a global exponential chart.
The finite Dynkin identity then bounds all endpoint coordinates polynomially
in the number of steps. No geometric growth estimate is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W]

/-- The increments telescope to the relative endpoint, with their actual
lengths controlled by the chain steps. -/
theorem BoundedHeightChain.exists_increment_list {π : G → W} {L M : ℝ}
    {m : ℕ} {x y : G} (h : BoundedHeightChain π L M m x y) :
    ∃ l : List G, l.length = m ∧ (∀ g ∈ l, dist (1 : G) g ≤ L) ∧ l.prod = x⁻¹ * y := by
  induction h with
  | nil x hx => exact ⟨[], rfl, by simp, by simp⟩
  | @cons m x y z hx hxy tail ih =>
    obtain ⟨l, hlen, hl, hprod⟩ := ih
    refine ⟨(x⁻¹ * y) :: l, by simp [hlen], ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · have hd := dist_mul_left x⁻¹ x y
        simpa only [inv_mul_cancel] using hd.trans_le hxy
      · exact hl g hg
    · simp only [List.prod_cons, hprod, mul_assoc, mul_inv_cancel_left]

omit [Group G] [IsIsometricSMul G G] in
/-- Increase the permitted step length without changing the chain. -/
theorem BoundedHeightChain.mono_step {π : G → W} {L L' M : ℝ}
    {m : ℕ} {x y : G} (h : BoundedHeightChain π L M m x y) (hL : L ≤ L') :
    BoundedHeightChain π L' M m x y := by
  induction h with
  | nil x hx => exact .nil x hx
  | cons hx hxy _ ih => exact .cons hx (hxy.trans hL) ih

omit [Group G] [IsIsometricSMul G G] in
/-- Append one final bounded step. -/
theorem BoundedHeightChain.snoc {π : G → W} {L M : ℝ}
    {m : ℕ} {x y z : G} (h : BoundedHeightChain π L M m x y)
    (hz : ‖π z‖ ≤ M) (hyz : dist y z ≤ L) :
    BoundedHeightChain π L M (m + 1) x z := by
  induction h with
  | nil x hx => exact .cons hx hyz (.nil z hz)
  | cons hx hxy _ ih => exact .cons hx hxy (ih hyz)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [ProperSpace G]

omit [IsIsometricSMul G G] [LieGroup (𝓘(ℝ, E)) ⊤ G] in
/-- Compact metric balls have bounded logarithms in any fixed exponential
coordinate basis. -/
theorem exists_bound_increment_log
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (L : ℝ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ g, dist (1 : G) g ≤ L →
      ∃ x, Exp x = g ∧ ‖b.equivFun x‖ ≤ R := by
  have hc : Continuous (fun g => b.equivFun (chart.symm g)) :=
    b.equivFun.toContinuousLinearEquiv.continuous.comp chart.symm.continuous
  obtain ⟨R, hR⟩ := (isCompact_closedBall (1 : G) L).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro g hg
  refine ⟨chart.symm g, ?_, ?_⟩
  · rw [← hchart, chart.apply_symm_apply]
  · exact (hR g (by simpa only [Metric.mem_closedBall, dist_comm] using hg)).trans
      (le_max_left _ _)

/-- The finite list of basis brackets always has a common bound. -/
theorem exists_basis_structureConstant_bound {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {J : Type*} [Fintype J] (b : Basis J ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range (fun p : J × J × J =>
    |b.repr ⁅b p.1, b p.2.1⁆ p.2.2|)).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun i j l =>
    (hC ⟨(i, j, l), rfl⟩).trans (le_max_left _ _)⟩

/-- Bounded-step chains in the nilpotent group have polynomial logarithmic
coordinate size. The height function imposes no extra restriction here. -/
theorem exists_polynomial_chain_coordinate_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hzero : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (L : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (π : G → W) (M : ℝ) (m : ℕ) (x y : G),
      BoundedHeightChain π L M m x y →
      ∃ z, Exp z = x⁻¹ * y ∧ ‖b.equivFun z‖ ≤ A * (1 + (m : ℝ)) ^ c := by
  obtain ⟨R, hR, hlog⟩ := exists_bound_increment_log Exp chart hchart b L
  obtain ⟨C, hC, hbracket⟩ := exists_basis_structureConstant_bound b
  let A : ℝ := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c * (1 + R) ^ c
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro π M m x y hxy
  obtain ⟨l, hlen, hl, hprod⟩ := hxy.exists_increment_list
  have hg (i : Fin l.length) : l.get i ∈ exponentialCoordinateBox Exp b R :=
    hlog _ (hl _ (List.get_mem _ _))
  have hp := product_mem_exponentialCoordinateBox dynkin
    (LieEquiv.refl : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) Exp hExp hzero b hC hR hbracket
    l.get hg
  rw [List.ofFn_get, hprod, hlen] at hp
  exact hp

end PolycyclicRecognition

end

end OAI
