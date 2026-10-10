import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import Mathlib.GroupTheory.Finiteness

namespace OAI

/-!
# Finite generation of a uniform lattice from metric chains

The bounded-distance lattice section sends ambient chains to bounded
lattice steps. The steps belong to one finite ball, which therefore
generates the lattice. This is the finite-generation part of the
Švarc argument, proved from compactness and explicit chains.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G]

omit [IsTopologicalGroup G] [ProperSpace G] in
/-- A uniform lattice in a metric group with linear metric chains
has a finite generating set contained in a single induced metric ball. -/
theorem IsUniformLattice.exists_generating_ball {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) :
    ∃ B : ℝ, 0 ≤ B ∧
      Subgroup.closure (closedBall (1 : Λ) B) = ⊤ := by
  obtain ⟨r, R, hR, hr, hrlip⟩ := hΛ.exists_metric_section
  let B := R + R + C.step
  have hRB : R ≤ B := by dsimp [B]; linarith [C.step_pos]
  let K : Subgroup Λ := Subgroup.closure (closedBall (1 : Λ) B)
  have hsmall (x : Λ) (hx : dist (1 : G) (x : G) ≤ B) : x ∈ K := by
    apply Subgroup.subset_closure
    change dist (x : G) 1 ≤ B
    simpa only [dist_comm] using hx
  have hdiff (x y : Λ) (hxy : dist (x : G) (y : G) ≤ B) : x⁻¹ * y ∈ K := by
    apply hsmall
    change dist (1 : G) ((x : G)⁻¹ * (y : G)) ≤ B
    rwa [dist_one_groupDifference]
  refine ⟨B, hR.trans hRB, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨n, p, hp0, hpn, _, hpstep⟩ := C.chain 1 (x : G)
  have hstart : r (p 0) ∈ K := by
    apply hsmall
    rw [hp0]
    exact (hr 1).trans hRB
  have hvertices : ∀ i ≤ n, r (p i) ∈ K := by
    intro i hi
    induction i with
    | zero => exact hstart
    | succ i ih =>
      have hi' : i < n := Nat.lt_of_succ_le hi
      have hprev := ih (Nat.le_of_lt hi')
      have hnext : (r (p i))⁻¹ * r (p (i + 1)) ∈ K := by
        apply hdiff
        have hs := (hrlip (p i) (p (i + 1))).trans
          (add_le_add (hpstep i hi') le_rfl)
        change dist (r (p i) : G) (r (p (i + 1)) : G) ≤ _ at hs
        simpa only [B, add_assoc, add_comm, add_left_comm] using hs
      simpa only [mul_inv_cancel_left] using K.mul_mem hprev hnext
  have hend : (r (p n))⁻¹ * x ∈ K := by
    apply hdiff
    rw [hpn, dist_comm]
    exact (hr x).trans hRB
  simpa only [mul_inv_cancel_left] using K.mul_mem (hvertices n le_rfl) hend

/-- Compactness and linear ambient chains give finite generation without
any algebraic structure theorem for lattices. -/
theorem IsUniformLattice.finitelyGenerated {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) : Group.FG Λ := by
  obtain ⟨B, _, hB⟩ := hΛ.exists_generating_ball C
  exact Group.fg_iff.mpr ⟨closedBall (1 : Λ) B, hB, hΛ.finite_closedBall B⟩

end PolycyclicRecognition

end

end OAI
