import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockOrbit
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitBasepoint
import OAI.NumberTheory.PrimePackets.ZetaDerivatives

namespace OAI

/-!
# Removing the generic-basepoint condition

A finite invariant measure on a block orbit pushes to an invariant
measure on the lattice space. Diagonal recurrence gives a generic
basepoint almost everywhere. Changing to that basepoint removes the
genericity hypothesis from the prime-degree block-orbit obstruction.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def latticeOrbitPoint {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    LatticeOrbitQuotient g H → X n :=
  Quotient.lift (fun a : H => Quotient.mk _ (g * a.val)) (by
    intro a b hab
    apply Quotient.sound
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b at hab
    change QuotientGroup.rightRel (integralGroup n) (g * a.val) (g * b.val)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    change g * (b.val * a.val⁻¹) * g⁻¹ ∈ integralGroup n at hab
    simpa only [_root_.mul_inv_rev, mul_assoc] using hab)

lemma continuous_latticeOrbitPoint {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    Continuous (latticeOrbitPoint g H) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_const.mul continuous_subtype_val)

lemma latticeOrbitPoint_rightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (x : LatticeOrbitQuotient g H) (h : H) :
    latticeOrbitPoint g H (latticeOrbitRightAction g H x h) =
      rightAction (latticeOrbitPoint g H x) h.val := by
  induction x using Quotient.inductionOn with
  | h a =>
    change Quotient.mk _ (g * (a.val * h.val)) = Quotient.mk _ ((g * a.val) * h.val)
    rw [mul_assoc]

lemma latticeOrbitPoint_map_invariant {n : ℕ} (g : G n) (H : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g H))
    (hinv : ∀ h : H, μ.map (fun x => latticeOrbitRightAction g H x h) = μ) (h : H) :
    (μ.map (latticeOrbitPoint g H)).map (fun x => rightAction x h.val) =
      μ.map (latticeOrbitPoint g H) := by
  let F := latticeOrbitPoint g H
  have hF := (continuous_latticeOrbitPoint g H).measurable
  calc
    _ = μ.map ((fun x => rightAction x h.val) ∘ F) :=
      Measure.map_map (continuous_rightAction h.val).measurable hF
    _ = μ.map (F ∘ fun x => latticeOrbitRightAction g H x h) := by
      congr 1
      funext x
      exact (latticeOrbitPoint_rightAction g H x h).symm
    _ = (μ.map (fun x => latticeOrbitRightAction g H x h)).map F :=
      (Measure.map_map hF (continuous_latticeOrbitRightAction g H h).measurable).symm
    _ = μ.map F := by rw [hinv h]

lemma diagonalFlow_mem_blockMatrixGroup {d : ℕ}
    (r : Setoid (Fin (d + 1))) (u : LogCoordinates d) :
    diagonalFlow u ∈ blockMatrixGroup r := by
  intro c _
  apply slMatrixConjugation_eq_self
  exact Matrix.commute_diagonal _ _

/-- Every nonzero finite invariant block-orbit measure admits a
generic lattice representative in the same actual orbit. -/
theorem exists_generic_block_orbit_point {d : ℕ}
    (g : G (d + 1)) (r : Setoid (Fin (d + 1)))
    (μ : Measure (LatticeOrbitQuotient g (blockMatrixGroup r)))
    [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : blockMatrixGroup r,
      μ.map (fun x => latticeOrbitRightAction g (blockMatrixGroup r) x h) = μ) :
    ∃ h : blockMatrixGroup r,
      ∀ v ∈ rowLattice (g * h.val).val, v ≠ 0 → ∀ j, v j ≠ 0 := by
  let ν := μ.map (latticeOrbitPoint g (blockMatrixGroup r))
  have hA : ∀ u : LogCoordinates d, ν.map (fun x => rightAction x (diagonalFlow u)) = ν := by
    intro u
    exact latticeOrbitPoint_map_invariant g (blockMatrixGroup r) μ hinv
      ⟨diagonalFlow u, diagonalFlow_mem_blockMatrixGroup r u⟩
  have hgen := ae_no_coordinate_zero d ν hA
  have hg : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice (latticeOrbitPoint g (blockMatrixGroup r) x),
      v ≠ 0 → ∀ j, v j ≠ 0 :=
    ae_of_ae_map (continuous_latticeOrbitPoint g _).measurable.aemeasurable hgen
  have : NeBot (ae μ) := ae_neBot.mpr hμ
  obtain ⟨x, hx⟩ := hg.exists
  induction x using Quotient.inductionOn with
  | h a => exact ⟨a, hx⟩

/-- In prime dimension, every nontrivial block subgroup with a
nonzero finite invariant lattice-orbit measure has just one block.
The basepoint is arbitrary; genericity is supplied by recurrence. -/
theorem block_partition_universal_of_invariant_finite_orbit {d : ℕ}
    (hn : (d + 1).Prime) (g : G (d + 1))
    (r : Setoid (Fin (d + 1))) (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (μ : Measure (LatticeOrbitQuotient g (blockMatrixGroup r)))
    [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : blockMatrixGroup r,
      μ.map (fun x => latticeOrbitRightAction g (blockMatrixGroup r) x h) = μ) :
    ∀ i j, r i j := by
  obtain ⟨h, hzero⟩ := exists_generic_block_orbit_point g r μ hμ hinv
  let E := latticeOrbitBasepointHomeomorph g (blockMatrixGroup r) h
  let ν := μ.map E.symm
  have hν : ν ≠ 0 := (Measure.map_ne_zero_iff E.symm.continuous.measurable.aemeasurable).mpr hμ
  apply block_partition_universal_of_finite_orbit hn (g * h.val) hzero r hnontrivial ν hν
  exact latticeOrbitBasepoint_measure_invariant g (blockMatrixGroup r) h μ hinv

end DukePrimeDegree

end

end OAI
