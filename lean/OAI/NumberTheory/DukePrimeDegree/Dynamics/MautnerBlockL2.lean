import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerBlock
import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerLatticeL2

namespace OAI

/-!
# The one-block Mautner argument on actual lattice observables

A root-invariant square-integrable observable is invariant under every
root of the same coordinate block, provided those roots preserve the
measure.  The group used in the proof is the specified subgroup, not the
full special linear group.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_block_root_fixed_of_L2_root_fixed {n : ℕ}
    (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (H : Subgroup (G n)) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (hroot : ∀ p ∈ S, ∀ q ∈ S, ∀ (hpq : p ≠ q) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hpq t ∈ H)
    (f : Lp ℝ 2 μ)
    (hfix : ∀ t : ℝ,
      (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))) =ᵐ[μ] f)
    (p : Fin n) (hp : p ∈ S) (q : Fin n) (hq : q ∈ S)
    (hpq : p ≠ q) (t : ℝ) :
    (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hpq t))) =ᵐ[μ] f := by
  let : SMulInvariantMeasure H (X n) μ :=
    ⟨fun h s hs => (latticeSubgroup_preserving H μ hH h).measure_preimage hs.nullMeasurableSet⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MulAction H (Lp ℝ 2 μ) := MulAction.compHom _ (inverseDomainHom H)
  let : ContinuousSMul H (Lp ℝ 2 μ) :=
    MulAction.continuousSMul_compHom (continuous_inverseDomainHom H)
  let : IsIsometricSMul H (Lp ℝ 2 μ) :=
    ⟨fun h => isometry_smul (Lp ℝ 2 μ) (inverseDomainHom H h)⟩
  have hrep (h : H) : (h • f : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => f (rightAction x h.val)) := by
    have he := DomMulAct.smul_Lp_ae_eq (inverseDomainHom H h) f
    change (h • f : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => f (rightAction x (h.val⁻¹)⁻¹)) at he
    simpa only [inv_inv] using he
  have hrootfix (u : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hij u, hroot i hi j hj hij u⟩ : H) • f = f :=
    Lp.ext ((hrep _).trans (hfix u))
  have hpqfix := block_roots_fixed_of_one_root_fixed S hij hi hj H hroot f hrootfix
    p hp q hq hpq t
  simpa only [hpqfix] using (hrep ⟨_, hroot p hp q hq hpq t⟩).symm

end DukePrimeDegree

end

end OAI
