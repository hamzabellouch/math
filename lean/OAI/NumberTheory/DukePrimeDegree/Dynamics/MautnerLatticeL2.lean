import OAI.NumberTheory.DukePrimeDegree.Dynamics.MautnerRootPair
import OAI.NumberTheory.DukePrimeDegree.Geometry.LatticeGroupDecomposition
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

namespace OAI

/-!
# Mautner for the actual lattice L² action

Only the specified subgroup preserves the measure. Pullback by its
right action is a continuous isometric action on L². Thus a root-flow
invariant L² observable is also invariant under the opposite root and
the associated diagonal elements of that subgroup.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def inverseDomainHom (H : Type*) [Group H] : H →* Hᵈᵐᵃ where
  toFun h := DomMulAct.mk h⁻¹
  map_one' := by simp
  map_mul' a b := by simp only [mul_inv_rev, DomMulAct.mk_mul]

lemma continuous_inverseDomainHom (H : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] : Continuous (inverseDomainHom H) :=
  DomMulAct.continuous_mk.comp continuous_inv

theorem ae_opposite_root_fixed_of_L2_root_fixed {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (H : Subgroup (G n))
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    (f : Lp ℝ 2 μ)
    (hfix : ∀ t : ℝ,
      (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))) =ᵐ[μ] f)
    (t : ℝ) :
    (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hij.symm t))) =ᵐ[μ] f := by
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
  have hroot (u : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hij u, hU u⟩ : H) • f = f :=
    Lp.ext ((hrep _).trans (hfix u))
  have hv := opposite_root_fixed_of_root_fixed hij H hU hV f hroot t
  simpa only [hv] using (hrep ⟨_, hV t⟩).symm

theorem ae_root_pair_diagonal_fixed_of_L2_root_fixed {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (H : Subgroup (G n))
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    (f : Lp ℝ 2 μ)
    (hfix : ∀ t : ℝ,
      (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))) =ᵐ[μ] f)
    (a : ℝ) (ha : a ≠ 0) :
    (fun x => f (rightAction x (Matrix.SpecialLinearGroup.diag2n hij a ha))) =ᵐ[μ] f := by
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
  have hroot (u : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hij u, hU u⟩ : H) • f = f :=
    Lp.ext ((hrep _).trans (hfix u))
  have hd := diag2n_fixed_of_root_fixed hij H hU hV f hroot a ha
  simpa only [hd] using (hrep ⟨_, diag2n_mem_of_opposite_roots hij H hU hV a ha⟩).symm

end DukePrimeDegree

end

end OAI
