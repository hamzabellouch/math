import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.CutBranching
import OAI.Probability.BinarySweep.YoungTheory.CoindFibers

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Young
open Representation Irrep

variable (μ : YoungDiagram) (p : ℕ)

abbrev HookPlacements := Cell (southeast μ p) ↪ Cell μ
abbrev HookHilbertInducedSpace := PiLp 2 (fun _ : HookPlacements μ p => SpechtHilbert (hookPart μ p))

def hookHilbertInduced : Representation ℂ (G μ) (HookHilbertInducedSpace μ p) :=
  coindHilbertRep (hookPerm μ p) (hilbertSpecht (hookPart μ p))
    (fun x => (placementSection (cutEquiv μ p) x)⁻¹)
    (placement_cosets_bijective (cutEquiv μ p))

def hookHilbertFiberEquiv : Representation.Equiv
    (coind (hookPerm μ p) (hilbertSpecht (hookPart μ p))) (hookHilbertInduced μ p) :=
  conjugateEquiv _ (coindHilbertEquiv (hookPerm μ p) (hilbertSpecht (hookPart μ p))
    (fun x => (placementSection (cutEquiv μ p) x)⁻¹)
    (placement_cosets_bijective (cutEquiv μ p)))

lemma hookHilbertInduced_inner (g : G μ) (v w : HookHilbertInducedSpace μ p) :
    inner ℂ (hookHilbertInduced μ p g v) (hookHilbertInduced μ p g w) = inner ℂ v w :=
  coindHilbert_unitary _ _ _ _ (hilbertSpecht_inner (hookPart μ p)) g v w

lemma hookHilbertInduced_unitary (g : G μ) (v : HookHilbertInducedSpace μ p) :
    ‖hookHilbertInduced μ p g v‖ = ‖v‖ :=
  ((hookHilbertInduced μ p g).isometryOfInner (hookHilbertInduced_inner μ p g)).norm_map v

lemma hook_hilbert_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤
      Module.finrank ℂ (IntertwiningMap (hilbertSpecht μ) (hookHilbertInduced μ p)) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  let : Module.Finite ℂ (SpechtSpace (hookPart μ p)) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace (hookPart μ p)))
  have hs := Irrep.multiplicity_symm (spechtRep (hookPart μ p)) (hookRestriction μ p)
  have he := Irrep.multiplicity_congr
    (repEquiv_comp (conjugateEquiv (spechtRep μ) (spechtHilbertEquiv μ)) (hookPerm μ p))
    (conjugateEquiv (spechtRep (hookPart μ p)) (spechtHilbertEquiv (hookPart μ p)))
  have hr := (coindHomEquiv (hookPerm μ p) (hilbertSpecht μ)
    (hilbertSpecht (hookPart μ p))).finrank_eq
  have hd := multiplicity_congr (Representation.Equiv.refl (hilbertSpecht μ))
    (hookHilbertFiberEquiv μ p)
  exact (hook_removal_multiplicity μ p).trans (Nat.le_of_eq (hs.trans (he.trans (hr.trans hd))))

theorem hook_induced_moment_le (w : G μ → ℂ) (q : ℕ) :
    (Module.finrank ℂ (SpechtSpace (southeast μ p)) : ℝ) *
      evenMoment q (groupAverage (hilbertSpecht μ) w) ≤
        evenMoment q (groupAverage (hookHilbertInduced μ p) w) := by
  have hm := multiplicity_moment_le (hilbertSpecht μ) (hookHilbertInduced μ p) w
    (hilbertSpecht_unitary μ) (hookHilbertInduced_unitary μ p) q
  have hp : 0 ≤ evenMoment q (groupAverage (hilbertSpecht μ) w) :=
    (Complex.nonneg_iff.mp (positive_pow
      (LinearMap.isPositive_adjoint_comp_self _) q).trace_nonneg).1
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hook_hilbert_multiplicity μ p) hp).trans hm

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [Fintype I] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

def fiberInclude (i : I) : W →ₗ[ℂ] CoindHilbertSpace (I := I) (W := W) :=
  (WithLp.linearEquiv 2 ℂ (I → W)).symm.toLinearMap.comp (LinearMap.single ℂ (fun _ : I => W) i)

def fiberProject (i : I) : CoindHilbertSpace (I := I) (W := W) →ₗ[ℂ] W :=
  (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℂ (I → W)).toLinearMap

def hilbertBlock (A : CoindHilbertSpace (I := I) (W := W) →ₗ[ℂ]
    CoindHilbertSpace (I := I) (W := W)) (i j : I) : W →ₗ[ℂ] W :=
  (fiberProject i).comp (A.comp (fiberInclude j))

omit [Fintype I] in
lemma fiberInclude_apply (i j : I) (w : W) : fiberInclude i w j = if j=i then w else 0 := by
  simp [fiberInclude,eq_comm]

omit [Fintype I] in
lemma hilbertBlock_coind (a : G) (i j : I) :
    hilbertBlock (coindHilbertRep φ σ r hc a) i j =
      if cosetIndexAction φ r hc a i = j then
        σ ((cosetEquiv φ r hc).symm (r i*a)).1 else 0 := by
  ext w
  change coindHilbertRep φ σ r hc a (fiberInclude j w) i = _
  rw [coindHilbertRep_apply,fiberInclude_apply]
  split_ifs <;> simp_all

variable [Fintype G] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
lemma hilbertBlock_average (p : G → ℂ) (i j : I) :
    hilbertBlock (groupAverage (coindHilbertRep φ σ r hc) p) i j =
      ∑ a, if cosetIndexAction φ r hc a i = j then
        p a • σ ((cosetEquiv φ r hc).symm (r i*a)).1 else 0 := by
  have he : hilbertBlock (groupAverage (coindHilbertRep φ σ r hc) p) i j =
      ∑ a, p a • hilbertBlock (coindHilbertRep φ σ r hc a) i j := by
    ext w
    simp [hilbertBlock,groupAverage,LinearMap.sum_apply,LinearMap.smul_apply]
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [hilbertBlock_coind]
  split_ifs <;> simp

end BinaryCoordinateSweeps.Irrep

end

end OAI
