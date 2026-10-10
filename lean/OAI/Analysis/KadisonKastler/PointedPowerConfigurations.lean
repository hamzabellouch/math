import OAI.Analysis.KadisonKastler.HilbertMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! # Configuration coordinates for a pointed countable Hilbert product

A configuration records the finitely many sites outside the reference
vector. Splitting off one site gives a finite Hilbert sum of identical
tail spaces, with an explicit action on every orthonormal basis vector.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators lp

noncomputable section

abbrev PointedPowerConfiguration := ℕ →₀ Fin 4
abbrev PointedPowerHilbert := ℓ²(PointedPowerConfiguration, ℂ)

def pointedPowerBasis (f : PointedPowerConfiguration) : PointedPowerHilbert :=
  lp.single 2 f 1

def pointedPowerVacuum : PointedPowerHilbert := pointedPowerBasis 0

@[simp] theorem norm_pointedPowerBasis (f : PointedPowerConfiguration) :
    ‖pointedPowerBasis f‖ = 1 := by
  simp only [pointedPowerBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]

@[simp] theorem norm_pointedPowerVacuum : ‖pointedPowerVacuum‖ = 1 :=
  norm_pointedPowerBasis 0

def pointedPowerHilbertBasis : HilbertBasis PointedPowerConfiguration ℂ PointedPowerHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem pointedPowerHilbertBasis_apply (f : PointedPowerConfiguration) :
    pointedPowerHilbertBasis f = pointedPowerBasis f := by
  exact (pointedPowerHilbertBasis.repr_symm_single f).symm

instance : Nontrivial PointedPowerHilbert := by
  have h : pointedPowerVacuum ≠ 0 := by
    intro hz
    have hn := norm_pointedPowerVacuum
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  exact ⟨⟨pointedPowerVacuum, 0, h⟩⟩

instance : TopologicalSpace.SeparableSpace PointedPowerHilbert := by
  have hs0 : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range pointedPowerBasis) : Set PointedPowerHilbert) :=
    (Set.countable_range pointedPowerBasis).isSeparable.span
  have hs := hs0.closure
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℂ (Set.range pointedPowerBasis)).topologicalClosure : Set PointedPowerHilbert) at hs
  have hd := pointedPowerHilbertBasis.dense_span
  rw [show (pointedPowerHilbertBasis : PointedPowerConfiguration → PointedPowerHilbert) =
    pointedPowerBasis from funext pointedPowerHilbertBasis_apply] at hd
  rw [hd] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

abbrev PointedPowerTail (i : ℕ) := {f : PointedPowerConfiguration // f i = 0}
abbrev PointedPowerTailHilbert (i : ℕ) := ℓ²(PointedPowerTail i, ℂ)

/-- A configuration is its label at one site and the vacuum-filled tail. -/
def pointedPowerSplit (i : ℕ) :
    PointedPowerConfiguration ≃ Fin 4 × PointedPowerTail i where
  toFun f := (f i, ⟨f.erase i, Finsupp.erase_same⟩)
  invFun p := p.2.val.update i p.1
  left_inv f := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp
  right_inv p := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      ext j
      by_cases h : j = i
      · subst j
        simp [p.2.property]
      · simp [h]

@[simp] theorem pointedPowerSplit_fst (i : ℕ) (f : PointedPowerConfiguration) :
    (pointedPowerSplit i f).1 = f i := rfl

@[simp] theorem pointedPowerSplit_symm (i : ℕ) (a : Fin 4) (f : PointedPowerTail i) :
    (pointedPowerSplit i).symm (a, f) = f.val.update i a := rfl

section FiniteFibres

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

private def finiteL2BasisVector (p : ι × κ) : FiniteHilbert ι ℓ²(κ, ℂ) :=
  tupleSingle p.1 (lp.single 2 p.2 1)

private theorem finiteL2BasisVector_orthonormal :
    Orthonormal ℂ (finiteL2BasisVector (ι := ι) (κ := κ)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k
  · subst k
    simp [finiteL2BasisVector, PiLp.inner_apply, tupleSingle_apply, Pi.single_apply, apply_ite,
      lp.inner_single_left, lp.single_apply, Prod.mk.injEq]
  · simp [finiteL2BasisVector, PiLp.inner_apply, tupleSingle_apply, Pi.single_apply, apply_ite,
      hik, Ne.symm hik, Prod.mk.injEq]

private theorem finiteL2BasisVector_total :
    ⊤ ≤ (Submodule.span ℂ (Set.range
      (finiteL2BasisVector (ι := ι) (κ := κ)))).topologicalClosure := by
  apply le_of_eq
  symm
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply bot_unique
  intro x hx
  change x = 0
  apply PiLp.ext
  intro i
  apply lp.ext
  funext j
  have h := hx (finiteL2BasisVector (i, j)) (Submodule.subset_span ⟨(i, j), rfl⟩)
  have he : inner ℂ (finiteL2BasisVector (i, j)) x = x i j := by
    simp only [finiteL2BasisVector, PiLp.inner_apply, tupleSingle_apply]
    rw [Finset.sum_eq_single i]
    · simp [lp.inner_single_left]
    · intro k _hk hki
      simp [hki]
    · simp
  rwa [he] at h

/-- The usual basis of the finite sum of scalar `l²` spaces. -/
def finiteL2Basis : HilbertBasis (ι × κ) ℂ (FiniteHilbert ι ℓ²(κ, ℂ)) :=
  HilbertBasis.mk finiteL2BasisVector_orthonormal finiteL2BasisVector_total

@[simp] theorem finiteL2Basis_apply (i : ι) (j : κ) :
    finiteL2Basis (i, j) = tupleSingle i (lp.single 2 j 1) := by
  simp only [finiteL2Basis, HilbertBasis.coe_mk, finiteL2BasisVector]

end FiniteFibres

private def pointedPowerSplitBasis (i : ℕ) :
    HilbertBasis (Fin 4 × PointedPowerTail i) ℂ PointedPowerHilbert := by
  let b := pointedPowerHilbertBasis
  have ho := b.orthonormal.comp (pointedPowerSplit i).symm
    (pointedPowerSplit i).symm.injective
  refine HilbertBasis.mk ho ?_
  have hr : Set.range (b ∘ (pointedPowerSplit i).symm) = Set.range b := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨pointedPowerSplit i f, by simp⟩
  rw [hr, b.dense_span]

private theorem pointedPowerSplitBasis_apply (i : ℕ) (p : Fin 4 × PointedPowerTail i) :
    pointedPowerSplitBasis i p = pointedPowerBasis ((pointedPowerSplit i).symm p) := by
  simp only [pointedPowerSplitBasis, HilbertBasis.coe_mk, Function.comp_apply,
    pointedPowerHilbertBasis_apply]

/-- Splitting off one site is a genuine Hilbert-space equivalence. -/
def pointedPowerFibreEquiv (i : ℕ) :
    PointedPowerHilbert ≃ₗᵢ[ℂ] FiniteHilbert (Fin 4) (PointedPowerTailHilbert i) :=
  (pointedPowerSplitBasis i).repr.trans finiteL2Basis.repr.symm

@[simp] theorem pointedPowerFibreEquiv_basis (i : ℕ) (f : PointedPowerConfiguration) :
    pointedPowerFibreEquiv i (pointedPowerBasis f) =
      tupleSingle (f i) (lp.single 2 ⟨f.erase i, Finsupp.erase_same⟩ 1) := by
  have hb := pointedPowerSplitBasis_apply i (pointedPowerSplit i f)
  simp only [Equiv.symm_apply_apply] at hb
  rw [← hb]
  change finiteL2Basis.repr.symm
    ((pointedPowerSplitBasis i).repr (pointedPowerSplitBasis i (pointedPowerSplit i f))) = _
  rw [HilbertBasis.repr_self, HilbertBasis.repr_symm_single]
  exact finiteL2Basis_apply _ _

end

end KadisonKastler

end OAI
