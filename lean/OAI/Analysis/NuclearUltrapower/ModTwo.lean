import OAI.Analysis.NuclearUltrapower.DyadicGroup
import OAI.Analysis.NuclearUltrapower.FiniteRepresentations

namespace OAI

section
noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
open scoped InnerProductSpace

/-- Reduction modulo two, acting by affine permutations on its eight points. -/
def residuePermutation : IntegralGroup →* Equiv.Perm Residue3 where
  toFun g := (residueMatrix g.right).toEquiv.trans (Equiv.addLeft (residue g))
  map_one' := by
    ext x i
    simp [residueMatrix]
  map_mul' g h := by
    ext x i
    change (residue (g * h) + residueMatrix (g * h).right x) i =
      (residue g + residueMatrix g.right (residue h + residueMatrix h.right x)) i
    rw [residue_mul, map_add]
    simp [residueMatrix, map_mul, add_assoc]

@[simp] theorem residuePermutation_apply (g : IntegralGroup) (x : Residue3) :
    residuePermutation g x = residue g + residueMatrix g.right x := rfl

abbrev ResidueHilbert := EuclideanSpace ℂ Residue3

def residueUnitary : IntegralGroup →* (ResidueHilbert ≃ₗᵢ[ℂ] ResidueHilbert) where
  toFun g := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (residuePermutation g)
  map_one' := by
    ext f x
    change f ((residuePermutation 1).symm x) = f x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext f x
    change f ((residuePermutation (g * h)).symm x) =
      f ((residuePermutation h).symm ((residuePermutation g).symm x))
    rw [map_mul]
    rfl

@[simp] theorem residueUnitary_apply (g : IntegralGroup) (f : ResidueHilbert) (x : Residue3) :
    residueUnitary g f x = f ((residuePermutation g).symm x) := rfl

def augmentation : Submodule ℂ ResidueHilbert := LinearMap.ker ({
  toFun f := ∑ x, f x
  map_add' f h := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum] } : ResidueHilbert →ₗ[ℂ] ℂ)

@[simp] theorem mem_augmentation (f : ResidueHilbert) :
    f ∈ augmentation ↔ ∑ x, f x = 0 := Iff.rfl

theorem augmentation_invariant (g : IntegralGroup) (f : ResidueHilbert)
    (hf : f ∈ augmentation) : residueUnitary g f ∈ augmentation := by
  rw [mem_augmentation] at *
  simpa only [residueUnitary_apply, Equiv.sum_comp] using hf

def augmentationVector : ResidueHilbert :=
  PiLp.single 2 (0 : Residue3) 1 - PiLp.single 2 (1 : Residue3) 1

theorem augmentationVector_mem : augmentationVector ∈ augmentation := by
  simp [augmentationVector, PiLp.sub_apply, PiLp.single_apply, Finset.sum_sub_distrib]

theorem augmentationVector_ne_zero : augmentationVector ≠ 0 := by
  intro h
  have he := congrArg (fun f : ResidueHilbert => f 0) h
  have hz : (0 : Residue3) ≠ 1 := by
    intro hz
    have h0 := congrFun hz 0
    exact zero_ne_one h0
  simp [augmentationVector, hz] at he

instance augmentation_nontrivial : Nontrivial augmentation := by
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro h
  have hmem := augmentationVector_mem
  rw [h] at hmem
  exact augmentationVector_ne_zero hmem

def augmentationRep : FiniteUnitaryRep IntegralGroup :=
  (FiniteUnitaryRep.mk ResidueHilbert residueUnitary).restrict augmentation augmentation_invariant

/-- A translation-fixed vector in the augmentation representation is zero. -/
theorem augmentation_no_translation_invariants (f : augmentationRep)
    (hf : ∀ v : IntegralVector3, augmentationRep.action (integralTranslation v) f = f) :
    f = 0 := by
  have ht (v : IntegralVector3) (x : Residue3) :
      f.val (residuePermutation (integralTranslation v) x) = f.val x := by
    have he := congrArg (fun z : augmentationRep => z.val (residuePermutation (integralTranslation v) x)) (hf v)
    change f.val ((residuePermutation (integralTranslation v)).symm
      (residuePermutation (integralTranslation v) x)) = _ at he
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hc (x : Residue3) : f.val x = f.val 0 := by
    have he : residuePermutation (integralTranslation (fun i => (x i).val)) 0 = x := by
      ext i
      simp [residue, integralTranslation, residueMatrix]
    simpa only [he] using ht (fun i => (x i).val) 0
  have hz : f.val 0 = 0 := by
    have hs := f.property
    rw [mem_augmentation] at hs
    simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hn : (Fintype.card Residue3 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_eq_zero.mp hs).resolve_left hn
  apply Subtype.ext
  ext x
  exact (hc x).trans hz

/-- All positive dilation pullbacks kill the translation subgroup. -/
theorem augmentation_pull_translation (j : ℕ) (hj : 0 < j) (v : IntegralVector3) :
    augmentationRep.action ((integralTheta ^ j) (integralTranslation v)) = 1 := by
  have hr : residuePermutation ((integralTheta ^ j) (integralTranslation v)) = 1 := by
    rw [integralTheta_pow_translation]
    ext x i
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    simp [residue, integralTranslation, residueMatrix, htwo, Nat.ne_of_gt hj]
  ext f
  apply Subtype.ext
  change LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (residuePermutation ((integralTheta ^ j) (integralTranslation v))) f.val = f.val
  rw [hr]
  rfl

/-- The required irreducible mod-two representation is a constituent of the
augmentation representation, hence has no translation-fixed vectors. -/
theorem exists_aperiodic_integral_rep :
    ∃ π : FiniteUnitaryRep.{0,0} IntegralGroup, π.Irreducible ∧
      (∀ j : ℕ, 0 < j → ¬ π.Equivalent (π.pull (integralTheta ^ j))) := by
  obtain ⟨π, hπ, T, hT⟩ := FiniteUnitaryRep.exists_irreducible augmentationRep
  refine ⟨π, hπ, fun j hj he => ?_⟩
  obtain ⟨U, hU⟩ := he
  have hkill (v : IntegralVector3) (x : π) :
      π.action ((integralTheta ^ j) (integralTranslation v)) x = x := by
    apply T.injective
    rw [hT, augmentation_pull_translation j hj]
    rfl
  have hfix (x : π) (v : IntegralVector3) : π.action (integralTranslation v) x = x := by
    apply U.injective
    rw [hU]
    change π.action ((integralTheta ^ j) (integralTranslation v)) (U x) = U x
    exact hkill v (U x)
  have hall (x : π) : x = 0 := by
    apply T.injective
    rw [map_zero]
    apply augmentation_no_translation_invariants
    intro v
    rw [← hT, hfix]
  obtain ⟨x, hx⟩ := exists_ne (0 : π)
  exact hx (hall x)

end NuclearUltrapower
end
end
end

end OAI
