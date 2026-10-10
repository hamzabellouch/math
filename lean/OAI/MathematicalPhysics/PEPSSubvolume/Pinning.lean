import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.LocalOperators

namespace OAI

/-! Pinned core/shell tensor coordinates and isometric insertion. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.Pinning
open Matrix
variable {L q : ℕ} (C X : Finset (Vertex L)) (hCX : C ⊆ X)

def coreRestrict (x : RegionConfiguration q X) : RegionConfiguration q C :=
  fun v => x ⟨v, hCX v.property⟩

def shellRestrict (x : RegionConfiguration q X) : RegionConfiguration q (X \ C) :=
  fun v => x ⟨v, (Finset.mem_sdiff.mp v.property).1⟩

def joinWithin (u : RegionConfiguration q C) (w : RegionConfiguration q (X \ C)) :
    RegionConfiguration q X := fun v =>
  if h : v.val ∈ C then u ⟨v,h⟩ else w ⟨v,Finset.mem_sdiff.mpr ⟨v.property,h⟩⟩

@[simp] theorem core_joinWithin (u : RegionConfiguration q C)
    (w : RegionConfiguration q (X \ C)) :
    coreRestrict C X hCX (joinWithin C X u w) = u := by
  funext v
  simp [coreRestrict,joinWithin,v.property]

@[simp] theorem shell_joinWithin (u : RegionConfiguration q C)
    (w : RegionConfiguration q (X \ C)) :
    shellRestrict C X (joinWithin C X u w) = w := by
  funext v
  simp [shellRestrict,joinWithin,(Finset.mem_sdiff.mp v.property).2]

@[simp] theorem joinWithin_restrict (x : RegionConfiguration q X) :
    joinWithin C X (coreRestrict C X hCX x) (shellRestrict C X x) = x := by
  funext v
  simp only [joinWithin, coreRestrict, shellRestrict]
  split_ifs <;> rfl

def splitEquiv : (RegionConfiguration q C × RegionConfiguration q (X \ C)) ≃
    RegionConfiguration q X where
  toFun z := joinWithin C X z.1 z.2
  invFun x := (coreRestrict C X hCX x, shellRestrict C X x)
  left_inv z := by ext <;> simp
  right_inv x := joinWithin_restrict C X hCX x

def insertion (u : EuclideanSpace ℂ (RegionConfiguration q C)) :
    Matrix (RegionConfiguration q X) (RegionConfiguration q (X \ C)) ℂ :=
  fun x w => if shellRestrict C X x = w then u (coreRestrict C X hCX x) else 0

@[simp] theorem insertion_join (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (x : RegionConfiguration q C) (w z : RegionConfiguration q (X \ C)) :
    insertion C X hCX u (joinWithin C X x w) z = if w = z then u x else 0 := by
  simp [insertion]

theorem insertion_isometry (u : EuclideanSpace ℂ (RegionConfiguration q C))
    (hu : ‖u‖ = 1) : (insertion C X hCX u).conjTranspose * insertion C X hCX u = 1 := by
  classical
  ext w z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp (splitEquiv (q := q) C X hCX)]
  simp only [splitEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, insertion_join]
  by_cases hwz : w = z
  · subst z
    simp only [apply_ite, ite_mul, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.one_apply_eq]
    simpa only [PiLp.inner_apply, RCLike.inner_apply, hu, one_pow,
      RCLike.ofReal_one, starRingEnd_apply, mul_comm] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u)
  · simp [Ne.symm hwz, Matrix.one_apply_ne hwz]

theorem liftBetween_core_join (a : Matrix (RegionConfiguration q C)
    (RegionConfiguration q C) ℂ) (x y : RegionConfiguration q C)
    (w z : RegionConfiguration q (X \ C)) :
    liftBetween hCX a (joinWithin C X x w) (joinWithin C X y z) =
      if w = z then a x y else 0 := by
  classical
  have heq : (∀ v : {v : Vertex L // v ∈ X}, v.val ∉ C →
      joinWithin C X x w v = joinWithin C X y z v) ↔ w = z := by
    constructor
    · intro h
      funext v
      simpa [joinWithin, (Finset.mem_sdiff.mp v.property).2] using
        (h ⟨v,(Finset.mem_sdiff.mp v.property).1⟩ (Finset.mem_sdiff.mp v.property).2)
    · rintro rfl v hv
      simp [joinWithin,hv]
  simp only [liftBetween, heq]
  change (if w = z then a (coreRestrict C X hCX (joinWithin C X x w))
    (coreRestrict C X hCX (joinWithin C X y z)) else 0) = _
  simp

include hCX in
theorem liftBetween_shell_join (b : Matrix (RegionConfiguration q (X \ C))
    (RegionConfiguration q (X \ C)) ℂ) (x y : RegionConfiguration q C)
    (w z : RegionConfiguration q (X \ C)) :
    liftBetween (Finset.sdiff_subset : X \ C ⊆ X) b
        (joinWithin C X x w) (joinWithin C X y z) =
      if x = y then b w z else 0 := by
  classical
  have heq : (∀ v : {v : Vertex L // v ∈ X}, v.val ∉ X \ C →
      joinWithin C X x w v = joinWithin C X y z v) ↔ x = y := by
    constructor
    · intro h
      funext v
      simpa [joinWithin, v.property] using h ⟨v, hCX v.property⟩
        (by simp [v.property])
    · rintro rfl v hv
      have hvc : v.val ∈ C := by simpa [v.property] using hv
      simp [joinWithin,hvc]
  simp only [liftBetween,heq]
  change (if x = y then b (shellRestrict C X (joinWithin C X x w))
    (shellRestrict C X (joinWithin C X y z)) else 0) = _
  simp

end PolynomialPEPS.Subvolume.Pinning

end

end OAI
