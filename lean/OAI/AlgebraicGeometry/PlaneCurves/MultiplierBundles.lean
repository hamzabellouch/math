import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ZPow
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace OAI

/-!
# Multiplier quotient actions, projections, topology, and local charts; The multiplicative complex torus as a period quotient
-/

section

namespace Nagata.W21

/-- The total space before taking the multiplicative-period quotient. -/
abbrev MultiplicativeLineCover (R : Type*) [CommMonoid R] := Rˣ × R

/-- The manuscript's generator `(z,t) ↦ (τz, γz⁻ⁿt)` as an actual equivalence.
Units supply the inverse multiplier; invertibility is not assumed as a field. -/
def multiplierStep {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Equiv.Perm (MultiplicativeLineCover R) where
  toFun p := (τ * p.1, (γ * p.1 ^ (-n)) • p.2)
  invFun p := (τ⁻¹ * p.1, (γ * (τ⁻¹ * p.1) ^ (-n))⁻¹ • p.2)
  left_inv := by
    rintro ⟨z, t⟩
    change (τ⁻¹ * (τ * z), (γ * (τ⁻¹ * (τ * z)) ^ (-n))⁻¹ •
      ((γ * z ^ (-n)) • t)) = (z, t)
    rw [inv_mul_cancel_left, inv_smul_smul]
  right_inv := by
    rintro ⟨z, t⟩
    change (τ * (τ⁻¹ * z), (γ * (τ⁻¹ * z) ^ (-n)) •
      ((γ * (τ⁻¹ * z) ^ (-n))⁻¹ • t)) = (z, t)
    rw [mul_inv_cancel_left, smul_inv_smul]

@[simp] theorem multiplierStep_base {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MultiplicativeLineCover R) :
    (multiplierStep τ γ n p).1 = τ * p.1 := rfl

@[simp] theorem multiplierStep_fibre {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MultiplicativeLineCover R) :
    (multiplierStep τ γ n p).2 = (↑(γ * p.1 ^ (-n)) : R) * p.2 := rfl

/-- Every integer iterate exists because the generator has a proved inverse. -/
def multiplierIterate {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n k : ℤ) :
    Equiv.Perm (MultiplicativeLineCover R) := multiplierStep τ γ n ^ k

@[simp] theorem multiplierIterate_zero {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MultiplicativeLineCover R) :
    multiplierIterate τ γ n 0 p = p := by simp [multiplierIterate]

theorem multiplierIterate_add {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n k l : ℤ) (p : MultiplicativeLineCover R) :
    multiplierIterate τ γ n (k + l) p =
      multiplierIterate τ γ n k (multiplierIterate τ γ n l p) := by
  simp only [multiplierIterate, zpow_add, Equiv.Perm.mul_apply]

/-- Orbit relation of the explicit integer iterates. -/
def multiplierOrbitSetoid {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Setoid (MultiplicativeLineCover R) where
  r p q := ∃ k : ℤ, multiplierIterate τ γ n k p = q
  iseqv := {
    refl := fun p ↦ ⟨0, multiplierIterate_zero τ γ n p⟩
    symm := by
      intro p q h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      calc
        multiplierIterate τ γ n (-k) q =
            multiplierIterate τ γ n (-k) (multiplierIterate τ γ n k p) := by rw [hk]
        _ = multiplierIterate τ γ n (-k + k) p :=
          (multiplierIterate_add τ γ n (-k) k p).symm
        _ = p := by rw [Int.add_left_neg, multiplierIterate_zero]
    trans := by
      intro p q r hp hq
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      refine ⟨l + k, ?_⟩
      rw [multiplierIterate_add, hk, hl] }

def MultiplierQuotient {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) : Type _ :=
  Quotient (multiplierOrbitSetoid τ γ n)

instance {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Nonempty (MultiplierQuotient τ γ n) :=
  ⟨Quotient.mk _ (1, 1)⟩

end Nagata.W21

end

section

namespace Nagata.W21

/-- Two covering-space points represent the same point exactly when they differ
by an integer power of the period. -/
def torusOrbitSetoid {G : Type*} [CommGroup G] (τ : G) : Setoid G where
  r z z' := ∃ k : ℤ, τ ^ k * z = z'
  iseqv := {
    refl := fun z ↦ ⟨0, by rw [zpow_zero, one_mul]⟩
    symm := by
      intro z z' h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      rw [← hk, ← mul_assoc, ← zpow_add, Int.add_left_neg, zpow_zero, one_mul]
    trans := by
      intro z z' z'' h h'
      obtain ⟨k, hk⟩ := h
      obtain ⟨l, hl⟩ := h'
      exact ⟨l + k, by rw [zpow_add, mul_assoc, hk, hl]⟩ }

/-- The multiplicative quotient; for the source torus use `G = ℂˣ`. -/
def TorusPoint {G : Type*} [CommGroup G] (τ : G) : Type _ :=
  Quotient (torusOrbitSetoid τ)

def torusPointMk {G : Type*} [CommGroup G] (τ z : G) : TorusPoint τ :=
  Quotient.mk _ z

instance {G : Type*} [CommGroup G] (τ : G) : Nonempty (TorusPoint τ) :=
  ⟨torusPointMk τ 1⟩

theorem torusPointMk_eq_iff {G : Type*} [CommGroup G] (τ z z' : G) :
    torusPointMk τ z = torusPointMk τ z' ↔ ∃ k : ℤ, τ ^ k * z = z' := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := torusOrbitSetoid τ) h

/-- Bridge to the literal scalar equation used in the common logarithmic chart.
The source's nonzero complex coordinates are represented by actual units. -/
theorem torusOrbitSetoid_iff_coe {R : Type*} [CommGroupWithZero R] (τ z z' : Rˣ) :
    torusOrbitSetoid τ z z' ↔ ∃ k : ℤ, (z' : R) = (τ : R) ^ k * (z : R) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using
      (congrArg (fun u : Rˣ ↦ (u : R)) hk).symm
  · rintro ⟨k, hk⟩
    refine ⟨k, Units.ext ?_⟩
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using hk.symm

end Nagata.W21

end

section

/-! The explicit multiplier orbit quotient projects to the actual base quotient. -/
namespace Nagata.W21

@[simp] theorem multiplierStep_inv_base {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MultiplicativeLineCover R) :
    ((multiplierStep τ γ n)⁻¹ p).1 = τ⁻¹ * p.1 := rfl

/-- Every iterate covers multiplication by the same power of the period. -/
theorem multiplierIterate_base {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n k : ℤ) (p : MultiplicativeLineCover R) :
    (multiplierIterate τ γ n k p).1 = τ ^ k * p.1 := by
  have hpos : ∀ j : ℕ, ∀ p : MultiplicativeLineCover R,
      (((multiplierStep τ γ n) ^ j) p).1 = τ ^ j * p.1 := by
    intro j
    induction j with
    | zero => intro p; simp
    | succ j ih =>
      intro p
      simp only [pow_succ', Equiv.Perm.mul_apply, multiplierStep_base, ih, mul_assoc]
  have hneg : ∀ j : ℕ, ∀ p : MultiplicativeLineCover R,
      ((((multiplierStep τ γ n)⁻¹) ^ j) p).1 = (τ⁻¹) ^ j * p.1 := by
    intro j
    induction j with
    | zero => intro p; simp
    | succ j ih =>
      intro p
      simp only [pow_succ', Equiv.Perm.mul_apply, multiplierStep_inv_base, ih, mul_assoc]
  cases k with
  | ofNat j =>
    simpa only [multiplierIterate, Int.ofNat_eq_natCast, zpow_natCast] using hpos j p
  | negSucc j =>
    simpa only [multiplierIterate, zpow_negSucc, ← inv_pow] using hneg (j + 1) p

/-- Quotienting the scalar multiplier action preserves its projection to the
base period quotient; this is not an asserted bundle structure. -/
def multiplierQuotientProjection {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    MultiplierQuotient τ γ n → TorusPoint τ :=
  Quotient.lift (fun p : MultiplicativeLineCover R ↦ torusPointMk τ p.1) (by
    intro p q h
    obtain ⟨k, hk⟩ := h
    apply (torusPointMk_eq_iff τ p.1 q.1).mpr
    refine ⟨k, ?_⟩
    rw [← multiplierIterate_base τ γ n k p, hk])

@[simp] theorem multiplierQuotientProjection_mk {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MultiplicativeLineCover R) :
    multiplierQuotientProjection τ γ n (Quotient.mk _ p) = torusPointMk τ p.1 := rfl

/-- Every base point has an actual point above it in the multiplier quotient. -/
theorem multiplierQuotientProjection_surjective {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) : Function.Surjective (multiplierQuotientProjection τ γ n) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  exact ⟨Quotient.mk _ (z, 1), rfl⟩

end Nagata.W21

end

section

namespace Nagata.W21

instance torusPointTopologicalSpace {G : Type*} [CommGroup G] [TopologicalSpace G]
    (τ : G) : TopologicalSpace (TorusPoint τ) :=
  inferInstanceAs (TopologicalSpace (Quotient (torusOrbitSetoid τ)))

instance multiplierQuotientTopologicalSpace {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [TopologicalSpace Rˣ] (τ γ : Rˣ) (n : ℤ) :
    TopologicalSpace (MultiplierQuotient τ γ n) :=
  inferInstanceAs (TopologicalSpace (Quotient (multiplierOrbitSetoid τ γ n)))

/-- The base uses the actual quotient topology of its period relation. -/
theorem isQuotientMap_torusPointMk {G : Type*} [CommGroup G] [TopologicalSpace G]
    (τ : G) : Topology.IsQuotientMap (torusPointMk τ) :=
  isQuotientMap_quotient_mk'

theorem continuous_torusPointMk {G : Type*} [CommGroup G] [TopologicalSpace G]
    (τ : G) : Continuous (torusPointMk τ) :=
  continuous_quotient_mk'

/-- The fibre projection is continuous for the two actual quotient topologies. -/
theorem continuous_multiplierQuotientProjection {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [TopologicalSpace Rˣ] (τ γ : Rˣ) (n : ℤ) :
    Continuous (multiplierQuotientProjection τ γ n) := by
  unfold multiplierQuotientProjection
  exact ((continuous_torusPointMk τ).comp continuous_fst).quotient_lift _

end Nagata.W21

end

section

namespace Nagata.W21

section TopologicalAction
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [TopologicalSpace Rˣ]
  [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]

 theorem continuous_multiplierStep (τ γ : Rˣ) (n : ℤ) :
    Continuous (multiplierStep τ γ n) := by
  change Continuous (fun p : MultiplicativeLineCover R ↦
    (τ * p.1, (γ * p.1 ^ (-n)) • p.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul (continuous_fst.zpow (-n))).smul continuous_snd)

 theorem continuous_multiplierStep_inv (τ γ : Rˣ) (n : ℤ) :
    Continuous ((multiplierStep τ γ n)⁻¹ : Equiv.Perm (MultiplicativeLineCover R)) := by
  change Continuous (fun p : MultiplicativeLineCover R ↦
    (τ⁻¹ * p.1, (γ * (τ⁻¹ * p.1) ^ (-n))⁻¹ • p.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul ((continuous_const.mul continuous_fst).zpow (-n))).inv.smul
      continuous_snd)

/-- All deck transformations are continuous, including negative iterates. -/
theorem continuous_multiplierIterate (τ γ : Rˣ) (n k : ℤ) :
    Continuous (multiplierIterate τ γ n k) := by
  have hpos : ∀ j : ℕ, Continuous ((multiplierStep τ γ n) ^ j) := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, Equiv.Perm.coe_one] using
        (continuous_id : Continuous (fun p : MultiplicativeLineCover R ↦ p))
    | succ j ih =>
      simpa only [pow_succ', Equiv.Perm.coe_mul] using
        (continuous_multiplierStep τ γ n).comp ih
  have hneg : ∀ j : ℕ, Continuous (((multiplierStep τ γ n)⁻¹) ^ j) := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, Equiv.Perm.coe_one] using
        (continuous_id : Continuous (fun p : MultiplicativeLineCover R ↦ p))
    | succ j ih =>
      simpa only [pow_succ', Equiv.Perm.coe_mul] using
        (continuous_multiplierStep_inv τ γ n).comp ih
  cases k with
  | ofNat j =>
    simpa only [multiplierIterate, Int.ofNat_eq_natCast, zpow_natCast] using hpos j
  | negSucc j => simpa only [multiplierIterate, zpow_negSucc, ← inv_pow] using hneg (j + 1)

end TopologicalAction

/-- Canonical projection from the covering surface to its multiplier orbit quotient. -/
def multiplierQuotientMk {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ)
    (p : MultiplicativeLineCover R) : MultiplierQuotient τ γ n := Quotient.mk _ p

theorem multiplierQuotientMk_eq_iff {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p q : MultiplicativeLineCover R) :
    multiplierQuotientMk τ γ n p = multiplierQuotientMk τ γ n q ↔
      ∃ k : ℤ, multiplierIterate τ γ n k p = q := by
  constructor
  · exact Quotient.exact
  · intro h; exact Quotient.sound (s := multiplierOrbitSetoid τ γ n) h

theorem multiplierQuotientMk_preimage_image {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (U : Set (MultiplicativeLineCover R)) :
    multiplierQuotientMk τ γ n ⁻¹' (multiplierQuotientMk τ γ n '' U) =
      ⋃ k : ℤ, (multiplierIterate τ γ n k) ⁻¹' U := by
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨k, hk⟩ := (multiplierQuotientMk_eq_iff τ γ n p q).mp he.symm
    exact Set.mem_iUnion.mpr ⟨k, by simpa only [Set.mem_preimage, hk] using hq⟩
  · intro hp
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    exact ⟨multiplierIterate τ γ n k p, hk,
      ((multiplierQuotientMk_eq_iff τ γ n p _).mpr ⟨k, rfl⟩).symm⟩

section LocalChart
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [TopologicalSpace Rˣ]

theorem isQuotientMap_multiplierQuotientMk (τ γ : Rˣ) (n : ℤ) :
    Topology.IsQuotientMap (multiplierQuotientMk τ γ n) := isQuotientMap_quotient_mk'

theorem continuous_multiplierQuotientMk (τ γ : Rˣ) (n : ℤ) :
    Continuous (multiplierQuotientMk τ γ n) := continuous_quotient_mk'

variable [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]

theorem isOpenMap_multiplierQuotientMk (τ γ : Rˣ) (n : ℤ) :
    IsOpenMap (multiplierQuotientMk τ γ n) := by
  intro U hU
  apply (isQuotientMap_multiplierQuotientMk τ γ n).isOpen_preimage.mp
  rw [multiplierQuotientMk_preimage_image]
  exact isOpen_iUnion fun k : ℤ ↦ hU.preimage (continuous_multiplierIterate τ γ n k)

/-- An injective open subset of the covering surface yields an actual local
homeomorphism of the total multiplier quotient. -/
noncomputable def multiplierLocalChart (τ γ : Rˣ) (n : ℤ)
    (U : Set (MultiplicativeLineCover R)) (hU : IsOpen U)
    (hinj : Set.InjOn (multiplierQuotientMk τ γ n) U) :
    OpenPartialHomeomorph (MultiplicativeLineCover R) (MultiplierQuotient τ γ n) :=
  OpenPartialHomeomorph.ofContinuousOpen
    (Set.InjOn.toPartialEquiv (multiplierQuotientMk τ γ n) U hinj)
    (by change ContinuousOn (multiplierQuotientMk τ γ n) U
        exact (continuous_multiplierQuotientMk τ γ n).continuousOn)
    (by change IsOpenMap (multiplierQuotientMk τ γ n)
        exact isOpenMap_multiplierQuotientMk τ γ n)
    (by change IsOpen U; exact hU)

end LocalChart

end Nagata.W21

end

end OAI
