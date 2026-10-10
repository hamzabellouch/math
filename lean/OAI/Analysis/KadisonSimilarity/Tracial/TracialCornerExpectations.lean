import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner
import OAI.Analysis.KadisonSimilarity.Tracial.TracialExpectations

namespace OAI

/-! Restricting a tracial expectation to a corner. The normalized corner
trace and the restricted expectation are constructed from the ambient ones. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CStarCorner

variable (p : P) (hp : IsStarProjection p)

/-- The part of an ambient unital star algebra lying in the corner. -/
def subalgebra (A : StarSubalgebra ℂ P) (hpA : p ∈ A) :
    StarSubalgebra ℂ (CStarCorner p hp) where
  carrier := {x | (x : P) ∈ A}
  zero_mem' := A.zero_mem
  one_mem' := by
    change ((1 : CStarCorner p hp) : P) ∈ A
    rw [coe_one]
    exact hpA
  add_mem' := fun ha hb => A.add_mem ha hb
  mul_mem' := fun ha hb => A.mul_mem ha hb
  algebraMap_mem' c := by
    change ((algebraMap ℂ (CStarCorner p hp) c : CStarCorner p hp) : P) ∈ A
    rw [Algebra.algebraMap_eq_smul_one]
    change c • ((1 : CStarCorner p hp) : P) ∈ A
    rw [coe_one]
    exact A.smul_mem hpA c
  star_mem' := by
    intro a ha
    change star (a : P) ∈ A
    exact star_mem ha

@[simp] theorem mem_subalgebra (A : StarSubalgebra ℂ P) (hpA : p ∈ A)
    (x : CStarCorner p hp) : x ∈ subalgebra p hp A hpA ↔ (x : P) ∈ A := Iff.rfl

/-- Normalize the ambient trace by the trace of the corner identity. -/
def normalizedTrace (τ : P →ₗ[ℂ] ℂ) : CStarCorner p hp →ₗ[ℂ] ℂ where
  toFun x := (τ p)⁻¹ * τ (x : P)
  map_add' x y := by simp only [NonUnitalStarSubalgebra.coe_add, map_add, mul_add]
  map_smul' c x := by
    change (τ p)⁻¹ * τ (c • (x : P)) = c * ((τ p)⁻¹ * τ (x : P))
    rw [map_smul, smul_eq_mul]
    ring

@[simp] theorem normalizedTrace_apply (τ : P →ₗ[ℂ] ℂ) (x : CStarCorner p hp) :
    normalizedTrace p hp τ x = (τ p)⁻¹ * τ (x : P) := rfl

theorem normalizedTrace_one (τ : P →ₗ[ℂ] ℂ) (ht : τ p ≠ 0) :
    normalizedTrace p hp τ 1 = 1 := by
  rw [normalizedTrace_apply, coe_one, inv_mul_cancel₀ ht]

theorem normalizedTrace_tracial (τ : P →ₗ[ℂ] ℂ)
    (htr : ∀ x y, τ (x * y) = τ (y * x)) (x y : CStarCorner p hp) :
    normalizedTrace p hp τ (x * y) = normalizedTrace p hp τ (y * x) := by
  change (τ p)⁻¹ * τ ((x : P) * (y : P)) = (τ p)⁻¹ * τ ((y : P) * (x : P))
  rw [htr]

theorem normalizedTrace_faithful (τ : P →ₗ[ℂ] ℂ) (ht : τ p ≠ 0)
    (hf : ∀ x, τ (star x * x) = 0 → x = 0)
    (x : CStarCorner p hp) (hx : normalizedTrace p hp τ (star x * x) = 0) :
    x = 0 := by
  apply Subtype.ext
  apply hf
  change (τ p)⁻¹ * τ (star (x : P) * (x : P)) = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero ht)

end CStarCorner

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P}
  (E : TracialExpectation τ C)
  (hf : ∀ x, τ (star x * x) = 0 → x = 0)
  (htr : ∀ x y, τ (x * y) = τ (y * x))
  (p : P) (hp : IsStarProjection p) (hpC : p ∈ C)

include hf htr hpC in
/-- Bimodularity makes the ambient expectation preserve the corner. -/
theorem map_mem_corner (x : CStarCorner p hp) :
    E.map (x : P) ∈ cstarCornerSubalgebra p hp := by
  constructor
  · rw [← E.map_mul_left hf p (x : P) hpC, x.property.1]
  · rw [← E.map_mul_right hf htr (x : P) p hpC, x.property.2]

/-- The restriction is trace preserving for the normalized corner trace. -/
def corner : TracialExpectation (CStarCorner.normalizedTrace p hp τ)
    (CStarCorner.subalgebra p hp C hpC) where
  map :=
    { toFun := fun x => ⟨E.map (x : P), E.map_mem_corner hf htr p hp hpC x⟩
      map_add' := fun x y => Subtype.ext (E.map.map_add (x : P) (y : P))
      map_smul' := fun c x => Subtype.ext (E.map.map_smul c (x : P)) }
  range x := E.range (x : P)
  pairing x c hc := by
    change (τ p)⁻¹ * τ ((c : P) * E.map (x : P)) =
      (τ p)⁻¹ * τ ((c : P) * (x : P))
    rw [E.pairing (x : P) (c : P) hc]

@[simp] theorem corner_map_coe (x : CStarCorner p hp) :
    ((E.corner hf htr p hp hpC).map x : P) = E.map (x : P) := rfl

include hf htr in
/-- The ambient expectation formula used in the dihedral corner follows
from freeness in the normalized corner, rather than being extra data. -/
theorem free_corner_compression (ht : τ p ≠ 0)
    (D : StarSubalgebra ℂ P) (hpD : p ∈ D)
    (hfree : ScalarFree (CStarCorner.normalizedTrace p hp τ)
      (CStarCorner.subalgebra p hp D hpD) (CStarCorner.subalgebra p hp C hpC))
    (e b : CStarCorner p hp) (he : (e : P) ∈ D) (hb : (b : P) ∈ C)
    (hb0 : τ (b : P) = 0) :
    E.map ((e : P) * (b : P) * (e : P)) =
      ((τ p)⁻¹ * τ (e : P)) ^ 2 • (b : P) := by
  have h := (E.corner hf htr p hp hpC).free_compression
    (CStarCorner.normalizedTrace_faithful p hp τ ht hf)
    (CStarCorner.normalizedTrace_one p hp τ ht)
    (CStarCorner.normalizedTrace_tracial p hp τ htr) hfree (e := e) (b := b) he hb
    (by simp only [CStarCorner.normalizedTrace_apply, hb0, mul_zero])
  exact congrArg (fun x : CStarCorner p hp => (x : P)) h

end TracialExpectation
end KadisonSimilarity

end

end OAI
