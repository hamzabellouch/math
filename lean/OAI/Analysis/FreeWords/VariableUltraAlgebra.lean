import Mathlib
import OAI.Analysis.FreeWords.UltraTrace

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKUltraTrace

open scoped BoundedContinuousFunction ComplexOrder InnerProductSpace

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

def coordinateAlgebra (R : ℕ → StarSubalgebra ℂ A) : StarSubalgebra ℂ (ℕ →ᵇ A) where
  carrier := {x | ∀ j, x j ∈ R j}
  zero_mem' := fun j => (R j).zero_mem
  add_mem' := fun hx hy j => (R j).add_mem (hx j) (hy j)
  one_mem' := fun j => (R j).one_mem
  mul_mem' := fun hx hy j => (R j).mul_mem (hx j) (hy j)
  algebraMap_mem' := fun c j => (R j).algebraMap_mem c
  star_mem' := fun hx j => star_mem (hx j)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem mem_coordinateAlgebra (R : ℕ → StarSubalgebra ℂ A) (x : ℕ →ᵇ A) :
    x ∈ coordinateAlgebra R ↔ ∀ j, x j ∈ R j := Iff.rfl

instance coordinateAlgebra_closed (R : ℕ → StarSubalgebra ℂ A)
    [hR : ∀ j, IsClosed (R j : Set A)] :
    IsClosed (coordinateAlgebra R : Set (ℕ →ᵇ A)) := by
  change IsClosed {x : ℕ →ᵇ A | ∀ j, x j ∈ R j}
  have hset : {x : ℕ →ᵇ A | ∀ j, x j ∈ R j} =
      ⋂ j, (fun x : ℕ →ᵇ A => x j) ⁻¹' (R j : Set A) := by ext; simp
  rw [hset]
  apply isClosed_iInter
  intro j
  exact (hR j).preimage (by fun_prop)

variable (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]

local instance coordOrder : PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance coordLE : LE (coordinateAlgebra R) := (coordOrder R).toLE

local instance coordPreorder : Preorder (coordinateAlgebra R) := (coordOrder R).toPreorder

local instance coordSOR : StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

def coordinateTrace (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) : coordinateAlgebra R →ₚ[ℂ] ℂ where
  toLinearMap := (ultraTrace τ ω).toLinearMap.comp (coordinateAlgebra R).subtype.toLinearMap
  monotone' := by
    intro x y hxy
    apply (ultraTrace τ ω).monotone'
    apply sub_nonneg.mp
    obtain ⟨v,hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
    have he : y.val-x.val = star v.val*v.val := congrArg Subtype.val hv
    change 0 ≤ y.val-x.val
    rw [he]
    exact star_mul_self_nonneg _

@[simp] theorem coordinateTrace_apply (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (x : coordinateAlgebra R) : coordinateTrace R τ ω x = ultraTrace τ ω x.val := rfl

theorem coordinateTrace_one (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (h1 : τ 1=1) :
    coordinateTrace R τ ω 1=1 := ultraTrace_one τ ω h1

theorem coordinateTrace_tracial (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (x y : coordinateAlgebra R) :
    coordinateTrace R τ ω (x*y)=coordinateTrace R τ ω (y*x) :=
  ultraTrace_tracial τ ω htr x.val y.val

theorem gns_norm_sqrt (τ : A →ₚ[ℂ] ℂ) (x : A) :
    ‖gnsVector τ x‖ = Real.sqrt (τ (star x*x)).re := by
  rw [@norm_eq_sqrt_re_inner ℂ,gnsVector_inner]
  rfl

theorem coordinate_norm_tendsto (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (x : coordinateAlgebra R) :
    Tendsto (fun j => ‖gnsVector τ (x.val j)‖) (ω : Filter ℕ)
      (𝓝 ‖gnsVector (coordinateTrace R τ ω) x‖) := by
  rw [gns_norm_sqrt]
  have ht := Real.continuous_sqrt.tendsto _ |>.comp
    (Complex.continuous_re.tendsto _ |>.comp (tendsto_ultraTraceValue τ ω (star x.val*x.val)))
  change Tendsto (fun j => Real.sqrt (τ (star (x.val j)*x.val j)).re)
    (ω : Filter ℕ) (𝓝 (Real.sqrt (ultraTraceValue τ ω (star x.val*x.val)).re)) at ht
  simp only [gns_norm_sqrt]
  exact ht

end

end KKVariableUltra
end

end OAI
