import Mathlib
import OAI.Analysis.FreeWords.FiniteDimensionalWitness
import OAI.Analysis.FreeWords.VariableUltraAlgebra

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKUltraTrace KKFactorSupport

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : StarSubalgebra ℂ A) [IsClosed (R : Set A)]

local instance subTraceOrder : PartialOrder R := CStarAlgebra.spectralOrder _

local instance : LE R := (subTraceOrder R).toLE

local instance : Preorder R := (subTraceOrder R).toPreorder

local instance : StarOrderedRing R := CStarAlgebra.spectralOrderedRing _

def subTrace (τ : A →ₚ[ℂ] ℂ) : R →ₚ[ℂ] ℂ where
  toLinearMap := τ.toLinearMap.comp R.subtype.toLinearMap
  monotone' := by
    intro x y hxy
    apply τ.monotone'
    apply sub_nonneg.mp
    obtain ⟨v,hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
    have he : y.val-x.val=star v.val*v.val := congrArg Subtype.val hv
    change 0≤y.val-x.val
    rw [he]
    exact star_mul_self_nonneg _

@[simp] theorem subTrace_apply (τ : A →ₚ[ℂ] ℂ) (x : R) : subTrace R τ x=τ x.val := rfl

theorem gns_subTrace_norm (τ : A →ₚ[ℂ] ℂ) (x : R) :
    ‖gnsVector (subTrace R τ) x‖=‖gnsVector τ x.val‖ := by
  rw [gns_norm_sqrt,gns_norm_sqrt]
  rfl

theorem gns_subTrace_injective (τ : A →ₚ[ℂ] ℂ)
    (hinj : Function.Injective (gnsVector τ)) : Function.Injective (gnsVector (subTrace R τ)) := by
  intro x y hxy
  have hz : ‖gnsVector (subTrace R τ) (x-y)‖=0 := by
    rw [map_sub,hxy,sub_self,norm_zero]
  rw [gns_subTrace_norm] at hz
  change ‖gnsVector τ (x.val-y.val)‖=0 at hz
  apply Subtype.ext
  apply hinj
  exact sub_eq_zero.mp (by simpa only [map_sub] using norm_eq_zero.mp hz)

theorem finite_subalgebra_commutator_witness [FiniteDimensional ℂ R]
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ x y, τ (x*y)=τ (y*x)) (h1 : τ 1=1)
    (hinj : Function.Injective (gnsVector τ))
    (hcenter : ∀ a : R, (∀ b : R, Commute a b) → ∃ c : ℂ, a=c•1)
    (x : A) (hx : x∈R) : ∃ u : unitary A, u.val∈R ∧
      ‖gnsVector τ (x-τ x•1)‖≤2*‖gnsVector τ (x*u.val-u.val*x)‖ := by
  let a : R := ⟨x,hx⟩
  obtain ⟨v,hv⟩ := finite_commutator_witness (subTrace R τ)
    (fun p q => htr p.val q.val) h1 (gns_subTrace_injective R τ hinj) hcenter a
  let u : unitary A := ⟨v.val.val,Unitary.map_mem R.subtype v.property⟩
  refine ⟨u,v.val.property,?_⟩
  rw [gns_subTrace_norm,gns_subTrace_norm] at hv
  exact hv

end

end KKVariableUltra
end

end OAI
