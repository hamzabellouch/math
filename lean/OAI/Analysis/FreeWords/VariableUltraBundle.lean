import Mathlib
import OAI.Analysis.FreeWords.FactorBase
import OAI.Analysis.FreeWords.TracialBicommutant
import OAI.Analysis.FreeWords.VariableUltraBall

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKUltraTrace KKTraceTransfer

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsVonNeumann (τ : A →ₚ[ℂ] ℂ) : VonNeumannAlgebra τ.GNS where
  toStarSubalgebra := bicommutantAlg τ.gnsStarAlgHom.range
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (bicommutantAlg τ.gnsStarAlgHom.range : Set (τ.GNS →L[ℂ] τ.GNS))) =
      (bicommutantAlg τ.gnsStarAlgHom.range : Set (τ.GNS →L[ℂ] τ.GNS))
    simp only [coe_bicommutantAlg,Set.centralizer_centralizer_centralizer]

local instance (τ : A →ₚ[ℂ] ℂ) : PartialOrder (ConcreteAlgebra (gnsVonNeumann τ)) := concreteOrder _

local instance (τ : A →ₚ[ℂ] ℂ) : LE (ConcreteAlgebra (gnsVonNeumann τ)) := (concreteOrder _).toLE

local instance (τ : A →ₚ[ℂ] ℂ) : Preorder (ConcreteAlgebra (gnsVonNeumann τ)) := (concreteOrder _).toPreorder

local instance (τ : A →ₚ[ℂ] ℂ) : StarOrderedRing (ConcreteAlgebra (gnsVonNeumann τ)) := concreteSOR _

def gnsNormalTrace (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) : FaithfulNormalTrace (gnsVonNeumann τ) where
  map := {
    toFun := fun x => ⟪gnsVector τ 1, x.val (gnsVector τ 1)⟫_ℂ
    map_add' := by
      intro x y
      change ⟪gnsVector τ 1, x.val (gnsVector τ 1) + y.val (gnsVector τ 1)⟫_ℂ = _
      exact inner_add_right _ _ _
    map_smul' := by intros; simp }
  positive x hx := hx.inner_nonneg_right _
  normalized := by
    change ⟪gnsVector τ 1, gnsVector τ 1⟫_ℂ = 1
    simpa only [gnsVector_inner,star_one,one_mul] using h1
  tracial := gns_bicommutantState_tracial τ htr
  faithful x hx hz := by
    obtain ⟨v,hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      ((ContinuousLinearMap.nonneg_iff_isPositive (f := x.val)).mpr hx)
    have hz' : ⟪gnsVector τ 1, x.val (gnsVector τ 1)⟫_ℂ=0 := hz
    rw [hv] at hz'
    change ⟪gnsVector τ 1, v.adjoint (v (gnsVector τ 1))⟫_ℂ=0 at hz'
    rw [ContinuousLinearMap.adjoint_inner_right] at hz'
    have hv0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hz'
    apply gns_bicommutant_separating τ htr x 0
    change x.val (gnsVector τ 1)=0
    rw [hv]
    change v.adjoint (v (gnsVector τ 1))=0
    rw [hv0,map_zero]
  normal r := by
    exact (ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val
      (gnsVector τ 1) (gnsVector τ 1)).continuousOn

@[simp] theorem gnsNormalTrace_image (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (a : A) :
    (gnsNormalTrace τ h1 htr).map (gnsBiHom τ a)=τ a := by
  change ⟪gnsVector τ 1, τ.gnsStarAlgHom a (gnsVector τ 1)⟫_ℂ=τ a
  rw [gnsStarAlgHom_vector,mul_one,gnsVector_inner,star_one,one_mul]

local instance (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)] :
    PartialOrder (coordinateAlgebra R) := CStarAlgebra.spectralOrder _

local instance (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)] :
    StarOrderedRing (coordinateAlgebra R) := CStarAlgebra.spectralOrderedRing _

theorem coordinate_gns_range (R : ℕ → StarSubalgebra ℂ A) [∀ j, IsClosed (R j : Set A)]
    (τ : A →ₚ[ℂ] ℂ) (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    (coordinateTrace R τ ω).gnsStarAlgHom.range = (gnsVonNeumann (coordinateTrace R τ ω)).toStarSubalgebra := by
  apply SetLike.coe_injective
  exact ((coe_bicommutantAlg _).trans
    (tracialGNS_bicommutant_of_closed_balls _ (coordinateTrace_tracial R τ ω htr)
      (coordinateVectorBall_isClosed R τ ω hω))).symm

end

end KKVariableUltra
end

end OAI
