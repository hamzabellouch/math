import Mathlib
import OAI.Analysis.FreeWords.UnitaryExtension

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKProjectionSupport

namespace KKProjectionSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A]

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance polarApproximationPartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance polarApproximationPreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance polarApproximationLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance polarApproximationStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem polar_unitary_factorization (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hM : IsFactor M) (a : ConcreteAlgebra M) :
    ∃ u : unitary (ConcreteAlgebra M),
      (u : ConcreteAlgebra M)*cfc Real.sqrt (star a*a)=a := by
  let S : ConcreteAlgebra M := cfc Real.sqrt (star a*a)
  have hScoe : (S : H →L[ℂ] H)=KKPolarSupport.opAbs (a : H →L[ℂ] H) := by
    exact M.toStarSubalgebra.subtype.map_cfc Real.sqrt (star a*a)
  obtain ⟨v,hvM,hva,hpi,hv,hker⟩ := KKPolarSupport.polar_decomposition M
    (a : H →L[ℂ] H) a.property
  let V : ConcreteAlgebra M := ⟨v,hvM⟩
  have hV : Partial V := Subtype.ext hv
  have hVa : V*S=a := by
    apply Subtype.ext
    change v*(S : H →L[ℂ] H)=(a : H →L[ℂ] H)
    rw [hScoe]; exact hva
  have hS : IsSelfAdjoint S := IsSelfAdjoint.cfc
  have hSS : S*S=star a*a := by
    apply Subtype.ext
    change (S : H →L[ℂ] H)*(S : H →L[ℂ] H)=star (a : H →L[ℂ] H)*(a : H →L[ℂ] H)
    rw [hScoe]; exact KKPolarSupport.opAbs_mul_self _
  have hPS := polar_initial_support hV hS hVa hSS
  obtain ⟨u,hu⟩ := partial_unitary_extension M τ hM V hV
  refine ⟨u,?_⟩
  change (u : ConcreteAlgebra M)*S=a
  calc
    (u : ConcreteAlgebra M)*S=(u : ConcreteAlgebra M)*((star V*V)*S) := by rw [hPS]
    _=((u : ConcreteAlgebra M)*(star V*V))*S := (mul_assoc _ _ _).symm
    _=a := by rw [hu,hVa]

theorem sqrt_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t-1)^2 ≤ (t-1)^2 := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  have hm : 0 ≤ Real.sqrt t*(Real.sqrt t+2)*(Real.sqrt t-1)^2 :=
    mul_nonneg (mul_nonneg hs (by linarith)) (sq_nonneg _)
  conv_rhs => rw [← hsq]
  nlinarith only [hm]

theorem trace_polar_unitary_approximation (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hM : IsFactor M) (a : ConcreteAlgebra M) :
    ∃ u : unitary (ConcreteAlgebra M),
      traceNorm τ (a-(u : ConcreteAlgebra M)) ≤ traceNorm τ (star a*a-1) := by
  obtain ⟨u,hu⟩ := polar_unitary_factorization M τ hM a
  let T := star a*a
  let S := cfc Real.sqrt T
  have hT : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a)
  have hS : IsSelfAdjoint S := IsSelfAdjoint.cfc
  have hU : (u : ConcreteAlgebra M)*S=a := hu
  have hdiff : a-(u : ConcreteAlgebra M)=(u : ConcreteAlgebra M)*(S-1) := by
    rw [mul_sub,mul_one,hU]
  have hsq : star (a-(u : ConcreteAlgebra M))*(a-(u : ConcreteAlgebra M))=(S-1)^2 := by
    rw [hdiff,star_mul,star_sub,hS.star_eq,star_one]
    calc
      (S-1)*star (u : ConcreteAlgebra M)*((u : ConcreteAlgebra M)*(S-1)) =
          (S-1)*(star (u : ConcreteAlgebra M)*(u : ConcreteAlgebra M))*(S-1) := by simp only [mul_assoc]
      _=(S-1)^2 := by rw [Unitary.coe_star_mul_self,mul_one,sq]
  have hsqT : star (star a*a-1)*(star a*a-1)=(T-1)^2 := by
    change star (T-1)*(T-1)=(T-1)^2
    rw [star_sub,hT.star_eq,star_one,sq]
  have hle : (S-1)^2 ≤ (T-1)^2 := by
    calc
      (S-1)^2 = cfc (fun t : ℝ => (Real.sqrt t-1)^2) T := by
        rw [cfc_pow (fun t : ℝ => Real.sqrt t-1) 2 T (by fun_prop) hT,
          cfc_sub Real.sqrt (fun _ : ℝ => 1) T (by fun_prop) (by fun_prop),
          cfc_const (1 : ℝ) T hT]
        simp only [map_one]; rfl
      _ ≤ cfc (fun t : ℝ => (t-1)^2) T := by
        apply (cfc_le_iff (fun t : ℝ => (Real.sqrt t-1)^2) (fun t : ℝ => (t-1)^2) T
          (by fun_prop) (by fun_prop) hT).mpr
        intro t ht
        exact sqrt_sub_one_sq_le (spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) ht)
      _ = (T-1)^2 := by
        rw [cfc_pow (fun t : ℝ => t-1) 2 T (by fun_prop) hT,
          cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) T (by fun_prop) (by fun_prop),
          cfc_id' ℝ T, cfc_const (1 : ℝ) T hT, map_one]
  have htrace : τ.map ((S-1)^2) ≤ τ.map ((T-1)^2) := OrderHomClass.mono (tracePositive τ) hle
  refine ⟨u,?_⟩
  unfold traceNorm
  rw [hsq,hsqT]
  exact Real.sqrt_le_sqrt (Complex.le_def.mp htrace).1

end

end KKProjectionSupport
end

end OAI
