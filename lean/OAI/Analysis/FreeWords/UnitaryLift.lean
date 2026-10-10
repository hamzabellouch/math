import Mathlib
import OAI.Analysis.FreeWords.PolarApproximation

namespace OAI

noncomputable section

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_norm_eq_sqrt (τ : A →ₚ[ℂ] ℂ) (x : A) :
    ‖gnsVector τ x‖ = Real.sqrt (τ (star x * x)).re := by
  rw [@norm_eq_sqrt_re_inner ℂ, gnsVector_inner]
  rfl

local instance unitaryLiftSequenceOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

local instance unitaryLiftSequenceSOR : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

@[simp] theorem ultraTrace_apply_value (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A) :
    ultraTrace τ ω x = ultraTraceValue τ ω x := rfl

theorem tendsto_gnsVector_norm (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A) :
    Tendsto (fun j => ‖gnsVector τ (x j)‖) (ω : Filter ℕ)
      (𝓝 (Real.sqrt ((ultraTrace τ ω) (star x * x)).re)) := by
  have ht := Real.continuous_sqrt.tendsto _ |>.comp
    (Complex.continuous_re.tendsto _ |>.comp (tendsto_ultraTraceValue τ ω (star x*x)))
  change Tendsto (fun j => Real.sqrt (τ (star (x j) * x j)).re) (ω : Filter ℕ) _ at ht
  simpa only [gnsVector_norm_eq_sqrt, ultraTrace_apply_value] using ht

theorem gnsStarAlgHom_zero_of_gnsNorm_tendsto_zero (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A)
    (hx : Tendsto (fun j => ‖gnsVector τ (x j)‖) (ω : Filter ℕ) (𝓝 0)) :
    (ultraTrace τ ω).gnsStarAlgHom x = 0 := by
  apply (tracial_gns_zero _ (ultraTrace_tracial τ ω htr) x).mpr
  have heq (j : ℕ) : τ (star (x j) * x j) = (‖gnsVector τ (x j)‖ : ℂ)^2 := by
    rw [← gnsVector_inner, inner_self_eq_norm_sq_to_K]
    rfl
  have hz : Tendsto (fun j => τ (star (x j) * x j)) (ω : Filter ℕ) (𝓝 0) := by
    have ht := (Complex.continuous_ofReal.tendsto 0 |>.comp hx).pow 2
    simpa only [heq, Function.comp_apply, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using ht
  exact tendsto_nhds_unique (tendsto_ultraTraceValue τ ω (star x*x)) hz

theorem ultrapower_unitary_lift_of_gns_approximation (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a*b) = τ (b*a)) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ A)
    (hx : (ultraTrace τ ω).gnsStarAlgHom x ∈
      unitary ((ultraTrace τ ω).GNS →L[ℂ] (ultraTrace τ ω).GNS))
    (happrox : ∀ j, ∃ u : unitary A,
      ‖gnsVector τ (x j - (u : A))‖ ≤ ‖gnsVector τ (star (x j) * x j - 1)‖) :
    ∃ y : ℕ →ᵇ A, (∀ j, y j ∈ unitary A) ∧
      (ultraTrace τ ω).gnsStarAlgHom y = (ultraTrace τ ω).gnsStarAlgHom x := by
  choose u hu using happrox
  let y : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => (u j : A)) continuous_of_discreteTopology ‖(1 : A)‖
    (fun j => by simpa only [mul_one] using (CStarRing.norm_coe_unitary_mul (u j) (1 : A)).le)
  let z : ℕ →ᵇ A := star x*x-1
  have hz : (ultraTrace τ ω).gnsStarAlgHom z = 0 := by
    change (ultraTrace τ ω).gnsStarAlgHom (star x*x-1) = 0
    rw [map_sub, map_mul, map_star, map_one, (Unitary.mem_iff.mp hx).1, sub_self]
  have hτz := (tracial_gns_zero _ (ultraTrace_tracial τ ω htr) z).mp hz
  have hlim : Tendsto (fun j => ‖gnsVector τ (z j)‖) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [hτz, Complex.zero_re, Real.sqrt_zero] using tendsto_gnsVector_norm τ ω z
  have hdiff : Tendsto (fun j => ‖gnsVector τ ((x-y) j)‖) (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun j => norm_nonneg _) _ hlim
    exact hu
  have he := gnsStarAlgHom_zero_of_gnsNorm_tendsto_zero τ htr ω (x-y) hdiff
  rw [map_sub, sub_eq_zero] at he
  exact ⟨y, fun j => (u j).property, he.symm⟩

end

end KKFactorSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport

open Filter Topology

open scoped BoundedContinuousFunction ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance unitaryLiftConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance unitaryLiftConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance unitaryLiftConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance unitaryLiftConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

local instance unitaryLiftConcreteSequenceOrder (M : VonNeumannAlgebra H) : PartialOrder (ℕ →ᵇ ConcreteAlgebra M) := CStarAlgebra.spectralOrder _

local instance unitaryLiftConcreteSequenceSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ℕ →ᵇ ConcreteAlgebra M) := CStarAlgebra.spectralOrderedRing _

theorem map_unitary_defect_eq_zero {A B : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B]
    [Algebra ℂ A] [Algebra ℂ B] (φ : A →⋆ₐ[ℂ] B) (x : A) (hx : φ x ∈ unitary B) : φ (star x*x-1)=0 := by
  rw [map_sub,map_mul,map_star,map_one,(Unitary.mem_iff.mp hx).1,sub_self]

theorem ultrapower_unitary_lift (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hM : KKFreeLiftFrontier.IsFactor M) (ω : Ultrafilter ℕ) (x : ℕ →ᵇ ConcreteAlgebra M)
    (hx : (ultraTrace (tracePositive τ) ω).gnsStarAlgHom x ∈
      unitary ((ultraTrace (tracePositive τ) ω).GNS →L[ℂ] (ultraTrace (tracePositive τ) ω).GNS)) :
    ∃ y : ℕ →ᵇ ConcreteAlgebra M, (∀ j, y j ∈ unitary (ConcreteAlgebra M)) ∧
      (ultraTrace (tracePositive τ) ω).gnsStarAlgHom y =
        (ultraTrace (tracePositive τ) ω).gnsStarAlgHom x := by
  apply ultrapower_unitary_lift_of_gns_approximation (tracePositive τ) τ.tracial ω x hx
  intro j
  obtain ⟨u, hu⟩ := trace_polar_unitary_approximation M τ hM (x j)
  refine ⟨u, ?_⟩
  rw [gnsVector_norm_eq_sqrt, gnsVector_norm_eq_sqrt]
  exact hu

end

end KKProjectionSupport
end

end OAI
