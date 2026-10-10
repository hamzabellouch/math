import Mathlib
import OAI.Analysis.BoundedHochschild.CStarQuotients
import OAI.Analysis.BoundedHochschild.TracialModulus

namespace OAI

/-! Tracial ultrapowers, quotient traces and bounded-ball maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

def ideal : Ideal (ℕ →ᵇ A) where
  carrier := nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  smul_mem' := fun x y hy => by
    change x*y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
    have hs := nullSubmodule_star τ h1 (ω : Filter ℕ) htr y hy
    have ht := nullSubmodule_mul_right τ h1 (ω : Filter ℕ) htr (star y) (star x) hs
    have hh := nullSubmodule_star τ h1 (ω : Filter ℕ) htr _ ht
    rw [star_mul,star_star,star_star] at hh
    exact hh

instance ideal_twoSided : (ideal τ h1 ω htr).IsTwoSided where
  mul_mem_of_left := fun {x} y hx => nullSubmodule_mul_right τ h1 (ω : Filter ℕ) htr x y hx

instance ideal_starClosed : HochschildCStarQuotient.StarClosed (ideal τ h1 ω htr) where
  star_mem := fun {x} hx => nullSubmodule_star τ h1 (ω : Filter ℕ) htr x hx

instance ideal_closed : IsClosed (ideal τ h1 ω htr : Set (ℕ →ᵇ A)) :=
  isClosed_nullSubmodule (traceHilbertMap τ h1) (ω : Filter ℕ)

abbrev Ultrapower := (ℕ →ᵇ A) ⧸ ideal τ h1 ω htr

instance ultrapowerCStar : CStarAlgebra (Ultrapower τ h1 ω htr) :=
  let _ := ideal_twoSided τ h1 ω htr
  let _ := ideal_starClosed τ h1 ω htr
  HochschildCStarQuotient.quotientCStarAlgebra (ideal τ h1 ω htr)

lemma norm_trace_le (a : A) : ‖τ a‖ ≤ ‖τ.toPreGNS a‖ := by
  have hin : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS a) = τ a := by
    simp [PositiveLinearMap.preGNS_inner_def]
  rw [← hin]
  have hone : ‖τ.toPreGNS 1‖ = 1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [hone,one_mul] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS 1) (τ.toPreGNS a)

def sequenceTrace (x : ℕ →ᵇ A) : ℂ := limUnder (ω : Filter ℕ) (fun j => τ (x j))

lemma tendsto_sequenceTrace (x : ℕ →ᵇ A) :
    Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds (sequenceTrace τ ω x)) := by
  have hb : ∀ j, τ (x j) ∈ Metric.closedBall 0 ‖x‖ := by
    intro j
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_trace_le τ h1 _).trans ((preGNS_norm_le τ h1 _).trans (x.norm_coe_le_norm j))
  obtain ⟨a,_,ha⟩ := (isCompact_closedBall (0:ℂ) ‖x‖).ultrafilter_le_nhds
    (ω.map (fun j => τ (x j))) (by
      rw [Ultrafilter.coe_map,le_principal_iff]
      change ∀ᶠ j in (ω : Filter ℕ), τ (x j) ∈ Metric.closedBall 0 ‖x‖
      exact Eventually.of_forall hb)
  have ht : Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds a) := ha
  simpa only [sequenceTrace,ht.limUnder_eq] using ht

def sequenceTraceLinear : (ℕ →ᵇ A) →ₗ[ℂ] ℂ where
  toFun := sequenceTrace τ ω
  map_add' x y := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (x+y))
    simpa only [BoundedContinuousFunction.add_apply,map_add] using
      (tendsto_sequenceTrace τ h1 ω x).add (tendsto_sequenceTrace τ h1 ω y)
  map_smul' c x := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (c • x))
    simpa only [BoundedContinuousFunction.smul_apply,map_smul,RingHom.id_apply] using
      (tendsto_sequenceTrace τ h1 ω x).const_smul c

lemma sequenceTrace_null (x : ℕ →ᵇ A) (hx : x ∈ ideal τ h1 ω htr) : sequenceTrace τ ω x = 0 := by
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => norm_trace_le τ h1 (x j))
  exact (mem_nullSubmodule _ _ x).mp hx

 
def quotientTraceLinear : Ultrapower τ h1 ω htr →ₗ[ℂ] ℂ :=
  (nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)).liftQ
    (sequenceTraceLinear τ h1 ω) (fun x hx => sequenceTrace_null τ h1 ω htr x hx)

@[simp] lemma quotientTraceLinear_mk (x : ℕ →ᵇ A) :
    quotientTraceLinear τ h1 ω htr (Ideal.Quotient.mk (ideal τ h1 ω htr) x) =
      sequenceTrace τ ω x := rfl

instance ultrapowerOrder : PartialOrder (Ultrapower τ h1 ω htr) :=
  CStarAlgebra.spectralOrder _

instance ultrapowerStarOrder : StarOrderedRing (Ultrapower τ h1 ω htr) :=
  CStarAlgebra.spectralOrderedRing _

lemma quotientTraceLinear_nonneg (X : Ultrapower τ h1 ω htr) (hX : 0 ≤ X) :
    0 ≤ quotientTraceLinear τ h1 ω htr X := by
  obtain ⟨Y,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective Y
  change 0 ≤ sequenceTrace τ ω (star y * y)
  apply ge_of_tendsto' (tendsto_sequenceTrace τ h1 ω _)
  intro j
  exact τ.map_nonneg (star_mul_self_nonneg (y j))

 
def quotientTrace : Ultrapower τ h1 ω htr →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (quotientTraceLinear τ h1 ω htr)
    (quotientTraceLinear_nonneg τ h1 ω htr)

@[simp] lemma quotientTrace_mk (x : ℕ →ᵇ A) :
    quotientTrace τ h1 ω htr (Ideal.Quotient.mk (ideal τ h1 ω htr) x) =
      sequenceTrace τ ω x := rfl

lemma quotientTrace_one : quotientTrace τ h1 ω htr 1 = 1 := by
  change sequenceTrace τ ω (1 : ℕ →ᵇ A) = 1
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _)
  change Tendsto (fun _ : ℕ => τ (1:A)) (ω : Filter ℕ) (nhds 1)
  rw [h1]
  exact tendsto_const_nhds

lemma quotientTrace_tracial (X Y : Ultrapower τ h1 ω htr) :
    quotientTrace τ h1 ω htr (X*Y) = quotientTrace τ h1 ω htr (Y*X) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective X
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective Y
  change sequenceTrace τ ω (x*y) = sequenceTrace τ ω (y*x)
  apply congrArg (limUnder (ω : Filter ℕ))
  funext j
  exact htr (x j) (y j)

lemma sequenceTrace_star_mul (x : ℕ →ᵇ A) :
    sequenceTrace τ ω (star x * x) =
      (sequenceTwoNorm (traceHilbertMap τ h1) ω x : ℂ)^2 := by
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _)
  have hh := ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω x)).pow 2
  convert hh using 1
  ext j
  exact (PositiveLinearMap.preGNS_norm_sq τ (τ.toPreGNS (x j))).symm

lemma quotientTrace_preGNS_norm (X : Ultrapower τ h1 ω htr) :
    ‖(quotientTrace τ h1 ω htr).toPreGNS X‖ =
      quotientTwoNorm (traceHilbertMap τ h1) ω X := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective X
  change ‖(quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x)‖ =
    sequenceTwoNorm (traceHilbertMap τ h1) ω x
  have hh := congrArg Complex.re
    (PositiveLinearMap.preGNS_norm_sq (quotientTrace τ h1 ω htr)
      ((quotientTrace τ h1 ω htr).toPreGNS (Ideal.Quotient.mk (ideal τ h1 ω htr) x)))
  change ((‖(quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x)‖ : ℂ)^2).re =
      (sequenceTrace τ ω (star x*x)).re at hh
  rw [sequenceTrace_star_mul τ h1 ω] at hh
  simp only [← Complex.ofReal_pow,Complex.ofReal_re] at hh
  have hn := sequenceTwoNorm_nonneg (traceHilbertMap τ h1) ω x
  nlinarith [norm_nonneg ((quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x))]

lemma quotientTrace_faithful (X : Ultrapower τ h1 ω htr)
    (hX : quotientTrace τ h1 ω htr (star X * X) = 0) : X = 0 := by
  apply (quotientTwoNorm_eq_zero_iff (traceHilbertMap τ h1) ω X).mp
  rw [← quotientTrace_preGNS_norm τ h1 ω htr]
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [hX]

end HochschildUltrapower

namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

 
def quotientHom : (ℕ →ᵇ A) →⋆ₐ[ℂ] Ultrapower τ h1 ω htr where
  toRingHom := Ideal.Quotient.mk (ideal τ h1 ω htr)
  commutes' _ := rfl
  map_star' _ := rfl

 
def constantSequence : A →⋆ₐ[ℂ] (ℕ →ᵇ A) where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def constant : A →⋆ₐ[ℂ] Ultrapower τ h1 ω htr :=
  (quotientHom τ h1 ω htr).comp constantSequence

lemma quotientTrace_constant (a : A) : quotientTrace τ h1 ω htr (constant τ h1 ω htr a) = τ a := by
  change sequenceTrace τ ω (BoundedContinuousFunction.const ℕ a) = τ a
  exact tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _) tendsto_const_nhds

lemma constant_injective (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) :
    Function.Injective (constant τ h1 ω htr) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hf
  rw [← quotientTrace_constant τ h1 ω htr, map_mul, map_star, map_sub, hab, sub_self,
    star_zero,zero_mul,map_zero]

variable {G : Type*} [Group G]

def boundedHom (u : ℕ → G →* unitary A) : G →* (ℕ →ᵇ A) where
  toFun g := BoundedContinuousFunction.mkOfBound
    ⟨fun j => (u j g : A), continuous_of_discreteTopology⟩ (2*‖(1:A)‖)
    (fun i j => by
      calc
        dist (u i g : A) (u j g : A) = ‖(u i g : A)-(u j g : A)‖ := dist_eq_norm _ _
        _ ≤ ‖(u i g : A)‖ + ‖(u j g : A)‖ := norm_sub_le _ _
        _ = 2*‖(1:A)‖ := by
          have hi := CStarRing.norm_coe_unitary_mul (u i g) (1:A)
          have hj := CStarRing.norm_coe_unitary_mul (u j g) (1:A)
          simp only [mul_one] at hi hj
          rw [hi,hj,two_mul])
  map_one' := by ext j; simp
  map_mul' g h := by ext j; simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma boundedHom_apply (u : ℕ → G →* unitary A) (g : G) (j : ℕ) :
    boundedHom u g j = (u j g : A) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma boundedHom_star (u : ℕ → G →* unitary A) (g : G) :
    star (boundedHom u g) = boundedHom u g⁻¹ := by
  ext j
  change star (u j g : A) = (u j g⁻¹ : A)
  rw [map_inv]
  rfl

def quotientFamily (u : ℕ → G →* unitary A) : G →* Ultrapower τ h1 ω htr :=
  (quotientHom τ h1 ω htr).toMonoidHom.comp (boundedHom u)

lemma quotientFamily_star (u : ℕ → G →* unitary A) (g : G) :
    star (quotientFamily τ h1 ω htr u g) = quotientFamily τ h1 ω htr u g⁻¹ := by
  change star (quotientHom τ h1 ω htr (boundedHom u g)) = _
  rw [← map_star,boundedHom_star]
  rfl

lemma quotientFamily_trace_zero (u : ℕ → G →* unitary A) (g : G)
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hg : Tendsto (fun j => τ (u j g : A)) atTop (nhds 0)) :
    quotientTrace τ h1 ω htr (quotientFamily τ h1 ω htr u g) = 0 := by
  exact tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (boundedHom u g)) (hg.mono_left hω)

 
def map (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) :
    Ultrapower τ h1 ω htr →L[ℂ] Ultrapower τ h1 ω htr :=
  quotientContinuousMap (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ) R hR

lemma map_modulus (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) :
    BallModulus (quotientTrace τ h1 ω htr).toPreGNS (map τ h1 ω htr R hR) := by
  have hm := quotientMap_ballModulus (traceHilbertMap τ h1) ω R hR
  intro r ε hε
  obtain ⟨δ,hδ,hmod⟩ := hm r ε hε
  refine ⟨δ,hδ,fun X hX hq => ?_⟩
  rw [quotientTrace_preGNS_norm] at hq ⊢
  have hn := quotientTwoNorm_nonneg (traceHilbertMap τ h1) ω X
  have hn' := quotientTwoNorm_nonneg (traceHilbertMap τ h1) ω (map τ h1 ω htr R hR X)
  have hout := hmod X hX (by simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hq)
  change |quotientTwoNorm (traceHilbertMap τ h1) ω (map τ h1 ω htr R hR X)| < ε at hout
  rwa [abs_of_nonneg hn'] at hout

lemma map_asymptotic_identity (u : ℕ → G →* unitary A) (g : G)
    (hω : (ω : Filter ℕ) ≤ atTop)
    (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) (a : A)
    (ha : Tendsto (fun j => ‖τ.toPreGNS (R (u j g : A) - a*(u j g : A))‖) atTop (nhds 0)) :
    map τ h1 ω htr R hR (quotientFamily τ h1 ω htr u g) =
      constant τ h1 ω htr a * quotientFamily τ h1 ω htr u g := by
  apply sub_eq_zero.mp
  change (Ideal.Quotient.mk (ideal τ h1 ω htr))
    (R.compLeftContinuousBounded ℕ (boundedHom u g) -
      BoundedContinuousFunction.const ℕ a * boundedHom u g) = 0
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  change _ ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  rw [mem_nullSubmodule]
  exact ha.mono_left hω

end HochschildUltrapower
end

end OAI
