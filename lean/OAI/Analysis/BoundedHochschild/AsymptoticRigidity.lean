import Mathlib
import OAI.Analysis.BoundedHochschild.FirstLetter
import OAI.Analysis.BoundedHochschild.Ultrapowers

namespace OAI

/-! Asymptotic first-letter identities and endpoint rigidity. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildFirstLetter
open Filter Topology
open scoped ComplexOrder
open HochschildRigidity TracialUltrapower HochschildUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 

theorem asymptotic_first_letter_rigidity
    (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A) (hR : BallSequential τ.toPreGNS R)
    (u : ℕ → FreeGroup ℕ →* unitary A)
    (hfree : ∀ g : FreeGroup ℕ, g ≠ 1 →
      Tendsto (fun j => τ (u j g : A)) atTop (nhds 0))
    (a b : A)
    (hw : ∀ (g : FreeGroup ℕ) i t l, g.toWord = (i,t)::l →
      (g.toWord.map Prod.fst).Nodup →
      Tendsto (fun j => ‖τ.toPreGNS (R (u j g : A) - (if t then a else b)*(u j g : A))‖)
        atTop (nhds 0)) : a = b := by
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hm : BallModulus (traceHilbertMap τ h1) R :=
    (ballSequential_iff_modulus _ _).mp hR
  apply constant_injective τ h1 ω htr hf
  apply countable_first_letter_rigidity (quotientTrace τ h1 ω htr)
    (quotientFamily τ h1 ω htr u) (quotientTrace_one τ h1 ω htr)
    (quotientFamily_star τ h1 ω htr u)
    (fun g hg => quotientFamily_trace_zero τ h1 ω htr u g hω (hfree g hg))
    (quotientTrace_tracial τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr)
    (HochschildUltrapower.map τ h1 ω htr R hm)
  · exact (ballSequential_iff_modulus _ _).mpr (map_modulus τ h1 ω htr R hm)
  · intro g i t l hword hnodup
    have hh := map_asymptotic_identity τ h1 ω htr u g hω R hm (if t then a else b)
      (hw g i t l hword hnodup)
    cases t <;> exact hh

end HochschildFirstLetter

namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable {G : Type*} [Group G]

lemma map_asymptotic_identity_sequence (u : ℕ → G →* unitary A) (g : G)
    (hω : (ω : Filter ℕ) ≤ atTop)
    (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) (a : ℕ →ᵇ A)
    (ha : Tendsto (fun j => ‖τ.toPreGNS (R (u j g : A) - a j*(u j g : A))‖) atTop (nhds 0)) :
    map τ h1 ω htr R hR (quotientFamily τ h1 ω htr u g) =
      quotientHom τ h1 ω htr a * quotientFamily τ h1 ω htr u g := by
  apply sub_eq_zero.mp
  change (Ideal.Quotient.mk (ideal τ h1 ω htr))
    (R.compLeftContinuousBounded ℕ (boundedHom u g) - a * boundedHom u g) = 0
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  change _ ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  rw [mem_nullSubmodule]
  exact ha.mono_left hω

end HochschildUltrapower

namespace HochschildFirstLetter
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open HochschildRigidity TracialUltrapower HochschildUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 

theorem asymptotic_first_letter_endpoints
    (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (R : A →L[ℂ] A) (hR : BallSequential τ.toPreGNS R)
    (u : ℕ → FreeGroup ℕ →* unitary A)
    (hfree : ∀ g : FreeGroup ℕ, g ≠ 1 →
      Tendsto (fun j => τ (u j g : A)) atTop (nhds 0))
    (a b : ℕ →ᵇ A)
    (hw : ∀ (g : FreeGroup ℕ) i t l, g.toWord = (i,t)::l →
      (g.toWord.map Prod.fst).Nodup →
      Tendsto (fun j => ‖τ.toPreGNS (R (u j g : A) - (if t then a j else b j)*(u j g : A))‖)
        atTop (nhds 0)) :
    Tendsto (fun j => ‖τ.toPreGNS (a j - b j)‖) atTop (nhds 0) := by
  rw [Filter.tendsto_iff_ultrafilter]
  intro ω hω
  have hm : BallModulus (traceHilbertMap τ h1) R :=
    (ballSequential_iff_modulus _ _).mp hR
  have he : quotientHom τ h1 ω htr a = quotientHom τ h1 ω htr b := by
    apply countable_first_letter_rigidity (quotientTrace τ h1 ω htr)
      (quotientFamily τ h1 ω htr u) (quotientTrace_one τ h1 ω htr)
      (quotientFamily_star τ h1 ω htr u)
      (fun g hg => quotientFamily_trace_zero τ h1 ω htr u g hω (hfree g hg))
      (quotientTrace_tracial τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr)
      (HochschildUltrapower.map τ h1 ω htr R hm)
    · exact (ballSequential_iff_modulus _ _).mpr (map_modulus τ h1 ω htr R hm)
    · intro g i t l hword hnodup
      cases t with
      | false =>
        exact map_asymptotic_identity_sequence τ h1 ω htr u g hω R hm b
          (hw g i false l hword hnodup)
      | true =>
        exact map_asymptotic_identity_sequence τ h1 ω htr u g hω R hm a
          (hw g i true l hword hnodup)
  have hz : Ideal.Quotient.mk (ideal τ h1 ω htr) (a-b) = 0 := by
    change quotientHom τ h1 ω htr (a-b) = 0
    rw [map_sub,he,sub_self]
  have ha := Ideal.Quotient.eq_zero_iff_mem.mp hz
  change (a-b) ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ) at ha
  rw [mem_nullSubmodule] at ha
  exact ha

end HochschildFirstLetter
end

end OAI
