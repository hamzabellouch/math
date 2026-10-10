import Mathlib
import OAI.Analysis.HardSphere.Collisions.InsertionCount
import OAI.Analysis.HardSphere.FormDomain.RayleighLarger

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma deficiency_penalty : ∃ C : ℝ, 0<C ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (r : ℝ), 0<r → 0<n →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (w : S → SmoothMultiplier 1 L),
    (∀ z X, conj ((w z).toFun X)=(w z).toFun X) →
    (∀ z, (∫ y : Torus L, ‖(w z).orbital y‖^2)=1) →
    (∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r) →
    ∀ (T k m : ℕ) (site : ℕ → S) (B E : ℝ),
    (∀ z, (w z).orbitalBound ≤ B) → (∀ z, (w z).orbitalEnergy ≤ E) →
    (∀ z, insertionCount site T z ≤ m) → C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → ∀ z, (closeLabels r (w z) Y).card ≤ k) →
    T*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 ≤ energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hins⟩ := local_insertion_iterated
  refine ⟨C,hC,?_⟩
  intro S _ n L r hr hn g hg w hw hwN hsep T k m site B E hB hE hct hs u hu hk
  obtain ⟨v,hv,hvn,hve⟩ := hins S n L r hr w hw hwN hsep T k m site B E hB hE hct hs u hu hk
  have hlow := hg.rayleigh_larger hn (Nat.le_add_right n T) v hv
  rw [hvn] at hlow
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (energy g/(n:ℝ))*((n+T:ℕ):ℝ)=energy g+(T:ℝ)*(energy g/(n:ℝ)) := by
    rw [Nat.cast_add,div_mul_eq_mul_div,mul_add,add_div,mul_div_cancel_right₀ _ hn0]
    ring
  rw [he] at hlow
  nlinarith

end HardSphere

end

end OAI
