/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license.
Authors: OpenAI
-/
import OAI.AlgebraicGeometry.CartierSections.ConeTopology
import OAI.AlgebraicGeometry.CartierSections.FractionValuation
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.WithTop

namespace OAI

/-!
# Continuity of valuations on fraction fields

Local algebra for uniform Cartier sections.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace CartierSections

lemma nonnegToExtendedReal_eq_coe_toReal {x : ENNReal} (hx : x ≠ ⊤) :
    nonnegToExtendedReal x = (x.toReal : WithTop ℝ) := by
  lift x to NNReal using hx with x
  rfl

section FractionFieldTopology
variable {T A K : Type*} [TopologicalSpace T] [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

/-- A continuous family of finite local-ring valuations extends continuously
in the pointwise topology to the actual fraction field. The value at zero is
infinity; for a nonzero fraction this is the difference of two finite real
continuous functions. In particular, we do not apply continuity of subtraction
at infinity minus infinity. -/
lemma continuous_fractionValuation_apply
    (v : T → AddValuation A ENNReal)
    (hv : ∀ t a, a ≠ 0 → v t a ≠ ⊤)
    (hc : ∀ a, Continuous (fun t => v t a)) (x : K) :
    Continuous (fun t => fractionValuation (v t) (hv t) x) := by
  by_cases hx : x = 0
  · subst x
    simpa only [AddValuation.map_zero] using
      (continuous_const : Continuous (fun _ : T => (⊤ : WithTop ℝ)))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
  have ha : a ≠ 0 := by
    intro haz
    apply hx
    rw [← hab, haz, map_zero, zero_div]
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hc' (a : A) (ha : a ≠ 0) : Continuous (fun t => (v t a).toReal) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (ENNReal.continuousAt_toReal (hv t a ha)).comp
      (f := fun t => v t a) (hc a).continuousAt
  have heq : (fun t => fractionValuation (v t) (hv t) x) =
      (fun t => (((v t a).toReal - (v t b).toReal : ℝ) : WithTop ℝ)) := by
    funext t
    rw [← hab, fractionValuation_ratio,
      nonnegToExtendedReal_eq_coe_toReal (hv t a ha),
      nonnegToExtendedReal_eq_coe_toReal (hv t b hb')]
    rfl
  rw [heq]
  exact WithTop.continuous_coe.comp ((hc' a ha).sub (hc' b hb'))

lemma continuous_fractionValuation_evaluations
    (v : T → AddValuation A ENNReal)
    (hv : ∀ t a, a ≠ 0 → v t a ≠ ⊤)
    (hc : ∀ a, Continuous (fun t => v t a)) :
    Continuous (fun t => fun x : K => fractionValuation (v t) (hv t) x) :=
  continuous_pi (continuous_fractionValuation_apply v hv hc)

end FractionFieldTopology

section ExpandedFractionField
variable {σ k A K : Type*} [Fintype σ] [Field k] [CommRing A] [IsDomain A]
  [Algebra k A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- A genuine monomial valuation on a fraction field, constructed from an
injective formal-coordinate expansion of its local ring. -/
noncomputable def expandedFractionValuation
    (θ : A →ₐ[k] MvPowerSeries σ k) (hθ : Function.Injective θ)
    (w : σ → NNReal) : AddValuation K (WithTop ℝ) :=
  fractionValuation (expansionValuation θ w)
    (fun _ hf => (expansionValuation_finite θ hθ w hf).ne)

@[simp] lemma expandedFractionValuation_regular
    (θ : A →ₐ[k] MvPowerSeries σ k) (hθ : Function.Injective θ)
    (w : σ → NNReal) (a : A) :
    expandedFractionValuation (K := K) θ hθ w (algebraMap A K a) =
      nonnegToExtendedReal (expansionValuation θ w a) :=
  fractionValuation_algebraMap _ _ _

lemma continuous_expandedFractionValuation_evaluations
    (θ : A →ₐ[k] MvPowerSeries σ k) (hθ : Function.Injective θ) :
    Continuous (fun w : σ → NNReal => fun x : K =>
      expandedFractionValuation θ hθ w x) :=
  continuous_fractionValuation_evaluations (expansionValuation θ)
    (fun w _ hf => (expansionValuation_finite θ hθ w hf).ne)
    (continuous_monomial_evaluation θ)

/-- Compactness in pointwise *rational*-function evaluation, including zero
weights, ties between monomials, and fractions having negative value. -/
lemma isCompact_expandedFractionValuation_cone
    (θ : A →ₐ[k] MvPowerSeries σ k) (hθ : Function.Injective θ)
    (a : σ → NNReal) (ha : ∀ i, 0 < a i) :
    IsCompact ((fun w : σ → NNReal => fun x : K =>
      expandedFractionValuation θ hθ w x) '' normalizedWeights a) :=
  (isCompact_normalizedWeights a ha).image
    (continuous_expandedFractionValuation_evaluations θ hθ)

end ExpandedFractionField
end CartierSections

end

end OAI
