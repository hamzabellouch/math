import OAI.Analysis.CircleDomains.Probability.LocalNullImage
import Mathlib.Topology.Path

namespace OAI

/-!
# From simple-arc payment to null trace images

Distinct points of a connected open subset of a locally connected metric
continuum can be joined there by a simple arc. The arc-existence hypothesis
is the local arcwise-connectedness theorem used by Lorimer (1981),
*Locally compact Hjelmslev planes and rings*, proof of Lemma 3.2,
pp. 1002–1003, displayed (*), DOI 10.4153/CJM-1981-077-5.
The null-image criterion derives the measure-theoretic conclusion from
this topological hypothesis and the simple-arc payment inequality.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

def HasSimpleArcsInConnectedOpens (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U → IsConnected U →
    ∀ x ∈ U, ∀ y ∈ U, x ≠ y →
      ∃ γ : Path x y, Function.Injective γ ∧ Set.range γ ⊆ U

/-- The null-image criterion with the actual simple-arc payment premise.
The input only supplies arcs; no oscillation or null-image conclusion
is included in it. -/
theorem null_image_of_simple_arc_payment
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [μ.OuterRegular] (harcs : HasSimpleArcsInConnectedOpens X)
    {F V : Set X} (hV : IsOpen V) (hF : μ (F ∩ V) = 0)
    (v : X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hpay : ∀ x ∈ F ∩ V, ∀ y ∈ F ∩ V,
      ∀ γ : Path x y, Function.Injective γ → range γ ⊆ V →
        |v x - v y| ≤ A * μ.real (range γ)) :
    volume (v '' (F ∩ V)) = 0 := by
  apply null_image_inter_open_of_connected_open_oscillation hV hF v hA
  intro U hUV hU hconn x hx y hy
  by_cases hxy : x = y
  · subst y
    simpa only [sub_self, abs_zero] using
      mul_nonneg hA (measureReal_nonneg (μ := μ) (s := U))
  obtain ⟨γ, hγ, hγU⟩ := harcs U hU hconn x hx.2 y hy.2 hxy
  exact (hpay x ⟨hx.1, hUV hx.2⟩ y ⟨hy.1, hUV hy.2⟩ γ hγ
    (hγU.trans hUV)).trans
      (mul_le_mul_of_nonneg_left (measureReal_mono hγU) hA)

end CircleDomainRigidity

end OAI
