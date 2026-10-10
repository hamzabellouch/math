import OAI.NumberTheory.DukePrimeDegree.Dynamics.HaarFromHomogeneousComponent
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-!
# Integrating homogeneous components

Invariance of almost every component in a measurable decomposition passes
to the ambient measure, and ambient genericity passes back to almost
every component. The orbit obstruction then identifies Haar measure
under the stated homogeneous-decomposition hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma map_bind_eq_of_ae_component_invariant {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (τ : Measure Z) (κ : Z → Measure X) (hκ : Measurable κ)
    (T : X → X) (hT : Measurable T)
    (hinv : ∀ᵐ z ∂τ, (κ z).map T = κ z) :
    (τ.bind κ).map T = τ.bind κ := by
  ext s hs
  rw [Measure.map_apply hT hs, Measure.bind_apply (hT hs) hκ.aemeasurable,
    Measure.bind_apply hs hκ.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hinv] with z hz
  simpa only [Measure.map_apply hT hs] using congrArg (fun ν : Measure X => ν s) hz

/-- A homogeneous decomposition with a common A-normalized orbit group
is enough for prime-degree Haar rigidity. All remaining hypotheses are
concrete orbit and root data; no entropy rigidity implication is assumed. -/
theorem isHaar_of_prime_homogeneous_decomposition {Z : Type*} [MeasurableSpace Z]
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hnontrivial : ∃ i j, i ≠ j ∧ r i j)
    (L : Subgroup (G (d + 1))) (hclosed : IsClosed (L : Set (G (d + 1))))
    (hnormal : ∀ (ell : Fin (d + 1) → ℝ) (hsum : ∑ a, ell a = 0) (t : ℝ),
      ∀ h ∈ L, diagonalOneParameter ell hsum t * h * diagonalOneParameter ell hsum (-t) ∈ L)
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Z → Measure (X (d + 1)))
    (hκ : Measurable κ) (hdecomp : τ.bind κ = μ)
    (hprob : ∀ᵐ z ∂τ, IsProbabilityMeasure (κ z))
    (hhomogeneous : ∀ᵐ z ∂τ,
      (∃ g : G (d + 1), ∀ᵐ x ∂κ z, x ∈ range (latticeOrbitPoint g L)) ∧
      ∀ h : L, (κ z).map (fun x => rightAction x h.val) = κ z) :
    IsHaarProbability μ := by
  have hLμ : L ≤ invariantRightSubgroup μ := by
    intro h hh
    change μ.map (fun x => rightAction x h) = μ
    rw [← hdecomp]
    exact map_bind_eq_of_ae_component_invariant τ κ hκ _
      (continuous_rightAction h).measurable (hhomogeneous.mono (fun _ hz => hz.2 ⟨h, hh⟩))
  have hgeneric : ∀ᵐ z ∂τ, ∀ᵐ x ∂κ z,
      ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0 := by
    apply Measure.ae_ae_of_ae_bind hκ.aemeasurable
    rw [hdecomp]
    exact ae_no_coordinate_zero d μ hA
  obtain ⟨z, hzprob, hzhom, hzgen⟩ := (hprob.and (hhomogeneous.and hgeneric)).exists
  let : IsProbabilityMeasure (κ z) := hzprob
  obtain ⟨g, hgorbit⟩ := hzhom.1
  exact isHaar_of_prime_homogeneous_component d hprime μ hA r hr hnontrivial
    g L hclosed hnormal hLμ hroot (κ z) (IsProbabilityMeasure.ne_zero _) hgorbit hzhom.2 hzgen

end DukePrimeDegree

end

end OAI
