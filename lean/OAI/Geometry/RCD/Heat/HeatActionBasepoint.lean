import OAI.Geometry.RCD.Heat.CenteredHeatActionRealization
import OAI.Geometry.RCD.Heat.CanonicalKernelIdentification

namespace OAI

/-! # One action-gradient constant for all physical centers

The reference point used to construct the canonical kernel does not change
the kernel, the compact heat factors, or their normalized action limits.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_basepoint (p q : X) (t : ℝ) (x y : X) :
    hX.canonicalHeatKernel hn p t x y=hX.canonicalHeatKernel hn q t x y := by
  by_cases ht : 0 < t
  · exact hX.canonicalHeatKernel_eq_of_isContinuousHeatKernel hn p
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn q) t ht x y
  · simp only [canonicalHeatKernel,dite_eq_right ht]

theorem compactHeatFactor_basepoint (p q : X)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (F : C(S,ℝ)) (t : ℝ) (ht : 0 < t) (x : X) :
    hX.compactHeatFactor hn p ν F t ht x=hX.compactHeatFactor hn q ν F t ht x := by
  change (∫ y:S, hX.canonicalHeatKernel hn p t x y*F y ∂ν)=
    ∫ y:S, hX.canonicalHeatKernel hn q t x y*F y ∂ν
  simp only [hX.canonicalHeatKernel_basepoint hn p q]

theorem fixedGaugeScaledPotential_basepoint (p q : X)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (F : C(S,ℝ)) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (z : X) (t : ℝ) (x : X) :
    hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x=
      hX.fixedGaugeScaledPotential hn q ν F ε hε δ hδ z t x := by
  simp only [fixedGaugeScaledPotential,scaledCompactHeatPotential,
    hX.compactHeatFactor_basepoint hn p q]

theorem CompactHeatConverges.basepoint {p q : X}
    {S : Set X} [CompactSpace S] {ν : Measure S} [IsProbabilityMeasure ν]
    {F : ℕ → C(S,ℝ)} {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
    {z : X} {ι : ℕ → ℕ} {H : ℝ → X → ℝ}
    (h : hX.CompactHeatConverges hn p ν F ε hε z ι H) :
    hX.CompactHeatConverges hn q ν F ε hε z ι H := by
  intro r hr δ hδ t ht
  simpa only [hX.fixedGaugeScaledPotential_basepoint hn q p] using h r hr δ hδ t ht

theorem uniform_centered_heat_action_realization (p₀ : X) :
    ∃ D : ℝ, 0 < D ∧ ∀ p : X,
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (ρ : X → ℝ) (_hρ : Measurable ρ) (_hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0},
      (∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) →
      ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
      ∀ (F : ℕ → C(S,ℝ)), (∀ k y, 0 < F k y) →
      ∀ (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k), (∀ k, ε k ≤ 1) →
      Tendsto ε atTop (𝓝 0) →
      ∀ (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ), Tendsto ι atTop atTop →
      hX.CompactHeatConverges hn p ν F ε hε z ι H →
      ∀ {R r δ : ℝ}, 0 ≤ R → (∀ y:S, dist z y ≤ R) → 0 < r → 0 < δ →
      ∀ t∈Ioo δ 1,
      let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| * (16*D*(R+32*r)^2/δ^2)),Real.sqrt_nonneg _⟩
      ∃ (v : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ),
        LipschitzWith (3*L) V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V) ∧
        (∀ x, |V x| ≤ 2*r*(L:ℝ)) ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic v
          =ᵐ[(hausdorff n X).restrict (closedBall z r)] fun x => H t x-H t z) := by
  obtain ⟨D,hD,hreal⟩ := hX.centered_heat_action_realization hn p₀
  refine ⟨D,hD,?_⟩
  intro p S _ ν _ ρ hρ hρ0 B hB hν F hF ε hε hε1 hε0 z ι H hι hconv R r δ hR hdist hr hδ t ht
  exact hreal ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z ι H hι
    (hconv.basepoint hX hn) hR hdist hr hδ t ht

def centeredActionBound (p₀ : X) : ℝ :=
  Classical.choose (hX.uniform_centered_heat_action_realization hn p₀)

theorem centeredActionBound_pos (p₀ : X) : 0 < hX.centeredActionBound hn p₀ :=
  (Classical.choose_spec (hX.uniform_centered_heat_action_realization hn p₀)).1

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
