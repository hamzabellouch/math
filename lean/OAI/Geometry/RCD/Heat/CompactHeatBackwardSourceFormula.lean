import OAI.Geometry.RCD.Heat.GlobalScaledLogSource
import OAI.Geometry.RCD.Heat.CompactHeatBackwardSource
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # The uniform backward source bound on the actual heat representative -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem backward_source_formula_lower (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ : X → ℝ) (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1), (t:ℝ) ≤ 1/2 →
      let m := hausdorff n X
      let Q := hX.quadratic
      let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
      let s := ε k/4*(1-t)
      let hs : 0 < s := mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)
      ∀ (g : Lp ℝ 2 m) (C : ℝ≥0), (∀ᵐ x ∂m, |g x| ≤ C) →
        (∀ x, hX.compactHeatFactor hn p ν (D.right k) s hs x = kernelHeat m Q hk s g x) →
        ∀ᵐ x ∂m, -A*(1+(dist z x)^2) ≤ (ε k/2)*
          (((-heatGenerator m Q s hs g : Lp ℝ 2 m) : X → ℝ) x/kernelHeat m Q hk s g x-
            localGamma m Q (heatSobolev m Q s hs g) (heatSobolev m Q s hs g) x/
              (kernelHeat m Q hk s g x)^2) := by
  obtain ⟨A,hA,hdata⟩ := D.backward_source_lower hK hε1 ρ hm hp hB hν z hR hT
  refine ⟨A,hA,?_⟩
  intro k t ht m Q hk s hs g C hg hge
  let U := kernelHeat m Q hk s g
  have hUc : Continuous U := ((hX.kernelHeat_bounded_regularity hn p hk g C hg s hs).1).continuous
  have hUb : ∀ x, |U x| ≤ C := (hX.kernelHeat_bounded_regularity hn p hk g C hg s hs).2
  have hUp : ∀ x, 0 < U x := by
    intro x
    change 0 < kernelHeat m Q hk s g x
    rw [← hge x]
    exact hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) s hs x
  have hUr : SobolevSpace.toLp m Q (heatSobolev m Q s hs g) =ᵐ[m] U := by
    simpa only [heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk hs g).symm
  exact global_scaled_log_source_lower m Q z (heatSobolev m Q s hs g)
    (-heatGenerator m Q s hs g) (heatSobolev_weak_laplacian m Q s hs g)
    U hUc hUr hUp C _ hUb
    (SobolevSpace.minimalSlope_le_lipschitz m Q _
      (hX.kernelHeat_bounded_regularity hn p hk g C hg s hs).1 hUr)
    (ε k/2) (fun x => -A*(1+(dist z x)^2)) (fun Ω hΩ => by
      obtain ⟨w,q,hq,hw,hbound⟩ := hdata k t ht Ω hΩ
      refine ⟨w,q,hq,?_,hbound⟩
      filter_upwards [hw] with x hx
      exact hx.trans (congrArg (fun a : ℝ => (ε k/2)*Real.log a) (hge x)))

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
