import OAI.MeasureTheory.Falconer.Estimates.DescriptorMasks
import OAI.MeasureTheory.Falconer.Estimates.MixedMaskBounds
import OAI.MeasureTheory.Falconer.Measures.MaskSupport

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def descriptorAmbientMask (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x z : Space d) : ℝ :=
  ∑ p ∈ cubePaths d (descriptorAnchor b),
    if x ∈ (Q.descendant p).carrier then
      capCutoffAmbient (descriptorMaskRadius N σ b) (descriptorMaskRadius_pos N σ b) S
        (descriptorGoodDirections Q ρ m N σ J (i+1) p b) z
    else 0

theorem descriptorAmbientMask_sphere (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) (w : Sphere d) :
    descriptorAmbientMask Q ρ m N σ J i b S x w = descriptorMask Q ρ m N σ J i b S x w := rfl

theorem descriptorAmbientMask_on_cell (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (p : List (Fin d → Bool)) (hp : p.length = descriptorAnchor b)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (z : Space d) :
    descriptorAmbientMask Q ρ m N σ J i b S x z =
      capCutoffAmbient (descriptorMaskRadius N σ b) (descriptorMaskRadius_pos N σ b) S
        (descriptorGoodDirections Q ρ m N σ J (i+1) p b) z := by
  unfold descriptorAmbientMask
  rw [Finset.sum_eq_single p]
  · simp only [ite_eq_left hx]
  · intro q hq hqp
    have hdis := Q.descendants_disjoint (((mem_cubePaths d _ q).mp hq).trans hp.symm) hqp
    exact ite_eq_right (fun hq => Set.disjoint_left.mp hdis hq hx)
  · exact fun hn => (hn ((mem_cubePaths d _ p).mpr hp)).elim

theorem descriptorAmbientMask_off_parent (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) {x : Space d} (hx : x ∉ Q.carrier) :
    descriptorAmbientMask Q ρ m N σ J i b S x = fun _ => 0 := by
  funext z
  apply Finset.sum_eq_zero
  intro p _
  exact ite_eq_right (fun hp => hx (Q.descendant_subset p hp))

theorem descriptorAmbientMask_contDiff (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) :
    ContDiff ℝ ∞ (descriptorAmbientMask Q ρ m N σ J i b S x) := by
  apply ContDiff.sum
  intro p _
  by_cases hx : x ∈ (Q.descendant p).carrier
  · simp only [ite_eq_left hx]
    exact capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _
  · simp only [ite_eq_right hx]
    exact contDiff_const

theorem descriptorAmbientMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientMask Q ρ m N σ J i b S)) := by
  apply Finset.measurable_sum
  intro p _
  exact ((capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _).continuous.measurable.comp
    measurable_snd).ite ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

theorem descriptorAmbientMask_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (x : Space d) (w : Sphere d),
        ‖iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) w‖ ≤
          C*((descriptorMaskRadius N σ b)⁻¹)^k := by
  obtain ⟨C,hC,hCb⟩ := capCutoffAmbient_ambient_derivatives d k
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep x w
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
      ((mem_cubePaths d _ p).mp hp) hxp)
    rw [he]
    exact hCb _ (descriptorMaskRadius_pos N σ b) S hsep _ w
  · rw [descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx]
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
    exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) k)

theorem descriptorAmbientMask_tsupport_good (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) (w : Sphere d)
    (hw : (w : Space d) ∈ tsupport (descriptorAmbientMask Q ρ m N σ J i b S x)) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro p hp hx
  have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
    ((mem_cubePaths d _ p).mp hp) hx)
  rw [he] at hw
  have hs := capCutoffAmbient_tsupport_subset (descriptorMaskRadius_pos N σ b) S
    (descriptorGoodDirections Q ρ m N σ J (i+1) p b) hw
  obtain ⟨c,hc,hwc⟩ := Set.mem_iUnion₂.mp hs
  exact (Finset.mem_filter.mp hc).2 w
    (by simpa only [Metric.mem_closedBall,Subtype.dist_eq] using hwc)

end Falconer

end OAI
