import OAI.MeasureTheory.Falconer.Radial.TwoSlabMass

namespace OAI

/-! # A finite family of plates: exceptional intersections and clustering -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ}

noncomputable def slabPairException (S : Finset (Space d × ℝ)) (r τ : ℝ) : Set (Space d) :=
  ⋃ p ∈ S, ⋃ q ∈ S, if τ ≤ normalDistance p.1 q.1 then
    {x | |inner ℝ p.1 x-p.2| ≤ r ∧ |inner ℝ q.1 x-q.2| ≤ r} else ∅

theorem measurableSet_slabPairException (S : Finset (Space d × ℝ)) (r τ : ℝ) :
    MeasurableSet (slabPairException S r τ) := by
  classical
  apply Finset.measurableSet_biUnion S
  intro p _
  apply Finset.measurableSet_biUnion S
  intro q _
  split_ifs
  · exact (measurableSet_le
      (by fun_prop : Measurable (fun x : Space d => |inner ℝ p.1 x-p.2|))
      measurable_const).inter (measurableSet_le
      (by fun_prop : Measurable (fun x : Space d => |inner ℝ q.1 x-q.2|)) measurable_const)
  · exact MeasurableSet.empty

theorem slabPairException_mass (μ : Measure (Space d))
    (S : Finset (Space d × ℝ)) {M s C r τ : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C) (hunit : ∀ p ∈ S, ‖p.1‖ = 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 < r) (hsmall : 10*r/τ ≤ 1) :
    μ (slabPairException S r τ) ≤ (S.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*r/τ)^(s-((d-2:ℕ):ℝ))) := by
  classical
  let B := ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
    (10*r/τ)^(s-((d-2:ℕ):ℝ)))
  change μ (⋃ p ∈ S, ⋃ q ∈ S, if τ ≤ normalDistance p.1 q.1 then
    {x | |inner ℝ p.1 x-p.2| ≤ r ∧ |inner ℝ q.1 x-q.2| ≤ r} else ∅) ≤ _
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ S, ∑ _q ∈ S, B := by
      apply Finset.sum_le_sum
      intro p hp
      apply (measure_biUnion_finset_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hsep
      · exact two_slab_frostman_bound μ p.1 q.1 p.2 q.2 hM hC hbounded hfrost
          (hunit p hp) (hunit q hq) hτ hτ1 hr hsep hsmall
      · simp only [measure_empty]; exact bot_le
    _ = _ := by simp [nsmul_eq_mul,pow_two,mul_assoc,B]

theorem cluster_outside_slabPairException (S : Finset (Space d × ℝ))
    {x : Space d} {M r τ : ℝ} (hx : ‖x‖ ≤ M)
    (hgood : x ∉ slabPairException S r τ)
    {p : Space d × ℝ} (hp : p ∈ S) (hxp : |inner ℝ p.1 x-p.2| ≤ r) :
    ∀ q ∈ S, |inner ℝ q.1 x-q.2| ≤ r → ∀ y : Space d,
      ‖y‖ ≤ M → |inner ℝ q.1 y-q.2| ≤ r →
      |inner ℝ p.1 y-p.2| ≤ 2*M*τ+3*r := by
  classical
  intro q hq hxq y hy hyq
  have hclose : normalDistance p.1 q.1 < τ := by
    by_contra! hn
    apply hgood
    exact mem_iUnion₂.mpr ⟨p,hp,mem_iUnion₂.mpr ⟨q,hq,by
      rw [ite_eq_left hn]; exact ⟨hxp,hxq⟩⟩⟩
  exact affine_slab_cluster hx hy hclose.le hxp hxq hyq

end Falconer

end OAI
