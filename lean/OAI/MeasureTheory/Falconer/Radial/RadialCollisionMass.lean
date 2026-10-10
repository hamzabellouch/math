import OAI.MeasureTheory.Falconer.Estimates.TroublesomePair

namespace OAI

/-! # Measurable radial collision masses and the original-pin Fubini identity -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialCollisionMass (μ : Measure (Space d)) (δ : ℝ)
    (p : Space d × Space d) : ℝ≥0∞ :=
  μ {y | dist (normalize (y-p.2)) (normalize (p.1-p.2)) ≤ δ}

theorem radialCollisionRelation_measurable (δ : ℝ) :
    MeasurableSet {p : (Space d × Space d) × Space d |
      dist (normalize (p.2-p.1.2)) (normalize (p.1.1-p.1.2)) ≤ δ} := by
  exact measurableSet_le
    ((measurable_normalized_vector (measurable_snd.sub measurable_fst.snd)).dist
      (measurable_normalized_vector (measurable_fst.fst.sub measurable_fst.snd)))
    measurable_const

theorem radialCollisionMass_measurable (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) :
    Measurable (radialCollisionMass μ δ) :=
  measurable_measure_prodMk_left (radialCollisionRelation_measurable δ)

theorem radial_collision_original_pin_fubini (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (_hG : MeasurableSet G)
    (z : Space d) (δ : ℝ) :
    (∫⁻ x in {x | (z,x) ∈ G}, radialCollisionMass μ δ (z,x) ∂ν) =
      ∫⁻ y, ν {x | (z,x) ∈ G ∧
        dist (normalize (y-x)) (normalize (z-x)) ≤ δ} ∂μ := by
  let A : Set (Space d × Space d) :=
    {p | dist (normalize (p.2-p.1)) (normalize (z-p.1)) ≤ δ}
  have hA : MeasurableSet A := by
    exact measurableSet_le
      ((measurable_normalized_vector (measurable_snd.sub measurable_fst)).dist
        (measurable_normalized_vector (measurable_const.sub measurable_fst)))
      measurable_const
  calc
    _ = ((ν.restrict {x | (z,x) ∈ G}).prod μ) A := (Measure.prod_apply hA).symm
    _ = ∫⁻ y, (ν.restrict {x | (z,x) ∈ G}) {x | (x,y) ∈ A} ∂μ :=
      Measure.prod_apply_symm hA
    _ = _ := by
      apply lintegral_congr
      intro y
      have hAy : MeasurableSet {x : Space d | (x,y) ∈ A} :=
        hA.preimage (measurable_id.prodMk measurable_const)
      rw [Measure.restrict_apply hAy]
      congr 1
      ext x
      simp only [A,mem_inter_iff,mem_ofPred_eq]
      exact and_comm

end Falconer

end OAI
