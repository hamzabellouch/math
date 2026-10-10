import OAI.MeasureTheory.Falconer.Radial.MeasurableTubeCover

namespace OAI

/-! # A Borel envelope for geometric bad directions

The finite anchor net and the envelope depend only on the point law and the
geometric test, before a direction measure is selected.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def boundedTubeUnion (D R : ℝ) (J : Finset (Space d))
    (w : Sphere d) : Set (Space d) :=
  {x | ‖x‖ ≤ D ∧ ∃ a ∈ J, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ R}

theorem boundedTubeUnion_joint_measurable (D R : ℝ) (J : Finset (Space d)) :
    MeasurableSet {p : Sphere d × Space d | p.2 ∈ boundedTubeUnion D R J p.1} := by
  have hU : MeasurableSet (⋃ a ∈ J, {p : Sphere d × Space d |
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R}) := by
    apply J.measurableSet_biUnion
    intro a _
    unfold perpendicularPart
    exact measurableSet_le (by fun_prop) measurable_const
  have he : {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} =
      ⋃ a ∈ J, {p : Sphere d × Space d | ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    ext p
    simp only [mem_iUnion,mem_ofPred_eq,exists_prop]
  have hb : MeasurableSet {p : Sphere d × Space d | ‖p.2‖ ≤ D} :=
    measurableSet_le (by fun_prop) measurable_const
  have hU' : MeasurableSet {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    rw [he]
    exact hU
  change MeasurableSet ({p : Sphere d × Space d | ‖p.2‖ ≤ D} ∩ _)
  exact hb.inter hU'

theorem boundedTubeUnion_mass_measurable (μ : Measure (Space d)) [SFinite μ]
    (D R : ℝ) (J : Finset (Space d)) :
    Measurable (fun w : Sphere d => μ (boundedTubeUnion D R J w)) :=
  measurable_measure_prodMk_left (boundedTubeUnion_joint_measurable D R J)

noncomputable def finiteBadDirections (μ : Measure (Space d))
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) : Set (Sphere d) :=
  {w | ∃ J ∈ G.powerset, J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}

theorem finiteBadDirections_measurable (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    MeasurableSet (finiteBadDirections μ G N D R a) := by
  classical
  have hU : MeasurableSet (⋃ J ∈ G.powerset,
      {w : Sphere d | J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}) := by
    apply G.powerset.measurableSet_biUnion
    intro J _
    exact (MeasurableSet.const _).inter
      (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R J))
  convert hU using 1
  ext w
  simp only [finiteBadDirections,mem_iUnion,mem_ofPred_eq,exists_prop]

theorem original_bad_direction_mem_envelope (μ : Measure (Space d)) [SFinite μ]
    {D R δ : ℝ} (G : Finset (Space d)) (N : ℕ) (a : ℝ≥0∞)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hnet : ∀ x : Space d, ‖x‖ ≤ D → ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (w : Sphere d) (S : Finset (Space d)) (hS : S.card ≤ N)
    (hmass : a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R}) :
    w ∈ finiteBadDirections μ G N D (2*R+δ) a := by
  classical
  let E := boundedTubeUnion D R S w
  obtain ⟨J,hJG,hJS,hcover⟩ := rounded_tube_cover w E S G
    (fun x hx => hnet x hx.1) (fun _ hx => hx.2)
  refine ⟨J,Finset.mem_powerset.mpr hJG,hJS.trans hS,?_⟩
  have hrestrict : μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R} ≤ μ E := by
    apply measure_mono_ae
    filter_upwards [hμ] with x hx hm
    exact ⟨hx,hm⟩
  apply (hmass.trans hrestrict).trans
  apply measure_mono
  intro x hx
  exact ⟨hx.1,hcover x hx⟩

end Falconer

end OAI
