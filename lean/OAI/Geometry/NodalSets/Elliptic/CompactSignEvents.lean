import Mathlib.Topology.Maps.Proper.Basic
import OAI.Geometry.NodalSets.Charts.BallGeometry
import OAI.Geometry.NodalSets.Waves.GaussianPartialMeasurability

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability MeasureTheory Set
open scoped ContDiff
noncomputable section
variable {Ω X : Type*} [TopologicalSpace Ω] [TopologicalSpace X]

lemma isOpen_compact_positive_event (F : Ω → X → ℝ) (K : Set X)
    (hK : IsCompact K) (hF : Continuous (fun z : Ω × X ↦ F z.1 z.2)) :
    IsOpen {a | ∀ x ∈ K, 0 < F a x} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {z : Ω × K | F z.1 z.2 ≤ 0} :=
    isClosed_le (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      continuous_const
  have hh := isClosedMap_fst_of_compactSpace _ hc
  have he : (Prod.fst '' {z : Ω × K | F z.1 z.2 ≤ 0})ᶜ = {a | ∀ x ∈ K, 0 < F a x} := by
    ext a
    constructor
    · intro ha x hx
      by_contra hn
      exact ha ⟨(a,⟨x,hx⟩),le_of_not_gt hn,rfl⟩
    · intro ha hmem
      obtain ⟨⟨b,x⟩,hh,heq⟩ := hmem
      change b = a at heq
      subst b
      exact (not_le_of_gt (ha x x.property)) hh
  rw [← he]
  exact hh.isOpen_compl

lemma measurable_compact_opposite_signs [MeasurableSpace Ω] [BorelSpace Ω]
    (F : Ω → X → ℝ) (Kpos Kneg : Set X) (hp : IsCompact Kpos) (hn : IsCompact Kneg)
    (hF : Continuous (fun z : Ω × X ↦ F z.1 z.2)) :
    MeasurableSet {a | (∀ x ∈ Kpos, 0 < F a x) ∧ (∀ x ∈ Kneg, F a x < 0)} := by
  have h1 := isOpen_compact_positive_event F Kpos hp hF
  have h2 := isOpen_compact_positive_event (fun a x ↦ -F a x) Kneg hn hF.neg
  simpa only [neg_pos,Set.inter_def,Set.mem_ofPred_eq] using (h1.inter h2).measurableSet

lemma seeded_gaussian_joint_continuous {ι : Type*} [Fintype ι]
    (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) :
    Continuous (fun z : (ι × Fin 2 → ℝ) × Coord ↦ seed z.2+gaussianWaveField V z.1 z.2) :=
  seeded_partial_joint_continuous V seed hV hs []

lemma source_closed_ball_compact (x : Coord) (r : ℝ) :
    IsCompact {y : Coord | sourceEuclideanNorm (y-x) ≤ r} := by
  have he : {y : Coord | sourceEuclideanNorm (y-x) ≤ r} =
      (fun v : Coord ↦ x+v) '' {v : Coord | sourceEuclideanNorm v ≤ r} := by
    ext y
    constructor
    · intro hy
      exact ⟨y-x,hy,add_sub_cancel _ _⟩
    · rintro ⟨v,hv,rfl⟩
      simpa only [add_sub_cancel_left,mem_ofPred_eq] using hv
  rw [he]
  exact (sourceEuclideanBall_compact r).image (continuous_const.add continuous_id)

lemma seeded_gaussian_sign_balls_measurable {ι : Type*} [Fintype ι]
    (V : ι → Coord → ℂ) (seed : Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (x y : Coord) (rpos rneg : ℝ) :
    MeasurableSet {a : ι × Fin 2 → ℝ |
      (∀ v : Coord, sourceEuclideanNorm (v-x) ≤ rpos → 0 < seed v+gaussianWaveField V a v) ∧
      (∀ v : Coord, sourceEuclideanNorm (v-y) ≤ rneg → seed v+gaussianWaveField V a v < 0)} :=
  measurable_compact_opposite_signs _ _ _ (source_closed_ball_compact x rpos)
    (source_closed_ball_compact y rneg) (seeded_gaussian_joint_continuous V seed hV hs)

end
end Yau.Geometry

end OAI
