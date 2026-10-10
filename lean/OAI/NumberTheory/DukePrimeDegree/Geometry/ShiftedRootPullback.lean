import OAI.NumberTheory.DukePrimeDegree.Entropy.ShiftedRootConditionalProduct

namespace OAI

/-! # Actual coordinate measures for root charts with varying time origins -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

def realFiberShift {S : Type*} [MeasurableSpace S] (τ : S → ℝ) (hτ : Measurable τ) :
    (S × ℝ) ≃ᵐ (S × ℝ) where
  toFun z := (z.1,z.2 + τ z.1)
  invFun z := (z.1,z.2 - τ z.1)
  left_inv z := by dsimp; congr 1; ring
  right_inv z := by dsimp; congr 1; ring
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add (hτ.comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub (hτ.comp measurable_fst))

def shiftedRootFactorCoordinateMap {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) :
    (T × B) × ℝ → RootSlice a b k × ℝ := fun z => (e z.1,z.2 + τ z.1)

lemma shiftedRootFactorCoordinateMap_embedding {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ) :
    MeasurableEmbedding (shiftedRootFactorCoordinateMap e τ) :=
  (he.prodMap MeasurableEmbedding.id).comp (realFiberShift τ hτ).measurableEmbedding

def shiftedRootFactorPullback {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) : Measure (T × (B × ℝ)) :=
  ((A.coordinateMeasure μ).comap (shiftedRootFactorCoordinateMap e τ)).map MeasurableEquiv.prodAssoc

lemma shiftedRootFactorPullback_finite {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ) :
    IsFiniteMeasure (shiftedRootFactorPullback hab A μ e τ) := by
  have hf := shiftedRootFactorCoordinateMap_embedding e he τ hτ
  have : IsFiniteMeasure ((A.coordinateMeasure μ).comap (shiftedRootFactorCoordinateMap e τ)) := ⟨by
    rw [hf.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top _ univ)⟩
  unfold shiftedRootFactorPullback
  infer_instance

lemma shiftedRootFactorPullback_map {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcover : A.transverse ⊆ Set.range e) :
    A.coordinateMeasure μ =
      ((shiftedRootFactorPullback hab A μ e τ).map MeasurableEquiv.prodAssoc.symm).map
        (shiftedRootFactorCoordinateMap e τ) := by
  have hf := shiftedRootFactorCoordinateMap_embedding e he τ hτ
  have hs : ∀ᵐ z ∂A.coordinateMeasure μ, z ∈ Set.range (shiftedRootFactorCoordinateMap e τ) := by
    filter_upwards [A.coordinateMeasure_ae_domain μ] with z hz
    obtain ⟨w,hw⟩ := hcover hz.1
    refine ⟨(w,z.2 - τ w),?_⟩
    apply Prod.ext hw
    dsimp [shiftedRootFactorCoordinateMap]
    ring
  unfold shiftedRootFactorPullback
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  have hi : (MeasurableEquiv.prodAssoc.symm ∘ MeasurableEquiv.prodAssoc :
      ((T × B) × ℝ) → ((T × B) × ℝ)) = id := by
    funext z
    exact MeasurableEquiv.prodAssoc.symm_apply_apply z
  rw [hi,Measure.map_id,hf.map_comap]
  exact (Measure.restrict_eq_self_of_ae_mem hs).symm

end DukePrimeDegree

end

end OAI
