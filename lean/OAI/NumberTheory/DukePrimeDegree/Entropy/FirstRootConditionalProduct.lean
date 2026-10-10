import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationFirstRootSlice
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootFactorConditionalProduct

namespace OAI

/-!
# Product conditionals in the first Gaussian root factor

Pulling an actual root-box coordinate measure back through the open
remaining-root chart supplies the coordinate transport required by the
neutral-holonomy product argument. Thus no product hypothesis is imposed
on the ambient measure.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

abbrev rootFactorCoordinateMap {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) : (T × B) × ℝ → RootSlice a b k × ℝ :=
  fun z => (e z.1, z.2)

def rootFactorPullback {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) (e : T × B → RootSlice a b k) :
    Measure (T × (B × ℝ)) :=
  ((A.coordinateMeasure μ).comap (rootFactorCoordinateMap e)).map MeasurableEquiv.prodAssoc

lemma rootFactorCoordinateMap_embedding {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e) :
    MeasurableEmbedding (rootFactorCoordinateMap e) :=
  he.prodMap MeasurableEmbedding.id

lemma rootFactorPullback_finite {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e) :
    IsFiniteMeasure (rootFactorPullback hab A μ e) := by
  have hf := rootFactorCoordinateMap_embedding e he
  have : IsFiniteMeasure ((A.coordinateMeasure μ).comap (rootFactorCoordinateMap e)) := ⟨by
    rw [hf.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top _ univ)⟩
  unfold rootFactorPullback
  infer_instance

lemma rootFactorPullback_map {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (hcover : A.transverse ⊆ Set.range e) :
    A.coordinateMeasure μ =
      ((rootFactorPullback hab A μ e).map MeasurableEquiv.prodAssoc.symm).map
        (rootFactorCoordinateMap e) := by
  have hf := rootFactorCoordinateMap_embedding e he
  have hs : ∀ᵐ z ∂A.coordinateMeasure μ, z ∈ Set.range (rootFactorCoordinateMap e) := by
    filter_upwards [A.coordinateMeasure_ae_domain μ] with z hz
    obtain ⟨w, hw⟩ := hcover hz.1
    exact ⟨(w, z.2), Prod.ext hw rfl⟩
  unfold rootFactorPullback
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  have hi : (MeasurableEquiv.prodAssoc.symm ∘ MeasurableEquiv.prodAssoc :
      ((T × B) × ℝ) → ((T × B) × ℝ)) = id := by
    funext z
    exact MeasurableEquiv.prodAssoc.symm_apply_apply z
  rw [hi, Measure.map_id, hf.map_comap]
  exact (Measure.restrict_eq_self_of_ae_mem hs).symm

variable [StandardBorelSpace B] [Nonempty B]

theorem firstRootChart_conditional_product
    (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (c : EliminationChain ({(a, b)} : Finset (Fin (d + 1) × Fin (d + 1))) {a})
    (hfinal : c.finalEntries = allPositiveRoots (d + 1))
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ allPositiveRoots (d + 1), p ≠ (a, b) → ell p.1 < ell p.2)
    (A : RootBox hab a) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hcover : A.transverse ⊆ Set.range (firstRootSliceParam hab c))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    let σ := rootFactorPullback hab A μ (firstRootSliceParam hab c)
    haveI := rootFactorPullback_finite hab A μ (firstRootSliceParam hab c)
      (firstRootSliceParam_isOpenEmbedding hab c).measurableEmbedding
    ∀ᵐ s ∂σ.fst, σ.condKernel s = (σ.condKernel s).fst.prod (σ.condKernel s).snd := by
  intro σ
  let := rootFactorPullback_finite hab A μ (firstRootSliceParam hab c)
    (firstRootSliceParam_isOpenEmbedding hab c).measurableEmbedding
  have hp : (a, b) ∈ allPositiveRoots (d + 1) := by
    rw [←hfinal]
    exact c.entries_subset_final (Finset.mem_singleton_self _)
  have he := (firstRootSliceParam_isOpenEmbedding hab c).measurableEmbedding
  have hcoord := rootFactorPullback_map hab A μ (firstRootSliceParam hab c) he hcover
  let factor (w : c.Time) : positiveRootGeneratedGroup ((allPositiveRoots (d + 1)).erase (a, b)) :=
    ⟨c.word w, firstRootWord_mem_remaining c hfinal w⟩
  have h := rootFactorChart_real_conditionals_constant d (allPositiveRoots (d + 1))
    (fun p hp => (Finset.mem_filter.mp hp).2) (allPositiveRoots_closed _) hab hp
    ell hell hneut hdecay A R hAR μ hA σ (firstRootSliceParam hab c) he hcoord
    (fun s => Quotient.mk _ s.val) factor (firstRootSliceParam_orbit hab c)
  filter_upwards [h] with s hs
  obtain ⟨ν, hν, hconst⟩ := hs
  let := hν
  have heq := eq_prod_of_constant_real_conditionals (σ.condKernel s) ν hconst
  have hm := congrArg (fun ρ : Measure (c.Time × ℝ) => ρ.snd) heq
  rw [Measure.snd_prod] at hm
  simpa only [hm] using heq

end DukePrimeDegree

end

end OAI
