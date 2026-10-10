import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace OAI

/-! # A symmetric fully supported law for the boundary random walk

The boundary construction starts with a probability law that assigns positive
mass to every element of the countable group. A geometric enumeration gives
such a law, and averaging with its inverse image makes it symmetric.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkEnumeration (G : Type*) [Group G] [Countable G] : ℕ → G :=
  letI := Encodable.ofCountable G
  fun n => (Encodable.decode (α := G) n).getD 1

omit [MeasurableSpace G] [MeasurableSingletonClass G] in
theorem randomWalkEnumeration_surjective : Function.Surjective (randomWalkEnumeration G) := by
  let := Encodable.ofCountable G
  intro g
  exact ⟨Encodable.encode g, by simp [randomWalkEnumeration, Encodable.encodek]⟩

def randomWalkGeometricParameter : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

def enumeratedRandomWalkLaw (G : Type*) [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] : Measure G :=
  (geometricMeasure randomWalkGeometricParameter).map (randomWalkEnumeration G)

instance enumeratedRandomWalkLaw_probability : IsProbabilityMeasure (enumeratedRandomWalkLaw G) := by
  unfold enumeratedRandomWalkLaw
  infer_instance

theorem enumeratedRandomWalkLaw_singleton_pos (g : G) :
    0 < enumeratedRandomWalkLaw G {g} := by
  obtain ⟨n, hn⟩ := randomWalkEnumeration_surjective (G := G) g
  rw [enumeratedRandomWalkLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton g)]
  have hs : {n} ⊆ randomWalkEnumeration G ⁻¹' {g} := by
    intro m hm
    obtain rfl := Set.mem_singleton_iff.mp hm
    exact hn
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [geometricMeasure_singleton (by norm_num [randomWalkGeometricParameter, Subtype.ext_iff] :
    randomWalkGeometricParameter ≠ 0)]
  apply ENNReal.ofReal_pos.mpr
  exact geometricMeasure_pos
    (by norm_num [randomWalkGeometricParameter, Subtype.ext_iff])
    (by norm_num [randomWalkGeometricParameter, Subtype.ext_iff]) n

def symmetricRandomWalkLaw (G : Type*) [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] : Measure G :=
  (2 : ℝ≥0∞)⁻¹ • enumeratedRandomWalkLaw G +
    (2 : ℝ≥0∞)⁻¹ • (enumeratedRandomWalkLaw G).map Inv.inv

instance symmetricRandomWalkLaw_probability : IsProbabilityMeasure (symmetricRandomWalkLaw G) := by
  have : IsProbabilityMeasure ((enumeratedRandomWalkLaw G).map Inv.inv) := inferInstance
  constructor
  simp only [symmetricRandomWalkLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem symmetricRandomWalkLaw_inv : (symmetricRandomWalkLaw G).map Inv.inv =
    symmetricRandomWalkLaw G := by
  rw [symmetricRandomWalkLaw, Measure.map_add _ _ (measurable_of_countable _)]
  rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hid : (Inv.inv : G → G) ∘ Inv.inv = id := by funext g; exact inv_inv g
  rw [hid, Measure.map_id, add_comm]

theorem symmetricRandomWalkLaw_singleton_pos (g : G) :
    0 < symmetricRandomWalkLaw G {g} := by
  have hp := enumeratedRandomWalkLaw_singleton_pos g
  have hfirst : 0 < (2 : ℝ≥0∞)⁻¹ * enumeratedRandomWalkLaw G {g} :=
    ENNReal.mul_pos (by norm_num) hp.ne'
  exact hfirst.trans_le (le_add_right le_rfl)

theorem symmetricRandomWalkLaw_null_iff (s : Set G) :
    symmetricRandomWalkLaw G s = 0 ↔ s = ∅ := by
  constructor
  · intro hs
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have h := (symmetricRandomWalkLaw_singleton_pos g).trans_le
      (measure_mono (singleton_subset_iff.mpr hg))
    rw [hs] at h
    exact (lt_irrefl 0) h
  · rintro rfl
    exact measure_empty

theorem absolutelyContinuous_symmetricRandomWalkLaw (ν : Measure G) :
    ν ≪ symmetricRandomWalkLaw G := by
  intro s hs
  rw [(symmetricRandomWalkLaw_null_iff s).mp hs, measure_empty]

theorem symmetricRandomWalkLaw_quasi (f : G → G) :
    Measure.QuasiMeasurePreserving f (symmetricRandomWalkLaw G) (symmetricRandomWalkLaw G) :=
  ⟨measurable_of_countable f, absolutelyContinuous_symmetricRandomWalkLaw _⟩

/-- The root law after the first increment. -/
def randomWalkConvolution (G : Type*) [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] : Measure G :=
  ((symmetricRandomWalkLaw G).prod (symmetricRandomWalkLaw G)).map
    (fun p : G × G => p.1 * p.2)

instance randomWalkConvolution_probability : IsProbabilityMeasure (randomWalkConvolution G) := by
  unfold randomWalkConvolution
  infer_instance

theorem randomWalkConvolution_singleton_pos (g : G) :
    0 < randomWalkConvolution G {g} := by
  rw [randomWalkConvolution, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton g)]
  have hs : ({g} : Set G) ×ˢ {1} ⊆ (fun p : G × G => p.1 * p.2) ⁻¹' {g} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [Set.mem_singleton_iff] at ha hb
    simp [ha, hb]
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [Measure.prod_prod]
  exact ENNReal.mul_pos (symmetricRandomWalkLaw_singleton_pos g).ne'
    (symmetricRandomWalkLaw_singleton_pos 1).ne'

theorem randomWalkLaw_absolutelyContinuous_convolution :
    symmetricRandomWalkLaw G ≪ randomWalkConvolution G := by
  intro s hs
  have he : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have h := (randomWalkConvolution_singleton_pos g).trans_le
      (measure_mono (singleton_subset_iff.mpr hg))
    rw [hs] at h
    exact (lt_irrefl 0) h
  rw [he, measure_empty]

theorem randomWalkConvolution_absolutelyContinuous_law :
    randomWalkConvolution G ≪ symmetricRandomWalkLaw G :=
  absolutelyContinuous_symmetricRandomWalkLaw _

end

end KadisonKastler

end OAI
