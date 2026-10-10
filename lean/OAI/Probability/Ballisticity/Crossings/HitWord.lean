import Mathlib
import OAI.Probability.Ballisticity.Estimates.SurvivingLane

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev HitWord {d : ℕ} (x : Lattice d) (S T : Set (Lattice d)) :=
  {w : List (Direction d) // wordPath x w ∈ HitAt S T w.length}

lemma hitWord_prefix {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (w : HitWord x S T) {X : Path d} (hX : X ∈ wordCylinder x w.val) :
    X ∈ HitAt S T w.val.length := by
  exact ⟨by simpa only [hX _ le_rfl] using w.property.1,
    fun j hj => by simpa only [hX j hj.le] using w.property.2 j hj⟩

lemma hitWord_cylinders_disjoint {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) :
    Pairwise (fun u v : HitWord x S T => Disjoint (wordCylinder x u.val) (wordCylinder x v.val)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro X hu hv
  by_cases he : u.val.length = v.val.length
  · exact huv (Subtype.ext (word_eq_of_cylinders x u.val v.val X hu hv he))
  · exact Set.disjoint_left.mp (hitAt_pairwise_disjoint hST he)
      (hitWord_prefix x S T u hu) (hitWord_prefix x S T v hv)

lemma hitWord_cover {d : ℕ} (x : Lattice d) (S T : Set (Lattice d))
    (X : Path d) (hx : X 0 = x)
    (hnn : ∀ n, ∃ e : Direction d, X (n+1) = X n + step e) :
    X ∈ Hit S T ↔ ∃ w : HitWord x S T, X ∈ wordCylinder x w.val := by
  constructor
  · intro hX
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hnn n
    rw [hx] at hcy
    have hp : wordPath x w ∈ HitAt S T w.length := by
      rw [hw]
      exact ⟨by simpa only [← hcy n (by omega)] using hn.1,
        fun j hj => by simpa only [← hcy j (by omega)] using hn.2 j hj⟩
    exact ⟨⟨w,hp⟩,hcy⟩
  · rintro ⟨w,hw⟩
    exact Set.mem_iUnion.mpr ⟨w.val.length,hitWord_prefix x S T w hw⟩

def wordTrace {d : ℕ} (x : Lattice d) (w : List (Direction d)) : Set (Lattice d) :=
  {z | ∃ j ≤ w.length, wordPath x w j = z}

lemma wordDepartures_subset_trace {d : ℕ} (x : Lattice d) (w : List (Direction d)) :
    (wordDepartures x w : Set (Lattice d)) ⊆ wordTrace x w := by
  intro z hz
  obtain ⟨j,hj,he⟩ := (wordDepartures_mem_iff x z w).mp hz
  exact ⟨j,hj.le,he.symm⟩

lemma hitWords_contact_iff {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) (u : HitWord x S T) (v : HitWord y S T)
    {P : Path d × Path d} (hu : P.1 ∈ wordCylinder x u.val) (hv : P.2 ∈ wordCylinder y v.val) :
    P ∈ PrefixContact S ↔ ¬ Disjoint (wordTrace x u.val) (wordTrace y v.val) := by
  have h1 := hitWord_prefix x S T u hu
  have h2 := hitWord_prefix y S T v hv
  constructor
  · rintro ⟨n,m,he,hn,hm⟩ hdis
    have hn' : n ≤ u.val.length := by
      by_contra h
      exact Set.disjoint_left.mp hST (hn _ (by omega)) h1.1
    have hm' : m ≤ v.val.length := by
      by_contra h
      exact Set.disjoint_left.mp hST (hm _ (by omega)) h2.1
    exact Set.disjoint_left.mp hdis ⟨n,hn',(hu n hn').symm⟩
      ⟨m,hm',(hv m hm').symm.trans he.symm⟩
  · intro hdis
    obtain ⟨z,hz1,hz2⟩ := Set.not_disjoint_iff.mp hdis
    obtain ⟨n,hn,he⟩ := hz1
    obtain ⟨m,hm,hf⟩ := hz2
    exact ⟨n,m,(hu n hn).trans (he.trans (hf.symm.trans (hv m hm).symm)),
      fun j hj => h1.2 j (hj.trans_le hn),fun j hj => h2.2 j (hj.trans_le hm)⟩

lemma annealedFrom_wordCylinder {d : ℕ} (ν : Measure (Row d)) (x : Lattice d)
    (w : List (Direction d)) :
    annealedFrom ν x (wordCylinder x w) =
      ∫⁻ ω, ENNReal.ofReal (wordWeight ω x w) ∂environmentLaw ν := by
  rw [annealedFrom_apply ν x _ (measurableSet_wordCylinder x w)]
  exact lintegral_congr fun ω => quenched_wordCylinder ω x w

lemma disjoint_word_pair_weight {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) (u v : List (Direction d))
    (hdis : Disjoint (wordDepartures x u : Set (Lattice d)) (wordDepartures y v : Set (Lattice d))) :
    sharedPairLaw ν x y (wordCylinder x u ×ˢ wordCylinder y v) =
      ((annealedFrom ν x).prod (annealedFrom ν y)) (wordCylinder x u ×ˢ wordCylinder y v) := by
  rw [sharedPairLaw_rectangle ν x y _ _ (measurableSet_wordCylinder x u)
    (measurableSet_wordCylinder y v),Measure.prod_prod,annealedFrom_wordCylinder,
    annealedFrom_wordCylinder]
  simp_rw [quenched_wordCylinder]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le _) (rowSigma_le _) (environment_indep_rows ν hdis)
    (measurable_wordWeight_on x u (fun _ hz => hz)).ennreal_ofReal
    (measurable_wordWeight_on y v (fun _ hz => hz)).ennreal_ofReal

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def hitWordsEvent {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T × HitWord y S T)) : Set (Path d × Path d) :=
  ⋃ w ∈ E, wordCylinder x w.1.val ×ˢ wordCylinder y w.2.val

lemma measurableSet_hitWordsEvent {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T × HitWord y S T)) : MeasurableSet (hitWordsEvent x y S T E) := by
  apply MeasurableSet.iUnion
  intro w
  apply MeasurableSet.iUnion
  intro _
  exact (measurableSet_wordCylinder x w.1.val).prod (measurableSet_wordCylinder y w.2.val)

lemma hitWordsEvent_diff_contact {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) (E : Set (HitWord x S T × HitWord y S T)) :
    hitWordsEvent x y S T E \ PrefixContact S =
      hitWordsEvent x y S T {w ∈ E | Disjoint (wordTrace x w.1.val) (wordTrace y w.2.val)} := by
  ext P
  constructor
  · rintro ⟨hP,hc⟩
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hP
    obtain ⟨he,hcy⟩ := Set.mem_iUnion.mp hw
    exact Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨⟨he,not_not.mp
      (fun h => hc ((hitWords_contact_iff x y S T hST w.1 w.2 hcy.1 hcy.2).mpr h))⟩,hcy⟩⟩
  · intro hP
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hP
    obtain ⟨he,hcy⟩ := Set.mem_iUnion.mp hw
    exact ⟨Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨he.1,hcy⟩⟩,
      fun hc => (hitWords_contact_iff x y S T hST w.1 w.2 hcy.1 hcy.2).mp hc he.2⟩

lemma hitWords_pair_cylinders_disjoint {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) : Pairwise (fun u v : HitWord x S T × HitWord y S T =>
      Disjoint (wordCylinder x u.1.val ×ˢ wordCylinder y u.2.val)
        (wordCylinder x v.1.val ×ˢ wordCylinder y v.2.val)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro P hu hv
  by_cases he : u.1 = v.1
  · have he' : u.2 ≠ v.2 := fun h => huv (Prod.ext he h)
    exact Set.disjoint_left.mp (hitWord_cylinders_disjoint y S T hST he') hu.2 hv.2
  · exact Set.disjoint_left.mp (hitWord_cylinders_disjoint x S T hST he) hu.1 hv.1

lemma hitWordsEvent_measure {d : ℕ} (μ : Measure (Path d × Path d))
    (x y : Lattice d) (S T : Set (Lattice d)) (hST : Disjoint S T)
    (E : Set (HitWord x S T × HitWord y S T)) :
    μ (hitWordsEvent x y S T E) = ∑' w : E,
      μ (wordCylinder x w.val.1.val ×ˢ wordCylinder y w.val.2.val) := by
  have he : hitWordsEvent x y S T E = ⋃ w : E,
      wordCylinder x w.val.1.val ×ˢ wordCylinder y w.val.2.val := by
    ext P
    simp only [hitWordsEvent,Set.mem_iUnion,Subtype.exists]
  rw [he]
  apply measure_iUnion
  · intro u v huv
    exact hitWords_pair_cylinders_disjoint x y S T hST (fun he => huv (Subtype.ext he))
  · intro w
    exact (measurableSet_wordCylinder x w.val.1.val).prod (measurableSet_wordCylinder y w.val.2.val)

theorem raw_prefix_off_contact_equal {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) (S T : Set (Lattice d)) (hST : Disjoint S T)
    (E : Set (HitWord x S T × HitWord y S T)) :
    sharedPairLaw ν x y (hitWordsEvent x y S T E \ PrefixContact S) =
      ((annealedFrom ν x).prod (annealedFrom ν y)) (hitWordsEvent x y S T E \ PrefixContact S) := by
  rw [hitWordsEvent_diff_contact x y S T hST E,
    hitWordsEvent_measure _ x y S T hST,hitWordsEvent_measure _ x y S T hST]
  apply tsum_congr
  intro w
  apply disjoint_word_pair_weight
  exact w.property.2.mono (wordDepartures_subset_trace x w.val.1.val)
    (wordDepartures_subset_trace y w.val.2.val)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
