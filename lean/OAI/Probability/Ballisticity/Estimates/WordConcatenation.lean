import Mathlib
import OAI.Probability.Ballisticity.Geometry.FiniteWordGeometry
import OAI.Probability.Ballisticity.Estimates.SuccessfulWords

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev CoordinateWord {d : ℕ} (e : Direction d) (x : Lattice d) (H : ℕ) :=
  HitWord x (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H)

def ValidWordSplit {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : List (Direction d) × List (Direction d)) : Prop :=
  wordPath x p.1 ∈ HitAt (Strip (realPosition (step e)) x h)
    (Upper (realPosition (step e)) x h) p.1.length ∧
  wordPath (wordPath x p.1 p.1.length) p.2 ∈ HitAt
    (Strip (realPosition (step e)) (wordPath x p.1 p.1.length) m)
    (Upper (realPosition (step e)) (wordPath x p.1 p.1.length) m) p.2.length

abbrev CoordinateSplit {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ) :=
  {p : List (Direction d) × List (Direction d) // ValidWordSplit e x h m p}

def coordinateSplitFirst {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : CoordinateSplit e x h m) : CoordinateWord e x h := ⟨p.val.1,p.property.1⟩

def coordinateSplitSecond {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : CoordinateSplit e x h m) : CoordinateWord e (wordPath x p.val.1 p.val.1.length) m :=
  ⟨p.val.2,p.property.2⟩

def coordinateWordConcat {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ)
    (p : CoordinateSplit e x h m) : CoordinateWord e x (h+m) :=
  ⟨p.val.1++p.val.2,wordPath_hit_append e x h m (coordinateSplitFirst e x h m p)
    (coordinateSplitSecond e x h m p)⟩

lemma coordinateWordConcat_injective {d : ℕ} (e : Direction d) (x : Lattice d) (h m : ℕ) :
    Function.Injective (coordinateWordConcat e x h m) := by
  intro u v huv
  have he : u.val.1++u.val.2 = v.val.1++v.val.2 := Subtype.ext_iff.mp huv
  have hlen (p : CoordinateSplit e x h m) :
      wordFirstHitTime e x h (p.val.1++p.val.2) = p.val.1.length := by
    have hf := wordFirstHitTime_append_prefix e x h h le_rfl (coordinateSplitFirst e x h m p) p.val.2
    have hg := wordFirstHitTime_endpoint e x h (coordinateSplitFirst e x h m p)
    exact hf.trans hg
  have hl : u.val.1.length = v.val.1.length := by rw [← hlen u,he,hlen v]
  have hp := List.append_inj he hl
  exact Subtype.ext (Prod.ext hp.1 hp.2)

namespace TupleKernel

lemma atomic_injection_sum_le {A B : Type*} [MeasurableSpace B] [Countable A] [Countable B]
    (f : A → B) (hf : Function.Injective f) (w : B → ℝ≥0∞) :
    (Measure.sum (fun a => w (f a) • Measure.dirac (f a))) ≤
      Measure.sum (fun b => w b • Measure.dirac b) := by
  intro U
  simp only [Measure.sum_apply_of_countable,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf (fun b => w b * Measure.dirac b U)

lemma countable_map_apply {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (f : A → B) (b : B) :
    μ.map f {b} = ∑' a, if f a = b then μ {a} else 0 := by
  rw [← Measure.sum_smul_dirac μ,Measure.map_sum (measurable_of_countable _).aemeasurable,
    Measure.sum_apply_of_countable]
  congr 1
  funext a
  rw [Measure.map_smul _ (measurable_of_countable f).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _),Measure.smul_apply]
  by_cases ha : f a = b <;> simp [ha]

lemma countable_restricted_map_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) (ν : Measure B) (S : Set A) (f : A → B)
    (hf : Set.InjOn f S) (hzero : ∀ a ∉ S, μ {a} = 0)
    (hatom : ∀ a ∈ S, μ {a} ≤ ν {f a}) : μ.map f ≤ ν := by
  apply measure_le_of_singletons
  intro b
  rw [countable_map_apply]
  by_cases hex : ∃ a ∈ S, f a = b
  · obtain ⟨a,ha,hab⟩ := hex
    rw [tsum_eq_single a]
    · simpa [hab] using hatom a ha
    · intro c hca
      by_cases hc : c ∈ S
      · have hne : f c ≠ b := fun he => hca (hf hc ha (he.trans hab.symm))
        simp only [ite_eq_right hne]
      · simp only [hzero c hc,ite_self]
  · have hz : ∀ a, (if f a = b then μ {a} else 0) = 0 := by
      intro a
      by_cases he : f a = b
      · rw [ite_eq_left he]
        exact hzero a (fun ha => hex ⟨a,ha,he⟩)
      · exact ite_eq_right he
    simp only [hz,tsum_zero,zero_le]

end TupleKernel

noncomputable def rawWordPairLaw {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) : Measure (List (Direction d) × List (Direction d)) :=
  (rawWordLaw (realPosition (step e)) h ω x).bind (fun u =>
    (rawWordLaw (realPosition (step e)) m ω (wordPath x u u.length)).map (fun v => (u,v)))

lemma rawWordPairLaw_singleton {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) (u v : List (Direction d)) :
    rawWordPairLaw e h m ω x {(u,v)} =
      rawWordLaw (realPosition (step e)) h ω x {u} *
      rawWordLaw (realPosition (step e)) m ω (wordPath x u u.length) {v} := by
  rw [rawWordPairLaw,Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable,
    lintegral_countable']
  have he (a : List (Direction d)) :
      ((rawWordLaw (realPosition (step e)) m ω (wordPath x a a.length)).map (fun v => (a,v))) {(u,v)} =
      if a=u then rawWordLaw (realPosition (step e)) m ω (wordPath x a a.length) {v} else 0 := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    by_cases ha : a=u
    · subst a
      rw [ite_eq_left rfl]
      congr 1
      ext b
      simp
    · rw [ite_eq_right ha]
      have hset : (fun b => (a,b)) ⁻¹' {(u,v)} = (∅ : Set (List (Direction d))) := by
        ext b
        simp [ha]
      rw [hset,measure_empty]
  simp_rw [he]
  rw [tsum_eq_single u]
  · simp [mul_comm]
  · intro a ha
    simp [ha]

lemma rawWordPairLaw_invalid {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) (p : List (Direction d) × List (Direction d))
    (hp : ¬ ValidWordSplit e x h m p) : rawWordPairLaw e h m ω x {p} = 0 := by
  rw [← Prod.eta p,rawWordPairLaw_singleton]
  simp only [rawWordLaw_singleton]
  unfold ValidWordSplit at hp
  by_cases h1 : wordPath x p.1 ∈ HitAt (Strip (realPosition (step e)) x h)
    (Upper (realPosition (step e)) x h) p.1.length
  · have h2 : ¬ wordPath (wordPath x p.1 p.1.length) p.2 ∈ HitAt
      (Strip (realPosition (step e)) (wordPath x p.1 p.1.length) m)
      (Upper (realPosition (step e)) (wordPath x p.1 p.1.length) m) p.2.length := fun h2 => hp ⟨h1,h2⟩
    simp only [ite_eq_left h1,ite_eq_right h2,mul_zero]
  · simp only [ite_eq_right h1,zero_mul]

lemma rawWordPairLaw_valid {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) (p : CoordinateSplit e x h m) :
    rawWordPairLaw e h m ω x {p.val} =
      rawWordLaw (realPosition (step e)) (h+m) ω x {p.val.1++p.val.2} := by
  rw [← Prod.eta p.val,rawWordPairLaw_singleton]
  simp only [rawWordLaw_singleton,ite_eq_left p.property.1,ite_eq_left p.property.2]
  have hc := (coordinateWordConcat e x h m p).property
  change wordPath x (p.val.1++p.val.2) ∈ HitAt (Strip (realPosition (step e)) x (h+m : ℕ))
    (Upper (realPosition (step e)) x (h+m : ℕ)) (p.val.1++p.val.2).length at hc
  rw [ite_eq_left hc,wordWeight_append,ENNReal.ofReal_mul (wordWeight_nonneg ω x p.val.1)]

lemma rawWordLaw_comp_le {d : ℕ} (e : Direction d) (h m : ℕ)
    (ω : Environment d) (x : Lattice d) :
    (rawWordPairLaw e h m ω x).map (fun p => p.1++p.2) ≤
      rawWordLaw (realPosition (step e)) (h+m) ω x := by
  apply TupleKernel.countable_restricted_map_le _ _ {p | ValidWordSplit e x h m p}
  · intro u hu v hv he
    have he' : coordinateWordConcat e x h m ⟨u,hu⟩ = coordinateWordConcat e x h m ⟨v,hv⟩ :=
      Subtype.ext he
    exact congrArg Subtype.val (coordinateWordConcat_injective e x h m he')
  · exact fun p hp => rawWordPairLaw_invalid e h m ω x p hp
  · intro p hp
    exact (rawWordPairLaw_valid e h m ω x ⟨p,hp⟩).le

end DirectionalTransience

end

end OAI
