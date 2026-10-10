import Mathlib
import OAI.Probability.Ballisticity.Stationary.Array

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

local instance : BorelSpace ℕ∞ := ⟨borel_eq_top_of_countable.symm⟩

local instance {d : ℕ} (e : Direction d) :
    MeasurableSpace (OnePoint (HorizontalSpace e)) := borel _

lemma stationary_mark_identDistrib {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ) (i : ℤ) :
    IdentDistrib (fun Y : ActualEpisodeArray e => Y.1 i) (fun Y => Y.1 0) μ μ := by
  have hm (i : ℤ) : Measurable (fun Y : ActualEpisodeArray e => Y.1 i) := by fun_prop
  have hs (i : ℤ) : IdentDistrib (fun Y : ActualEpisodeArray e => Y.1 (i+1))
      (fun Y => Y.1 i) μ μ := by
    refine ⟨(hm (i+1)).aemeasurable,(hm i).aemeasurable,?_⟩
    change Measure.map ((fun Y : ActualEpisodeArray e => Y.1 i) ∘ StationaryCompact.shift) μ = _
    rw [←Measure.map_map (hm i) hstat.measurable,hstat.map_eq]
  induction i using Int.induction_on with
  | zero => exact IdentDistrib.refl (hm 0).aemeasurable
  | succ n ih => exact (hs n).trans ih
  | pred n ih =>
    have ht := (hs (-(n:ℤ)-1)).symm
    have hi : -(n:ℤ)-1+1=-(n:ℤ) := by omega
    rw [hi] at ht
    exact ht.trans ih

lemma stationary_marks_ae_all {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ)
    (p : StationaryCompact.MarkSpace → Prop) (hp : MeasurableSet {m | p m})
    (h0 : ∀ᵐ Y ∂μ, p (Y.1 0)) : ∀ᵐ Y ∂μ, ∀ i, p (Y.1 i) := by
  apply ae_all_iff.mpr
  intro i
  exact (stationary_mark_identDistrib e μ hstat i).symm.ae_snd hp h0

lemma stationary_marks_integral {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ)
    (g : StationaryCompact.MarkSpace → ℝ) (hg : Measurable g)
    (h0 : Integrable (fun Y => g (Y.1 0)) μ) (i : ℤ) :
    Integrable (fun Y => g (Y.1 i)) μ ∧
      (∫ Y, g (Y.1 i) ∂μ)=(∫ Y, g (Y.1 0) ∂μ) := by
  have hi := (stationary_mark_identDistrib e μ hstat i).comp hg
  exact ⟨hi.integrable_iff.mpr h0,hi.integral_eq⟩

lemma stationary_finite_marks_all {d : ℕ} (e : Direction d)
    (μ : Measure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift μ μ)
    (h0 : ∀ᵐ Y ∂μ, 0<(Y.1 0).1 ∧ (Y.1 0).1<⊤ ∧ (Y.1 0).2.1<⊤ ∧ (Y.1 0).2.2<∞) :
    ∀ᵐ Y ∂μ, ∀ i, 0<(Y.1 i).1 ∧ (Y.1 i).1<⊤ ∧ (Y.1 i).2.1<⊤ ∧ (Y.1 i).2.2<∞ := by
  apply stationary_marks_ae_all e μ hstat
    (fun m : StationaryCompact.MarkSpace => 0 < m.1 ∧ m.1 < ⊤ ∧ m.2.1 < ⊤ ∧ m.2.2 < ∞) _ h0
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
        (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const)))

end DirectionalTransience

end

end OAI
