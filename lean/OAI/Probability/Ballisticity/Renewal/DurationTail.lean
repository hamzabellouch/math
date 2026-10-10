import Mathlib
import OAI.Probability.Ballisticity.Geometry.StripTimeTail
import OAI.Probability.Ballisticity.Estimates.WidthGridTail
import OAI.Probability.Ballisticity.Estimates.RapidDecaySubsequence

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma firstWordEvent_of_length_pos {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hpos : 0 < (firstWord ℓ X).length) : X ∈ FirstWordEvent ℓ (firstWord ℓ X) := by
  apply firstWordEvent_self
  by_contra hh
  simp only [firstWord,dite_eq_right hh,List.length_nil] at hpos
  omega

lemma duration_tail_cover {d : ℕ} (e : Direction d) (H T : ℕ) (hH : 0 < H)
    (X : Path d) (hNN : ∀ n, ∃ f, X (n+1)=X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e)))
    (hτ : T < (firstWord (realPosition (step e)) X).length) :
    X ∈ NoTruePastHeight e H ∪ StripUntil e H T := by
  have hw := firstWordEvent_of_length_pos (realPosition (step e)) X (by omega)
  have h0 : X 0=0 := by simpa using hw.2.1 0 (Nat.zero_le _)
  obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e X h0 hNN ht hH
  by_cases hnT : n ≤ T
  · exact Or.inl ⟨h0,n,hn,fun t ht htn => hw.2.2.2.2 t ht (by omega)⟩
  · apply Or.inr
    refine ⟨h0,fun j hj => ⟨?_,hn.2 j (by omega)⟩⟩
    have hh := hw.1 j
    simp only [signedHeight_projection,signedHeight_zero,Int.cast_zero] at hh
    exact_mod_cast hh

lemma raw_duration_tail_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H T : ℕ) (hH : 0 < H) :
    (annealedLaw ν).real {X | T < (firstWord (realPosition (step e)) X).length} ≤
      (annealedLaw ν).real (NoTruePastHeight e H)+(annealedLaw ν).real (StripUntil e H T) := by
  apply le_trans ?_ (measureReal_union_le _ _)
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [annealed_nearest_neighbor ν,htrans] with X hNN ht
  exact duration_tail_cover e H T hH X hNN ht

lemma duration_polynomial_rapidDecay {d : ℕ} (hd : 2 ≤ d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℕ, 0 < A ∧ RapidDecay (fun N =>
      (conditionedLaw ν (realPosition (step e))).real
        {X | A*(N+1)^(4*d+2) < (firstWord (realPosition (step e)) X).length}) := by
  obtain ⟨A,hA,htime⟩ := stripTime_rapidDecay hd ν hue e htrans
  have ht := htime.comp_strictMono (fun _ => measureReal_nonneg) _ square_pred_strictMono
  have ht' : RapidDecay (fun N => (annealedLaw ν).real
      (StripUntil e ((N+1)^2) (A*(N+1)^(4*d+2)))) := by
    convert ht using 1
    ext N
    have hsq : 1 ≤ (N+1)^2 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.sub_add_cancel hsq,← pow_mul,show 2*(2*d+1)=4*d+2 by omega]
  have hw := noTruePastSquare_rapidDecay hd ν hue e htrans
  have hraw : RapidDecay (fun N => (annealedLaw ν).real
      {X | A*(N+1)^(4*d+2) < (firstWord (realPosition (step e)) X).length}) := by
    apply (hw.add ht').of_le (fun _ => measureReal_nonneg)
    exact Eventually.of_forall (fun N => raw_duration_tail_bound ν e htrans ((N+1)^2) _ (by positivity))
  have hp := noDrop_positive_of_directionallyTransient ν (realPosition (step e)) htrans
  have hp' : 0 < (annealedLaw ν).real (NoDrop (realPosition (step e)) 0) :=
    ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  refine ⟨A,hA,(hraw.const_mul (((annealedLaw ν).real (NoDrop (realPosition (step e)) 0))⁻¹)).of_le
    (fun _ => measureReal_nonneg) ?_⟩
  apply Eventually.of_forall
  intro N
  have hh := annealed_ge_noDrop_mul_conditioned ν (realPosition (step e)) hp.ne'
    {X | A*(N+1)^(4*d+2) < (firstWord (realPosition (step e)) X).length}
    (measurableSet_lt measurable_const ((measurable_of_countable List.length).comp (measurable_firstWord _)))
  exact (le_inv_mul_iff₀ hp').mpr hh

end DirectionalTransience

end

end OAI
