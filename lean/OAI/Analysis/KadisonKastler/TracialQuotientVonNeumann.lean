import OAI.Analysis.KadisonKastler.TracialQuotientCompleteness
import OAI.Analysis.KadisonKastler.KaplanskyDensity

namespace OAI

/-! # The tracial sequence quotient is a represented von Neumann algebra -/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local notation "Q" => TracialSequenceQuotient τ ω
local notation "φ" => tracialQuotientTrace τ ω
local instance : PartialOrder Q := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing _
local notation "K" => TraceStateHilbert φ
local notation "π" => traceStateRepresentation φ
local notation "ι" => traceStateVector φ

def tracialSequenceAlgebra : VonNeumannAlgebra K :=
  generatedVonNeumannAlgebra (traceStateRepresentation φ).range

/-- A contraction in the bicommutant is recovered by bounded two-completeness. -/
theorem tracialSequenceAlgebra_contraction_in_range (hω : (ω : Filter ℕ) ≤ atTop)
    (T : K →L[ℂ] K) (hT : T ∈ tracialSequenceAlgebra τ ω) (hn : ‖T‖ ≤ 1) :
    ∃ b : Q, π b = T := by
  classical
  have ht : T ∈ Set.centralizer (Set.centralizer ((traceStateRepresentation φ).range : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra (traceStateRepresentation φ).range : Set (K →L[ℂ] K)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  have happ (n : ℕ) : ∃ b : Q, ‖b‖ ≤ 1 ∧ ‖T (ι 1) - ι b‖ < 1 / (n + 1 : ℝ) := by
    obtain ⟨S, hSn, hS⟩ := publishedKaplanskyDensity K (traceStateRepresentation φ).range T ht hn
      {ι 1} (1 / (n + 1 : ℝ)) (by positivity)
    obtain ⟨b, hb⟩ := S.property
    change π b = S.val at hb
    refine ⟨b, ?_, ?_⟩
    · rw [← norm_traceStateRepresentation φ b, hb]
      exact hSn
    · have h := hS (ι 1) (Finset.mem_singleton_self _)
      rw [← hb, traceStateRepresentation_vector, mul_one] at h
      exact h
  choose a han ha using happ
  have halim : Tendsto (fun n => ι (a n)) atTop (𝓝 (T (ι 1))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
      (Eventually.of_forall (fun n => ?_)) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [dist_eq_norm, norm_sub_rev] using (ha n).le
  obtain ⟨b, _, hb⟩ := tracialQuotient_bounded_complete τ ω hω a 1 zero_le_one han halim.cauchySeq
  have hbone : ι b = T (ι 1) := tendsto_nhds_unique hb halim
  refine ⟨b, ?_⟩
  apply DFunLike.ext'
  apply (traceStateVector_dense φ).equalizer (π b).continuous T.continuous
  funext a
  have hcomm : traceStateRight φ a * T = T * traceStateRight φ a := by
    apply ht
    intro S hS
    obtain ⟨c, rfl⟩ := hS
    exact (traceState_left_right_commute φ c a).eq
  have hcommv := congrArg (fun R : K →L[ℂ] K => R (ι 1)) hcomm
  change π b (ι a) = T (ι a)
  simpa only [mul_apply_eq_comp, traceStateRight_vector, one_mul,
    ← hbone, traceStateRepresentation_vector] using hcommv

end

end KadisonKastler

end OAI
