import OAI.Analysis.KadisonKastler.TracialDiagonalLimit
import OAI.Analysis.KadisonKastler.FaithfulTraceGNS
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Two-norm completeness on bounded sets of the tracial quotient -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  (τ : ∀ j, FaithfulTracialState (B j)) (ω : Ultrafilter ℕ)

local notation "Q" => TracialSequenceQuotient τ ω
local notation "φ" => tracialQuotientTrace τ ω
local instance : PartialOrder Q := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing Q := CStarAlgebra.spectralOrderedRing _

/-- Every operator-norm-bounded two-Cauchy sequence has its GNS limit in
this quotient. A one-unit norm slack suffices for the subsequent closure proof. -/
theorem tracialQuotient_bounded_complete (hω : (ω : Filter ℕ) ≤ atTop)
    (a : ℕ → Q) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hc : CauchySeq (fun n => traceStateVector φ (a n))) :
    ∃ b : Q, ‖b‖ ≤ C + 1 ∧
      Tendsto (fun n => traceStateVector φ (a n)) atTop (𝓝 (traceStateVector φ b)) := by
  obtain ⟨f, hf, hfast⟩ := Metric.exists_subseq_bounded_of_cauchySeq
    (fun n => traceStateVector φ (a n)) hc (fun n => 1 / (n + 1 : ℝ))
    (fun n => by positivity)
  have hlift (n : ℕ) : ∃ x : VaryingBoundedSequence B,
      tracialSequenceQuotientMap τ ω x = a (f n) ∧ ‖x‖ < ‖a (f n)‖ + 1 :=
    (traceNullClosedIdeal τ ω).quotient_norm_lt_rep (a (f n)) (by norm_num)
  choose x hx hxn using hlift
  have hcoord (n j : ℕ) : ‖x n j‖ ≤ C + 1 :=
    (varyingSequence_norm_apply_le (x n) j).trans
      ((hxn n).le.trans (add_le_add (ha (f n)) le_rfl))
  have htwo (n m : ℕ) (hnm : n ≤ m) :
      traceTwoNorm φ (tracialSequenceQuotientMap τ ω (x m) -
        tracialSequenceQuotientMap τ ω (x n)) < 1 / (n + 1 : ℝ) := by
    rw [hx, hx, ← norm_traceStateVector, traceStateVector_sub, ← dist_eq_norm]
    exact hfast n (f m) (hf.monotone hnm)
  obtain ⟨y, hyn, hy⟩ := exists_tracial_diagonal_limit τ ω hω x (C + 1)
    (by positivity) hcoord (fun n => 1 / (n + 1 : ℝ)) htwo
  let b := tracialSequenceQuotientMap τ ω y
  have hb : ‖b‖ ≤ C + 1 :=
    (NonUnitalStarAlgHom.norm_apply_le (tracialSequenceQuotientMap τ ω) y).trans hyn
  refine ⟨b, hb, tendsto_nhds_of_cauchySeq_of_subseq hc hf.tendsto_atTop ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
    (Eventually.of_forall (fun n => ?_)) tendsto_one_div_add_atTop_nhds_zero_nat
  change dist (traceStateVector φ (a (f n))) (traceStateVector φ b) ≤ _
  rw [dist_comm, dist_eq_norm, ← traceStateVector_sub, norm_traceStateVector]
  exact (by simpa only [hx] using hy n)

end

end KadisonKastler

end OAI
