import OAI.NumberTheory.JointDickman.Counting.EndpointCountingCutoff
import OAI.NumberTheory.JointDickman.Amplification.FiniteCutoffProfiles

namespace OAI

/-! # Periodic averaging of the error for each actual candidate representation -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def baseCandidateContribution (B L T H M : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) (u : ℕ) : ℝ :=
  if e ∈ blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) then
    candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (smoothCandidateCutoff B T) e else 0

theorem baseCandidateContribution_nonneg (B L T H M : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) (u : ℕ) : 0 ≤ baseCandidateContribution B L T H M τ C e u := by
  unfold baseCandidateContribution
  split_ifs
  · exact candidateMeanWeight_nonneg B L τ C _ _ (smoothCandidateCutoff_nonneg B T) e
  · exact le_rfl

theorem baseCandidateContribution_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (h : u ≡ v [MOD auxiliarySquarePeriod B]) (e : BlockCandidateIndex M) :
    baseCandidateContribution B L T H M τ C e u = baseCandidateContribution B L T H M τ C e v := by
  have he := blockPrimeSites_modEq (M := M) h
  unfold baseCandidateContribution
  rw [he]

noncomputable def residueBaseContribution (B L T H M : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) (r : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  baseCandidateContribution B L T H M τ C e r.val

theorem residueBaseContribution_natCast (B L T H M : ℕ) (τ C : ℝ)
    (e : BlockCandidateIndex M) (u : ℕ) :
    residueBaseContribution B L T H M τ C e u = baseCandidateContribution B L T H M τ C e u := by
  unfold residueBaseContribution
  rw [ZMod.val_natCast]
  exact baseCandidateContribution_modEq (Nat.mod_modEq u _) e

open Classical in
theorem baseCandidateContribution_ramp_error {B L T H M : ℕ} {τ C δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (e : BlockCandidateIndex M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (∑ u ∈ range K, baseCandidateContribution B L T H M τ C e u*
        |(if ((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)) <
            (candidateLow e : ℝ)/(T*candidateQuotient e) then 1 else 0)-
          countingRamp δ (((u : ℝ)+(e.1.1.val+1))/((T : ℝ)*(N+1)))
            ((candidateLow e : ℝ)/(T*candidateQuotient e))|)/(N : ℝ) <
        (T : ℝ)*δ*((∑ r, residueBaseContribution B L T H M τ C e r)/(auxiliarySquarePeriod B : ℝ))+ε := by
  let f := residueBaseContribution B L T H M τ C e
  have hf : ∀ r, 0 ≤ f r := fun r => baseCandidateContribution_nonneg B L T H M τ C e r.val
  have hA : 0 ≤ ∑ r, f r := sum_nonneg (fun r _ => hf r)
  have hb : ∀ r, 0 ≤ f r ∧ f r ≤ ∑ r, f r := fun r =>
    ⟨hf r,single_le_sum (fun r _ => hf r) (mem_univ r)⟩
  filter_upwards [periodic_counting_ramp_error_eventually f hA hb hδ hT hε] with N hN
  intro K
  simpa only [f,residueBaseContribution_natCast] using
    hN (e.1.1.val+1) ((candidateLow e : ℝ)/(T*candidateQuotient e)) K

end JointDickman

end OAI
