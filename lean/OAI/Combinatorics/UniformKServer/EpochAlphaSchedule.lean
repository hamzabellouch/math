import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlpha
import OAI.Combinatorics.UniformKServer.AlphaEmpty
import OAI.Combinatorics.UniformKServer.SideReferenceSchedule

namespace OAI

                                         
section

/-! Actual total choice of the epoch proportions, including the empty branch.
 Validity is derived from the persistent epoch and forced side-reference
 recurrences; the inactive or zero-side cases are not excluded. -/
noncomputable section
namespace UniformKServer.EpochAlphaSchedule
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def config (a : ι → ℝ) (s : EpochGeometry.State ι) (U ell ct C : ℝ) : AlphaEmpty.Config ι :=
  if (EpochParameters.active a).Nonempty then
    match EpochGeometry.dominant s with
    | none => some (EpochAlpha.regular a (EpochGeometry.total s.base) ell ct C)
    | some o => if ho : o ∈ EpochParameters.active a then
        if U=0 then some (EpochAlpha.singleton a ell ct C ⟨o,ho⟩)
        else some (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C ⟨o,ho⟩)
      else none
  else none

theorem dominant_active {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) {o : ι} (ho : EpochGeometry.dominant s=some o) :
    o ∈ EpochParameters.active a := by
  apply EpochParameters.mem_active.mpr
  have hp := (EpochGeometry.dominant_spec ho).1
  have hl := (EpochGeometry.dominant_size hs ho).1
  linarith

theorem active_eq {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (U ell ct C : ℝ) :
    AlphaEmpty.active (config a s U ell ct C)=EpochParameters.active a := by
  unfold config
  split
  · rename_i hn
    cases ho : EpochGeometry.dominant s with
    | none => rfl
    | some o =>
      simp only [dite_eq_left (dominant_active hs ho)]
      split_ifs <;> rfl
  · rename_i hn
    exact (Finset.not_nonempty_iff_eq_empty.mp hn).symm

theorem valid_config {a : ι → ℝ} {s : EpochGeometry.State ι}
    (hs : EpochGeometry.valid a s) (ha : ∀ i, 0 ≤ a i)
    {U ell ct C : ℝ} (hl : 1 ≤ ell) (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct)
    (hheight : ∀ i : EpochParameters.active a,
      SideParameters.height (EpochGeometry.total s.base) (a i) ≤ 50000*ell)
    (hU : ∀ o, EpochGeometry.dominant s=some o → EpochParameters.sideReference a o U) :
    AlphaEmpty.valid (config a s U ell ct C) := by
  unfold config
  split
  · rename_i hn
    cases ho : EpochGeometry.dominant s with
    | none => exact EpochAlpha.regular_valid hs ha hn ho (by linarith) hc hct hC hheight
    | some o =>
      have hoa := dominant_active hs ho
      simp only [dite_eq_left hoa]
      split_ifs with hz
      · exact EpochAlpha.singleton_valid ⟨o,hoa⟩
          (EpochAlpha.side_zero_singleton ha ⟨o,hoa⟩ (hU o ho) hz) (by linarith) hc hC
      · exact EpochAlpha.marked_valid hs ha ⟨o,hoa⟩ ho (hU o ho)
          (lt_of_le_of_ne (hU o ho).1 (Ne.symm hz)) hl hc hct hC hheight
  · exact True.intro

theorem base_bound {a : ℕ → ι → ℝ} (p : ℕ → Bool) {K : ℝ}
    (ha : ∀ t, EpochGeometry.total (a t) ≤ K) : ∀ t,
    EpochGeometry.total (EpochGeometry.schedule a p t).base ≤ K := by
  intro t
  induction t with
  | zero => exact ha 0
  | succ t ih =>
    unfold EpochGeometry.schedule EpochGeometry.update
    split_ifs
    · exact ha (t+1)
    · exact ih

def schedule (a : ℕ → ι → ℝ) (p : ℕ → Bool) (k : ℕ) (ct C : ℝ) (t : ℕ) :
    AlphaEmpty.Config ι :=
  config (a t) (EpochGeometry.schedule a p t) (SideReferenceSchedule.reference a p t)
    (EpochAlpha.ell k) ct C

theorem schedule_valid {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (k : ℕ) {ct C : ℝ} (hc : 0 < ct) (hct : ct*50000 ≤ 1)
    (hC : 1000 < C*ct) (hsize : ∀ t, EpochGeometry.total (a t) ≤ 2*k)
    (hmin : ∀ t i, 0 < a t i → (9/100000:ℝ) ≤ a t i) (t : ℕ) :
    AlphaEmpty.valid (schedule a p k ct C t) := by
  have hv := EpochGeometry.schedule_valid ha p t
  apply valid_config hv (ha t) (EpochAlpha.ell_one k) hc hct hC
  · intro i
    have hai := EpochParameters.mem_active.mp i.property
    exact EpochAlpha.height_upper (EpochParameters.active_total_pos hv hai)
      (base_bound p hsize t) (hmin t i hai)
  · exact fun o ho => SideReferenceSchedule.reference_spec ha p t ho

theorem schedule_active {a : ℕ → ι → ℝ} (ha : ∀ t i, 0 ≤ a t i)
    (p : ℕ → Bool) (k : ℕ) (ct C : ℝ) (t : ℕ) :
    AlphaEmpty.active (schedule a p k ct C t)=EpochParameters.active (a t) :=
  active_eq (EpochGeometry.schedule_valid ha p t) _ _ _ _

end UniformKServer.EpochAlphaSchedule

end


end

end OAI
