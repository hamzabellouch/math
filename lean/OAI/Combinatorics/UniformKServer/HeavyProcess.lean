import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyRecordGeometry

namespace OAI

                                   
section

/-! A horizon-independent fixed-slot heavy process with the source's one-step
cooldown. Its centers equal the radius-independent deterministic schedule. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

def empty (a : X) : State X Λ r where
  present := ∅
  center := fun _ => a
  radius := fun _ => 0
  radius_bounds := by simp
  separated := by simp

def fresh (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ) : Λ :=
  Classical.choose (fresh_exists S T hr hΛ)

theorem fresh_absent (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ) :
    fresh S T hr hΛ ∉ S.present ∧ fresh S T hr hΛ ∉ T.present := by
  have h := Classical.choose_spec (fresh_exists S T hr hΛ)
  simpa only [fresh,mem_union,not_or] using h

def step (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R ∈ Set.Icc (16*r) (20*r)) : State X Λ r :=
  if HeavySchedule.trigger r h (centers S) x then
    HeavyRecords.insert S hr x R hR (fresh S T hr hΛ) (fresh_absent S T hr hΛ).1
  else S

theorem centers_step (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R ∈ Set.Icc (16*r) (20*r)) :
    centers (step S T hr hΛ h x R hR)=HeavySchedule.step r h (centers S) x := by
  unfold step HeavySchedule.step
  split_ifs
  · exact centers_insert S hr x R hR _ _
  · rfl

theorem cooldown_step (S T : State X Λ r) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : Prop) (x : X) (R : ℝ) (hR : R ∈ Set.Icc (16*r) (20*r)) (l : Λ)
    (hl : l ∈ (step S T hr hΛ h x R hR).present) (ho : l ∉ S.present) : l ∉ T.present := by
  unfold step at hl
  split_ifs at hl
  · change l ∈ Insert.insert _ (survivors S x) at hl
    rcases mem_insert.mp hl with he | hs
    · rcases chosen_cases S x R (fresh S T hr hΛ) with hi | ⟨hi,_⟩
      · have hp := (Classical.choose_spec hi).1.1
        exact (ho (he ▸ hp)).elim
      · rw [he,hi]
        exact (fresh_absent S T hr hΛ).2
    · exact (ho (mem_filter.mp hs).1).elim
  · exact (ho hl).elim

def runPair (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r)) :
    ℕ → State X Λ r × State X Λ r
  | 0 => (empty a,empty a)
  | t+1 => let ST := runPair a hr hΛ h x R hR t
           (ST.2,step ST.2 ST.1 hr hΛ (h t) (x t) (R t) (hR t))

def run (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) : State X Λ r := (runPair a hr hΛ h x R hR t).2

theorem run_centers (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) : centers (run a hr hΛ h x R hR t)=HeavySchedule.centers r h x t := by
  induction t with
  | zero => simp only [run,runPair,empty,centers,image_empty,HeavySchedule.centers]
  | succ t ih =>
    change centers (step _ _ hr hΛ (h t) (x t) (R t) (hR t))=_
    rw [centers_step]
    change HeavySchedule.step r (h t) (centers (run a hr hΛ h x R hR t)) (x t)=_
    rw [ih]
    rfl

theorem run_cooldown (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (l : Λ) (hnew : l ∈ (run a hr hΛ h x R hR (t+2)).present)
    (hold : l ∉ (run a hr hΛ h x R hR (t+1)).present) :
    l ∉ (run a hr hΛ h x R hR t).present := by
  exact cooldown_step _ _ hr hΛ (h (t+1)) (x (t+1)) (R (t+1)) (hR (t+1)) l hnew hold

theorem run_coverage (a : X) (hr : 0 ≤ r) (hΛ : 2*Fintype.card X < Fintype.card Λ)
    (h : ℕ → Prop) (x : ℕ → X) (R : ℕ → ℝ) (hR : ∀ t, R t ∈ Set.Icc (16*r) (20*r))
    (t : ℕ) (hh : h t) : ∃ l, covers (run a hr hΛ h x R hR (t+1)) l (x t) := by
  have hc := HeavySchedule.centers_coverage r hr h x t hh
  rw [←run_centers a hr hΛ h x R hR] at hc
  obtain ⟨c,hc,hd⟩ := hc
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hc
  refine ⟨l,hl,?_⟩
  have hb := ((run a hr hΛ h x R hR (t+1)).radius_bounds l hl).1
  rw [dist_comm] at hd
  linarith

end UniformKServer.HeavyProcess

end


end

end OAI
