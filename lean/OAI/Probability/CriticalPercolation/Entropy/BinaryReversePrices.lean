import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryStages
import OAI.Probability.CriticalPercolation.Entropy.BinaryReverseKernels

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]

lemma reverseGuess_mark (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (hp : p ≠ 0) (w : E → Prop → ℝ)
    (ω : E → Bool) (e : E) (ha : Admissible G B a b ω e) :
    (LazyDFS.search G order a B).reverseGuess p
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
      (Function.update (configuration ω) e True) 0 e =
      ((1-p)/p) * markWeight G order B a b p w ω e /
        (1+markCost G order B a b p w ω e)^2 := by
  obtain ⟨hn,u,v,hev,hu,hv⟩ := ha
  have hc := admissible_closed G B a b hb ω e ⟨hn,u,v,hev,hu,hv⟩
  have hpi := G.contact_exit_pivot (configuration ω) B a u v e hev hc hn hu ⟨b,hb,hv.symm⟩
  have ha : Admissible G B a b ω e := ⟨hn,u,v,hev,hu,hv⟩
  simp only [reverseGuess,ite_eq_left hpi,add_zero,markWeight,markCost,ite_eq_left ha,
    queryDelta_update]
  field_simp

end CriticalPercolation.ExactExposure

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
local instance pricesFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_guess_price (hp : p ≠ 0) (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) :
    pivotGuess G order d x p w n D i (stage n D ω m (i.val+1)) e =
      ((1-p)/p) * selectedWeight G order d x p w n D i ω (m i) /
        (1+selectedCost G order d x p w n D i ω (m i))^2 := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hin : i.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have hc := active_canonical G order d x p w _ n h _ hr _ hin
  have hm : nodeMark n h (i.val+2) = some e := by rw [← marks_nodeMark,marks_fromWords,he]
  have ht : targets d x n h (i.val+2) = stepTargets (E := E) d x n D i := by
    change _ = scheduledTargets (E := E) d x n (fun j => (D j).1) i.val
    rw [targets_prefix d x n h _ i.isLt.le,scheduledTargets_eq d x n _ m _ i.isLt.le]
  have hl : (node d x n h (i.val+2)).1 = stepLeft (E := E) d x n D i :=
    congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
  have hS : ∀ j ∈ (stageIndices n D i.val).image (fun i => i.val+2), 2 ≤ j ∧ j < i.val+2 := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hklt := (Finset.mem_filter.mp hk).2
    omega
  have hh := (switched_contact_reconstruction G order d x p w _ n h (configuration ω) hr
    (i.val+2) (by omega) (by have := i.isLt; omega) hc e hm _ hS 0).2.2
  rw [hl,ht] at hh
  unfold pivotGuess
  rw [stage,configuration_opened,stageIndices_succ_active n D i hi,Finset.image_insert]
  rw [← hh]
  obtain ⟨f,hf,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hfe : f=e := Option.some.inj (hf.symm.trans he)
  subst f
  have hpr := reverseGuess_mark G order (stepTargets (E := E) d x n D i)
    (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i)
    (scheduled_parent_mem d x n D i) p hp w ω e ha
  simpa only [selectedWeight,selectedCost,ite_eq_left (Finset.mem_filter.mp hi).2,he] using hpr

lemma supported_inverse_update (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    inverseUpdate (E := E) n D i.val (stage n D ω m (i.val+1)) (masked (activeSteps n D) m i) =
      stage n D ω m i.val := by
  unfold inverseUpdate
  rw [dite_eq_left i.isLt]
  by_cases hi : i ∈ activeSteps n D
  · obtain ⟨e,he,_⟩ := supported_active_admissible G order d x p w s n D ω m hz
      ⟨i,(Finset.mem_filter.mp hi).2⟩
    simp only [ite_eq_left hi,masked,he]
    exact supported_stage_close G order d x p w s n D ω m hz i hi e he
  · simp only [ite_eq_right hi,stage,stageIndices_succ_inactive n D i hi]

lemma supported_recover (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) :
    ReverseReference.recover (inverseUpdate (E := E) n D) n (stage n D ω m n)
      (masked (activeSteps n D) m) = ω := by
  let m' : ℕ → Option E := fun j => if hj : j<n then masked (activeSteps n D) m ⟨j,hj⟩ else none
  have hm : (fun i : Fin n => m' i.val) = masked (activeSteps n D) m := by
    funext i
    simp only [m',dite_eq_left i.isLt]
  have hh := ReverseReference.recover_trajectory (inverseUpdate (E := E) n D)
    (stage n D ω m) m' n (fun j hj => by
      simpa only [m',dite_eq_left hj] using supported_inverse_update G order d x p w s n D ω m hz ⟨j,hj⟩)
  rw [hm,stage_zero] at hh
  exact hh

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
