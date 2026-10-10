import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryTranscript
import OAI.Probability.CriticalPercolation.Entropy.MarkedBits
import OAI.Probability.CriticalPercolation.Entropy.BinaryOutput

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*}
local instance stagesFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def stageIndices (n : ℕ) (D : FixedDescriptor n) (k : ℕ) : Finset (Fin n) :=
  (activeSteps n D).filter fun i => i.val < k

noncomputable def stage (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool)
    (m : Fin n → Option E) (k : ℕ) : E → Bool := opened (stageIndices n D k) m ω

lemma stage_zero (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E) :
    stage n D ω m 0 = ω := by
  simp only [stage,stageIndices,Nat.not_lt_zero,Finset.filter_false,opened_empty]

lemma stage_last (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E) :
    stage n D ω m n = opened (activeSteps n D) m ω := by
  unfold stage stageIndices
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]

lemma stageIndices_succ_active (n : ℕ) (D : FixedDescriptor n) (i : Fin n)
    (hi : i ∈ activeSteps n D) :
    stageIndices n D (i.val+1) = insert i (stageIndices n D i.val) := by
  ext j
  simp only [stageIndices,Finset.mem_filter,Finset.mem_insert]
  constructor
  · rintro ⟨hj,hji⟩
    by_cases he : j=i
    · exact Or.inl he
    · exact Or.inr ⟨hj,by have hne : j.val ≠ i.val := fun e => he (Fin.ext e); omega⟩
  · rintro (rfl|⟨hj,hji⟩)
    · exact ⟨hi,Nat.lt_succ_self _⟩
    · exact ⟨hj,Nat.lt_succ_of_lt hji⟩

lemma stageIndices_succ_inactive (n : ℕ) (D : FixedDescriptor n) (i : Fin n)
    (hi : i ∉ activeSteps n D) : stageIndices n D (i.val+1) = stageIndices n D i.val := by
  ext j
  simp only [stageIndices,Finset.mem_filter]
  constructor
  · rintro ⟨hj,hji⟩
    refine ⟨hj,?_⟩
    have he : j.val ≠ i.val := fun he => hi (Fin.ext he ▸ hj)
    omega
  · rintro ⟨hj,hji⟩
    exact ⟨hj,Nat.lt_succ_of_lt hji⟩

lemma configuration_opened (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E)
    (S : Finset (Fin n)) :
    configuration (opened S m ω) = switched n (fromWords n (fun j => (D j).1) m)
      (configuration ω) (S.image fun i => i.val+2) := by
  apply Set.ext
  intro e
  have hm (i : Fin n) : nodeMark n (fromWords n (fun j => (D j).1) m) (i.val+2) = m i := by
    rw [← marks_nodeMark,marks_fromWords]
  simp only [configuration,MarkedBits.opened,switched,Set.mem_ofPred_eq]
  simp only [Finset.mem_image,exists_exists_and_eq_and,hm]
  by_cases he : ∃ i ∈ S, m i = some e
  · simp only [he,ite_true,or_true]
  · simp only [he,ite_false,or_false]
    rfl

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_mark_closed (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) : ω e = false := by
  obtain ⟨f,hf,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hfe : f=e := Option.some.inj (hf.symm.trans he)
  subst f
  have hc := admissible_closed G _ _ _ (scheduled_parent_mem d x n D i) ω e ha
  exact Bool.eq_false_iff.mpr hc

lemma supported_marks_distinct (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i j : Fin n)
    (e : E) (hi : m i = some e) (hj : m j = some e) : i=j := by
  obtain ⟨_,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hm (j : Fin n) : nodeMark n h (j.val+2) = m j := by rw [← marks_nodeMark,marks_fromWords]
  have he := selected_marks_injective G order d x p w _ n h _ hr _ _ (by omega) (by omega)
    (by have := i.isLt; omega) (by have := j.isLt; omega) e ((hm i).trans hi) ((hm j).trans hj)
  exact Fin.ext (by omega)

lemma supported_stage_closed (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) :
    stage n D ω m i.val e = false := by
  rw [stage,opened_unchanged]
  · exact supported_mark_closed G order d x p w s n D ω m hz i hi e he
  · intro j hj hje
    have hjlt := (Finset.mem_filter.mp hj).2
    have hji := supported_marks_distinct G order d x p w s n D ω m hz j i e hje he
    subst j
    omega

lemma supported_stage_close (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) :
    Function.update (stage n D ω m (i.val+1)) e false = stage n D ω m i.val := by
  dsimp only [stage]
  rw [stageIndices_succ_active n D i hi]
  apply close_opened_insert _ m ω i e he (supported_mark_closed G order d x p w s n D ω m hz i hi e he)
  intro j hj hje
  have hjlt := (Finset.mem_filter.mp hj).2
  have hji := supported_marks_distinct G order d x p w s n D ω m hz j i e hje he
  subst j
  omega

lemma supported_opening_injective
    (z z' : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0)
    (hz' : conditionedMass G order d x p w s n D z' ≠ 0)
    (he : (stage n D z.1 z.2 n,masked (activeSteps n D) z.2,masked (activeSteps n D)ᶜ z.2) =
      (stage n D z'.1 z'.2 n,masked (activeSteps n D) z'.2,masked (activeSteps n D)ᶜ z'.2)) : z=z' := by
  rcases z with ⟨ω,m⟩
  rcases z' with ⟨η,m'⟩
  have hm : m=m' := masked_injective (activeSteps n D) m m'
    (congrArg (fun y => y.2.1) he) (congrArg (fun y => y.2.2) he)
  subst m'
  have ho := congrArg Prod.fst he
  simp only [stage_last] at ho
  exact Prod.ext (opened_injective_closed _ m ω η
    (supported_mark_closed G order d x p w s n D ω m hz)
    (supported_mark_closed G order d x p w s n D η m hz') ho) rfl

lemma stage_endpointEvent (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) :
    endpointEvent G
      (x (interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))).1)
      (x (interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))).2) s
      (configuration (stage n D ω m n)) := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  rw [stage_last,configuration_opened]
  have he := switched_endpointEvent G order d x p w s n (fromWords n (fun j => (D j).1) m) _ hr
  rw [activeNodes_eq_descriptor G d x n _ _ D hD] at he
  rw [interval_fromWords d n _ m (fun _ => none)] at he
  exact he

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
