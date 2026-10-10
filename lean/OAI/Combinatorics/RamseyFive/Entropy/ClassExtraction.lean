import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OrderedExtraction
import OAI.Combinatorics.RamseyFive.Entropy.ClassSelection

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {κ α β : Type*} [Fintype κ] [Fintype α] [Fintype β]
local instance classExtractκDE : DecidableEq κ := Classical.decEq _
local instance classExtractαDE : DecidableEq α := Classical.decEq _
local instance classExtractβDE : DecidableEq β := Classical.decEq _
local instance classExtractFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

lemma conditionOn_mean_le_pos (p : Law α) (E : Finset α) (hE : 0 < eventMass p E)
    (f : α→ℝ) (hf : ∀ a,0 < p a → 0 ≤ f a) :
    mean (conditionOn p E hE) f ≤ mean p f/eventMass p E := by
  simp only [mean,Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : 0 < p a
  · simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right (conditionOn_le p E hE a) (hf a hp)
  · have hz : p a=0 := le_antisymm (le_of_not_gt hp) (p.nonneg a)
    have hz' : conditionOn p E hE a=0 := by simp [conditionOn_apply,hz]
    simp only [hz,hz',zero_mul,zero_div,le_refl]

lemma conditionContext_first (p : Law (κ×α)) (E : Finset κ)
    (hE : 0 < eventMass (first p) E) :
    first (conditionContext p E hE)=conditionOn (first p) E hE := by
  apply Law.ext
  funext c
  simp only [conditionContext,first,adaptiveLaw,←Finset.mul_sum,(fiber p c).sum_one,mul_one]

def selectedClassIndices {n l : ℕ} (hl : l ≤ n) (U : κ→Finset (Fin n))
    (code : κ→Fin n→α) (a : α) (c : κ) : Fin l ↪o Fin n :=
  retainedIndices hl (classPositions (U c) (code c) a)

def selectedClassEvent {n : ℕ} (l : ℕ) (U : κ→Finset (Fin n))
    (code : κ→Fin n→α) (a : α) : Finset κ :=
  Finset.univ.filter fun c=>l ≤ (classPositions (U c) (code c) a).card

omit [Fintype α] in
lemma selectedClassIndices_properties {n l : ℕ} (hl : l ≤ n) (U : κ→Finset (Fin n))
    (code : κ→Fin n→α) (a : α) (c : κ) (hc : c∈selectedClassEvent l U code a)
    (i : Fin l) : selectedClassIndices hl U code a c i∈U c ∧
      code c (selectedClassIndices hl U code a c i)=a := by
  have hi:=retainedIndices_mem hl (classPositions (U c) (code c) a)
    (Finset.mem_filter.mp hc).2 i
  exact Finset.mem_filter.mp hi

omit [Fintype α] in
theorem selectedClass_deficit {n l : ℕ} (hl : l ≤ n) (p : Law (κ×(Fin n→β)))
    (U : κ→Finset (Fin n)) (code : κ→Fin n→α) (a : α)
    (hE : 0 < eventMass (first p) (selectedClassEvent l U code a)) (J : ℝ)
    (hnonneg : ∀ c,0 < first p c → 0 ≤ activeDeficit (fiber p c) (U c) J)
    (hfix : ∀ c,0 < first p c → FixedOutside (fiber p c) (U c))
    (hcap : ∀ c,0 < first p c → ∀ i∈U c,entropy (map (fiber p c) (fun x=>x i)) ≤ J) :
    let q:=conditionContext p (selectedClassEvent l U code a) hE
    let f:=fun c=>(selectedClassIndices hl U code a c).toEmbedding
    mean (first (selectByContext q (fun c=>(f c : Fin l→Fin n))))
      (fun c=>(l:ℝ)*J-entropy (fiber (selectByContext q (fun c=>(f c : Fin l→Fin n))) c)) ≤
      mean (first p) (fun c=>activeDeficit (fiber p c) (U c) J)/
        eventMass (first p) (selectedClassEvent l U code a) := by
  dsimp only
  let E:=selectedClassEvent l U code a
  let q:=conditionContext p E hE
  have hpos (c : κ) (hc : 0 < first q c) : c∈E ∧ 0 < first p c := by
    rw [conditionContext_first] at hc
    exact conditionOn_positive (first p) E hE c hc
  have hfib (c : κ) (hc : 0 < first q c) : fiber q c=fiber p c := by
    apply conditionContext_fiber
    rwa [←conditionContext_first]
  have hh:=selectByContext_deficit q U
    (fun c=>(selectedClassIndices hl U code a c).toEmbedding) J
    (fun c hc i=>(selectedClassIndices_properties hl U code a c (hpos c hc).1 i).1)
    (fun c hc=>by rw [hfib c hc];exact hfix c (hpos c hc).2)
    (fun c hc i hi=>by rw [hfib c hc];exact hcap c (hpos c hc).2 i hi)
  simp only [Fintype.card_fin] at hh
  apply hh.trans
  calc
    _ = mean (conditionOn (first p) E hE) (fun c=>activeDeficit (fiber p c) (U c) J) := by
      rw [←conditionContext_first]
      apply le_antisymm <;> apply mean_mono_pos
      · intro c hc; rw [hfib c hc]
      · intro c hc; rw [hfib c hc]
    _ ≤ _ := conditionOn_mean_le_pos (first p) E hE _ hnonneg
end
end SharpRamseyFive.FiniteEntropy

end OAI
