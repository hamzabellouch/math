import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryConfiguration
import OAI.Probability.CriticalPercolation.Entropy.BinaryCosts

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

abbrev stepLeft (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : V :=
  (descriptorNode (E := E) d x n D (i.val+2)).1
abbrev stepRight (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : V :=
  (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val+2))).1
abbrev stepTargets (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) : Set V :=
  scheduledTargets (E := E) d x n (fun j => (D j).1) i.val

def activeSteps (n : ℕ) (D : FixedDescriptor n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (D i).2.2 = true

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

noncomputable def pairQuery (i : Fin n) : QueryTree E :=
  (pair G (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i)).bare

noncomputable def selectedTranscript (i : Fin n) (ω : E → Bool) : E → Bool :=
  if (D i).2.2 = true then
    representative (pairQuery G d x n D i).run (fun _ => false) ((pairQuery G d x n D i).run ω)
  else ω

noncomputable def selectedWeight (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if (D i).2.2 = true then match m with
    | none => 0
    | some e => markWeight G order (stepTargets (E := E) d x n D i)
        (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i) p w ω e
  else scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m

noncomputable def selectedCost (i : Fin n) (ω : E → Bool) (m : Option E) : ℝ :=
  if (D i).2.2 = true then match m with
    | none => 0
    | some e => markCost G order (stepTargets (E := E) d x n D i)
        (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i) p w ω e
  else 0

lemma selected_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) (m : Option E) :
    0 ≤ selectedWeight G order d x p w n D i ω m ∧
      0 ≤ selectedCost G order d x p w n D i ω m := by
  unfold selectedWeight selectedCost
  split_ifs
  · cases m with
    | none => exact ⟨le_rfl,le_rfl⟩
    | some e => exact mark_nonneg G order _ _ _ hp w h0 h1 ω e
  · exact ⟨scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m,le_rfl⟩

lemma selected_run (i : Fin n) (ω : E → Bool) (m : Option E) :
    selectedWeight G order d x p w n D i (selectedTranscript G d x n D i ω) m =
      selectedWeight G order d x p w n D i ω m ∧
    selectedCost G order d x p w n D i (selectedTranscript G d x n D i ω) m =
      selectedCost G order d x p w n D i ω m := by
  unfold selectedWeight selectedCost selectedTranscript
  split_ifs with hi
  · cases m with
    | none => exact ⟨rfl,rfl⟩
    | some e =>
      exact pair_mark_congr G order _ _ _ (scheduled_parent_mem d x n D i) p w _ ω
        (representative_run (pairQuery G d x n D i).run (fun _ => false) ω) e
  · exact ⟨rfl,rfl⟩

lemma selectedWeight_le_raw (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) (m : Option E) :
    selectedWeight G order d x p w n D i ω m ≤
      scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m := by
  unfold selectedWeight
  split_ifs
  · cases m with
    | none => exact scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ none
    | some e =>
      unfold scheduleWeight
      rw [scheduledAnchor_node]
      exact G.markWeight_le_raw order _ _ _ (scheduled_parent_mem d x n D i) hp w h0 h1 ω e
  · exact le_rfl

lemma supported_selected_eq (s : ℕ) (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    selectedWeight G order d x p w n D i ω (m i) =
      scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) := by
  unfold selectedWeight
  split_ifs with hi
  · obtain ⟨e,he,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz ⟨i,hi⟩
    dsimp only at he ha
    rw [he]
    unfold scheduleWeight
    rw [scheduledAnchor_node]
    exact G.markWeight_eq_raw_of_admissible order _ _ _ (scheduled_parent_mem d x n D i) p w ω e ha
  · rfl

lemma supported_selected_positive (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (z : (E → Bool) × (Fin n → Option E))
    (hz : 0 < conditionedMass G order d x p w s n D z) (i : Fin n) :
    0 < selectedWeight G order d x p w n D i (selectedTranscript G d x n D i z.1) (z.2 i) := by
  rw [(selected_run G order d x p w n D i z.1 (z.2 i)).1,
    supported_selected_eq G order d x p w n D s z.1 z.2 hz.ne' i]
  exact lt_of_le_of_ne (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _)
    (Ne.symm (supported_schedule_ne_zero G order d x p w s n D z.1 z.2 hz.ne' i))

lemma selected_moment (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (i : Fin n) (hi : i ∈ activeSteps n D) :
    (∑ ym : (E → Bool) × Option E,
      pushMass (selectedTranscript G d x n D i) (FiniteProduct.density (QueryTree.bitWeight p)) ym.1 *
      selectedWeight G order d x p w n D i ym.1 ym.2 *
        (1+selectedCost G order d x p w n D i ym.1 ym.2)) ≤ 4 := by
  have hi' : (D i).2.2 = true := (Finset.mem_filter.mp hi).2
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [sum_pushMass_mul]
  simp_rw [(selected_run G order d x p w n D i _ _).1,
    (selected_run G order d x p w n D i _ _).2]
  simp only [selectedWeight,selectedCost,ite_eq_left hi',Fintype.sum_option,zero_mul,zero_add]
  exact marked_pair_bound G order horder ho _ _ _ (scheduled_parent_mem d x n D i) hp w h0 h1

end CriticalPercolation.BinaryLaw
end
end

end OAI
