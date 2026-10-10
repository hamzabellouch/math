import OAI.Probability.MatroidProphet.Pivots.Phases
import OAI.Probability.MatroidProphet.Residual.Generators
import Mathlib.Data.Int.Interval

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set

abbrev IntWindow (a : ℤ) := {k : ℤ // k ∈ Set.Icc (a - 2) 1}

noncomputable instance (a : ℤ) : Fintype (IntWindow a) := Fintype.ofFinite _

abbrev ParityWindow (a : ℤ) (ε : Fin 2) := {k : IntWindow a // k.val % 2 = (ε.val : ℤ)}

noncomputable instance (a : ℤ) (ε : Fin 2) : Fintype (ParityWindow a ε) := Fintype.ofFinite _

def roundParity (ε : Fin 2) (k : ℤ) : ℤ := if k % 2 = (ε.val : ℤ) then k else k + 1

lemma roundParity_bounds (ε : Fin 2) (k : ℤ) : k ≤ roundParity ε k ∧ roundParity ε k ≤ k + 1 := by
  unfold roundParity
  split <;> omega

lemma roundParity_mod (ε : Fin 2) (k : ℤ) : roundParity ε k % 2 = (ε.val : ℤ) := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

lemma roundParity_le_iff (ε : Fin 2) (k b : ℤ) (hb : b % 2 = (ε.val : ℤ)) :
    roundParity ε k ≤ b ↔ k ≤ b := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

lemma roundParity_lt_iff (ε : Fin 2) (k b : ℤ) (hb : b % 2 = (ε.val : ℤ)) :
    roundParity ε k < b ↔ k ≤ b - 2 := by
  have hε := ε.isLt
  unfold roundParity
  split <;> omega

variable {α G : Type*} [Fintype α] [LinearOrder α] [Fintype G]

def windowPlacement (a : ℤ) (ν : G → ℤ) (hν : ∀ g, a ≤ ν g ∧ ν g ≤ 0) : G → IntWindow a :=
  fun g => ⟨ν g, by have := hν g; constructor <;> omega⟩

def parityPlacement (a : ℤ) (ε : Fin 2) (ν : G → ℤ)
    (hν : ∀ g, a ≤ ν g ∧ ν g ≤ 0) : G → ParityWindow a ε :=
  fun g => ⟨⟨roundParity ε (ν g), by
    have := hν g
    have := roundParity_bounds ε (ν g)
    constructor <;> omega⟩, roundParity_mod ε (ν g)⟩

def generatedPath (M : Matroid α) (F : ℤ → Set α) (g : G → α) (ν : G → ℤ) (k : ℤ) : Set α :=
  M.closure (F k ∪ g '' {i | ν i ≤ k})

lemma window_prefix (M : Matroid α) (F : ℤ → Set α) (hF : Monotone F)
    (a : ℤ) (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (k : IntWindow a) :
    M.closure (blockPrefix (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν) k) =
      generatedPath M F g ν k.val := by
  rw [blockPrefix_eq (fun t : IntWindow a => F t.val) (fun _ _ h => hF h)]
  rfl

lemma parity_upperPath
    {α : Type u_1} {G : Type u_2} [Fintype α] [LinearOrder α] [Fintype G]
    (M : Matroid α) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (b : ParityWindow a ε) :
    upperPath M (fun t : ParityWindow a ε => F t.val.val) g (parityPlacement a ε ν hν) b =
      generatedPath M F g ν b.val.val := by
  have hs : {i | parityPlacement a ε ν hν i ≤ b} = {i | ν i ≤ b.val.val} := by
    ext i
    exact roundParity_le_iff ε (ν i) b.val.val b.property
  unfold upperPath generatedPath
  rw [hs]

lemma parity_lowerPath
    {α : Type u_1} {G : Type u_2} [Fintype α] [LinearOrder α] [Fintype G]
    (M : Matroid α) (hE : M.E = univ)
    (F : ℤ → Set α) (hF : Monotone F) (a : ℤ)
    (hFe : ∀ k < a, F k = M.closure ∅) (ε : Fin 2)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (b : ParityWindow a ε) :
    lowerPath M (fun t : ParityWindow a ε => F t.val.val) g (parityPlacement a ε ν hν) b =
      generatedPath M F g ν (b.val.val - 2) := by
  have hgen : g '' {i | parityPlacement a ε ν hν i < b} = g '' {i | ν i ≤ b.val.val - 2} := by
    congr 1
    ext i
    exact roundParity_lt_iff ε (ν i) b.val.val b.property
  unfold lowerPath generatedPath
  rw [hgen]
  apply Subset.antisymm
  · apply M.closure_subset_closure
    apply union_subset_union _ Subset.rfl
    intro e he
    obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
    have hcb : c.val.val ≤ b.val.val - 2 := by
      have hb := b.property
      have hcmod := c.property
      change c.val.val < b.val.val at hc
      omega
    exact hF hcb he
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · intro e he
      by_cases hlo : a - 2 ≤ b.val.val - 2
      · let c : ParityWindow a ε := ⟨⟨b.val.val - 2, ⟨hlo, by have := b.val.property.2; omega⟩⟩,
          by change (b.val.val - 2) % 2 = (ε.val : ℤ); have := b.property; omega⟩
        apply M.subset_closure _ (by simp [hE])
        left
        refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨?_, he⟩⟩
        change b.val.val - 2 < b.val.val
        omega
      · have hearly : b.val.val - 2 < a := by omega
        rw [hFe _ hearly] at he
        exact M.closure_subset_closure (empty_subset _) he
    · exact (subset_union_right.trans (M.subset_closure _ (by simp [hE])))

lemma window_before (M : Matroid α) (hE : M.E = univ)
    (F : ℤ → Set α) (hF : Monotone F) (a : ℤ)
    (hFe : ∀ k < a, F k = M.closure ∅)
    (g : G → α) (ν : G → ℤ) (hν : ∀ i, a ≤ ν i ∧ ν i ≤ 0) (k : IntWindow a) :
    M.closure (blockBefore (fun t : IntWindow a => F t.val) g (windowPlacement a ν hν) k) =
      generatedPath M F g ν (k.val - 1) := by
  rw [blockBefore_eq_iUnion]
  have hgen : g '' {i | windowPlacement a ν hν i < k} = g '' {i | ν i ≤ k.val - 1} := by
    congr 1
    ext i
    change ν i < k.val ↔ ν i ≤ k.val - 1
    omega
  rw [hgen]
  unfold generatedPath
  apply Subset.antisymm
  · apply M.closure_subset_closure
    apply union_subset_union _ Subset.rfl
    intro e he
    obtain ⟨c, hc, he⟩ := mem_iUnion.mp he |>.imp fun _ h => mem_iUnion.mp h
    apply hF (show c.val ≤ k.val - 1 from by change c.val < k.val at hc; omega) he
  · apply (M.closure_subset_closure ?_).trans_eq (M.closure_closure _)
    apply union_subset
    · intro e he
      by_cases hlo : a - 2 ≤ k.val - 1
      · let c : IntWindow a := ⟨k.val - 1, ⟨hlo, by have := k.property.2; omega⟩⟩
        apply M.subset_closure _ (by simp [hE])
        left
        refine mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨?_, he⟩⟩
        change k.val - 1 < k.val
        omega
      · have hearly : k.val - 1 < a := by omega
        rw [hFe _ hearly] at he
        exact M.closure_subset_closure (empty_subset _) he
    · exact (subset_union_right.trans (M.subset_closure _ (by simp [hE])))

end Pivots
end MatroidProphet

end OAI
