import OAI.Probability.FreeIsing.Model

namespace OAI

noncomputable section
namespace Problem367

def treeStep {d : ℕ} (v : TreeVertex d) (c : Fin d) : TreeVertex d :=
  if h : v.1.getLast? = some c then
    ⟨v.1.dropLast, v.2.dropLast⟩
  else
    ⟨v.1 ++ [c], by
      apply List.isChain_append.mpr
      refine ⟨v.2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.head?_cons, Option.mem_some_iff] at hb
      subst b
      intro hac
      subst a
      exact h ha⟩

theorem treeStep_adj {d : ℕ} (v : TreeVertex d) (c : Fin d) :
    treeAdj v (treeStep v c) := by
  unfold treeStep
  split_ifs with h
  · right
    refine ⟨c, ?_⟩
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp h
    simp [hl]
  · exact Or.inl ⟨c, rfl⟩

theorem treeStep_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (treeStep v) := by
  intro c c' heq
  by_cases hc : v.1.getLast? = some c
  · by_cases hc' : v.1.getLast? = some c'
    · exact Option.some.inj (hc.symm.trans hc')
    · have hh := congrArg (fun w : TreeVertex d => w.1.length) heq
      simp only [treeStep, dite_eq_left hc, dite_eq_right hc', List.length_dropLast, List.length_append, List.length_singleton] at hh
      omega
  · by_cases hc' : v.1.getLast? = some c'
    · have hh := congrArg (fun w : TreeVertex d => w.1.length) heq
      simp only [treeStep, dite_eq_right hc, dite_eq_left hc', List.length_dropLast, List.length_append, List.length_singleton] at hh
      omega
    · have hh := congrArg (fun w : TreeVertex d => w.1) heq
      simpa [treeStep, hc, hc'] using hh

theorem treeStep_eq_iff {d : ℕ} (v w : TreeVertex d) (c : Fin d) :
    treeStep v c = w ↔ w.1 = v.1 ++ [c] ∨ v.1 = w.1 ++ [c] := by
  constructor
  · intro h
    by_cases hc : v.1.getLast? = some c
    · right
      obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hc
      have hw := congrArg Subtype.val h
      simp only [treeStep, dite_eq_left hc] at hw
      simpa [hl] using (congrArg (fun x : List (Fin d) => x ++ [c]) hw)
    · left
      have hw := congrArg Subtype.val h
      simpa only [treeStep, dite_eq_right hc] using hw.symm
  · rintro (hc | hc)
    · have hn : v.1.getLast? ≠ some c := by
        intro hlast
        have hchain : List.IsChain (fun a b : Fin d => a ≠ b) (v.1 ++ [c]) := by
          rw [← hc]
          exact w.2
        exact (List.isChain_append.mp hchain).2.2 c hlast c rfl rfl
      apply Subtype.ext
      simp [treeStep, hn, hc]
    · apply Subtype.ext
      simp [treeStep, hc]

theorem treeStep_involutive {d : ℕ} (c : Fin d) :
    Function.Involutive (fun v : TreeVertex d => treeStep v c) := by
  intro v
  apply (treeStep_eq_iff _ _ c).mpr
  exact ((treeStep_eq_iff v (treeStep v c) c).mp rfl).symm

theorem treeAdj_iff_exists_treeStep {d : ℕ} (v w : TreeVertex d) :
    treeAdj v w ↔ ∃ c : Fin d, treeStep v c = w := by
  constructor
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact ⟨c, (treeStep_eq_iff v w c).mpr (Or.inl hc)⟩
    · exact ⟨c, (treeStep_eq_iff v w c).mpr (Or.inr hc)⟩
  · rintro ⟨c, rfl⟩
    exact treeStep_adj v c

noncomputable def treeNeighborEquiv {d : ℕ} (v : TreeVertex d) :
    Fin d ≃ {w : TreeVertex d // treeAdj v w} :=
  Equiv.ofBijective (fun c => ⟨treeStep v c, treeStep_adj v c⟩) (by
    constructor
    · intro a b h
      exact treeStep_injective v (congrArg Subtype.val h)
    · intro w
      obtain ⟨c, hc⟩ := (treeAdj_iff_exists_treeStep v w.1).mp w.2
      exact ⟨c, Subtype.ext hc⟩)

instance treeNeighborsFinite {d : ℕ} (v : TreeVertex d) :
    Finite {w : TreeVertex d // treeAdj v w} :=
  Finite.of_equiv (Fin d) (treeNeighborEquiv v)

theorem card_treeNeighbors {d : ℕ} (v : TreeVertex d) :
    Nat.card {w : TreeVertex d // treeAdj v w} = d := by
  rw [← Nat.card_congr (treeNeighborEquiv v)]
  simp

def treeNeighborFinset {d : ℕ} (v : TreeVertex d) : Finset (TreeVertex d) := by
  classical
  exact Finset.univ.image (treeStep v)

@[simp] theorem mem_treeNeighborFinset {d : ℕ} (v w : TreeVertex d) :
    w ∈ treeNeighborFinset v ↔ treeAdj v w := by
  classical
  simp [treeNeighborFinset, treeAdj_iff_exists_treeStep]

@[simp] theorem card_treeNeighborFinset {d : ℕ} (v : TreeVertex d) :
    (treeNeighborFinset v).card = d := by
  classical
  rw [treeNeighborFinset, Finset.card_image_of_injective _ (treeStep_injective v)]
  simp

theorem treeStep_length {d : ℕ} (v : TreeVertex d) (c : Fin d) :
    (treeStep v c).1.length =
      if v.1.getLast? = some c then v.1.length - 1 else v.1.length + 1 := by
  unfold treeStep
  split_ifs <;> simp

theorem sum_treeNeighborFinset_radial {d : ℕ} (v : TreeVertex d) (F : ℕ → ℝ) :
    ∑ w ∈ treeNeighborFinset v, F w.1.length =
      if v.1.length = 0 then (d : ℝ) * F 1
      else F (v.1.length - 1) + ((d : ℝ) - 1) * F (v.1.length + 1) := by
  classical
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn]
  by_cases hv : v.1.length = 0
  · have hnil := List.length_eq_zero_iff.mp hv
    simp [treeStep_length, hnil]
  · have hne : v.1 ≠ [] := by
      intro hnil
      exact hv (List.length_eq_zero_iff.mpr hnil)
    let c := v.1.getLast hne
    have hc : v.1.getLast? = some c := List.getLast?_eq_some_getLast hne
    have hd : 1 ≤ d := by have := c.isLt; omega
    rw [ite_eq_right hv, ← Finset.add_sum_erase Finset.univ
      (fun a : Fin d => F (treeStep v a).1.length) (Finset.mem_univ c)]
    simp only [treeStep_length, hc, Option.some.injEq]
    congr 1
    calc
      ∑ a ∈ Finset.univ.erase c,
          F (if c = a then v.1.length - 1 else v.1.length + 1) =
          ∑ _a ∈ Finset.univ.erase c, F (v.1.length + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [ite_eq_right (Ne.symm (Finset.mem_erase.mp ha).1)]
      _ = ((d : ℝ) - 1) * F (v.1.length + 1) := by
        simp [Nat.cast_sub hd]

end Problem367

end

end OAI
