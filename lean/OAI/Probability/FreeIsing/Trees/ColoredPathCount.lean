import OAI.Probability.FreeIsing.Trees.ColoredPathAverage
import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

namespace Problem367.ColoredPathAverage

def pathReducedTailEquiv {d : ℕ} (n : ℕ) (i : Fin d) :
    Path d n i ≃ ReducedTail i n := by
  induction n generalizing i with
  | zero =>
    change PUnit ≃ ReducedTail i 0
    exact (Equiv.ofUnique PUnit Unit).trans (reducedTailZeroEquiv i).symm
  | succ n ih =>
    refine Equiv.trans ?_ (reducedTailSuccEquiv i n).symm
    exact {
      toFun := fun p => ⟨⟨p.1.1, Ne.symm p.1.2⟩, ih p.1.1 p.2⟩
      invFun := fun p => ⟨⟨p.1.1, Ne.symm p.1.2⟩, (ih p.1.1).symm p.2⟩
      left_inv := by
        rintro ⟨⟨color, hcolor⟩, path⟩
        simp only [Equiv.symm_apply_apply]
        rfl
      right_inv := by rintro ⟨⟨j, hj⟩, p⟩; simp }

@[simp] theorem card_path {d : ℕ} (n : ℕ) (i : Fin d) :
    Fintype.card (Path d n i) = (d - 1) ^ n := by
  rw [Fintype.card_congr (pathReducedTailEquiv n i), card_reducedTail]

@[simp] theorem colors_eq_cons_pathReducedTailEquiv {d n : ℕ} {i : Fin d}
    (p : Path d n i) :
    colors p = i :: (pathReducedTailEquiv n i p).1 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨⟨j, hj⟩, p⟩
    change i :: colors p = i :: j :: (pathReducedTailEquiv n j p).1
    exact congrArg (List.cons i) (ih p)

theorem colors_injective {d n : ℕ} (i : Fin d) :
    Function.Injective (colors (d := d) (n := n) (i := i)) := by
  intro p q hpq
  apply (pathReducedTailEquiv n i).injective
  apply Subtype.ext
  simpa only [colors_eq_cons_pathReducedTailEquiv, List.cons.injEq, true_and] using hpq

theorem exists_path_colors {d n : ℕ} (i : Fin d) (w : List (Fin d))
    (hlen : w.length = n + 1) (hhead : w.head? = some i)
    (hchain : List.IsChain (fun a b : Fin d => a ≠ b) w) :
    ∃ p : Path d n i, colors p = w := by
  cases w with
  | nil => simp at hlen
  | cons j w =>
    have hji : j = i := by simpa using hhead
    subst j
    let q : ReducedTail i n := ⟨w, by simpa using hlen, hchain⟩
    refine ⟨(pathReducedTailEquiv n i).symm q, ?_⟩
    simp [q]

end Problem367.ColoredPathAverage

end

end OAI
