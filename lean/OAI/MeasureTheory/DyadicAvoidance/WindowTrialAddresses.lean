import OAI.MeasureTheory.DyadicAvoidance.WindowTableModel
import OAI.MeasureTheory.DyadicAvoidance.TrialAddresses

namespace OAI

noncomputable section

namespace Problem310.WindowTrialAddresses

open FiniteTableModel TrialAddresses

variable {M d g r₀ : ℕ}

abbrev LocalTrial (W : WindowData (M + 1) d g r₀) (P : Node M d) :=
  WindowTrial M (W.r (d - P.val.length))

def localStarts (W : WindowData (M + 1) d g r₀) (P : Node M d) (i : Fin M) : ℕ :=
  W.a (selectorEdge P i)

def localIndex (W : WindowData (M + 1) d g r₀) (P : Node M d)
    (z : LocalTrial W P) : ℕ := windowTrialIndex (localStarts W P) z

@[simp] theorem card_localTrial (W : WindowData (M + 1) d g r₀) (P : Node M d) :
    Fintype.card (LocalTrial W P) = M * W.r (d - P.val.length) := by
  simp [LocalTrial]

theorem localIndex_bounds (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (z : LocalTrial W P) :
    3 ≤ localIndex W P z ∧ localIndex W P z ≤ selectorEndpoints W P z.1 := by
  have hs := W.start_three (selectorEdge P z.1) (selectorEdge_valid P z.1)
  have he := selector_window_endpoint W P z.1
  have hk := z.2.isLt
  dsimp [localIndex, windowTrialIndex, localStarts]
  omega

/-- The actual finite-model selector coordinate read at one child-window trial. -/
def localSelectorAddress (W : WindowData (M + 1) d g r₀) (P : Node M d)
    (x t : ℝ) (z : LocalTrial W P) : SelectorAddress (selectorEndpoints W) :=
  selectorAddress (selectorEndpoints W) P z.1
    (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))

theorem localSelectorAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (localSelectorAddress W P x t) := by
  change Function.Injective (trialAddress
    (fun e : Node M d × Fin M => selectorEndpoints W e.1 e.2)
    (fun z : LocalTrial W P => (P, z.1)) (localIndex W P) x t)
  apply trialAddress_injective _ _ _ _ _ ht.1 ht.2
  · exact fun z => (localIndex_bounds W P z).1
  · exact fun z => (localIndex_bounds W P z).2
  · exact windowTrial_pair_injective (localStarts W P) (fun i => (P, i))
      (fun _ _ h => congrArg Prod.snd h)

theorem localSelectorAddress_ne_center (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (z : LocalTrial W P) (e : Node M d × Fin M) :
    localSelectorAddress W P x t z ≠
      selectorAddress (selectorEndpoints W) e.1 e.2 x := by
  exact trialAddress_ne_center
    (fun e : Node M d × Fin M => selectorEndpoints W e.1 e.2)
    (fun z : LocalTrial W P => (P, z.1)) (localIndex W P) x t ht.1 ht.2
    (fun z => (localIndex_bounds W P z).1)
    (fun z => (localIndex_bounds W P z).2) z e

/-- This is the single address-injectivity assumption needed by center
exposure: every center coordinate and every local trial coordinate are fresh. -/
theorem center_local_sum_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Function.Injective (Sum.elim
      (fun e : Node M d × Fin M => selectorAddress (selectorEndpoints W) e.1 e.2 x)
      (localSelectorAddress W P x t)) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (center_selectorAddress_injective (selectorEndpoints W) x h)
    | inr j =>
      exact False.elim ((localSelectorAddress_ne_center W P x t ht j i) h.symm)
  | inr i =>
    cases j with
    | inl j =>
      exact False.elim ((localSelectorAddress_ne_center W P x t ht i j) h)
    | inr j =>
      exact congrArg Sum.inr (localSelectorAddress_injective W P x t ht h)

/-- Once local routing stays in its chosen child subtree, all terminal
coordinates are distinct. WindowData automatically supplies the necessary
resolution refinement, so no numerical hypothesis remains. -/
theorem localTerminalAddress_injective (W : WindowData (M + 1) d g r₀)
    (P : Node M d) (x t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (leaf : LocalTrial W P → Leaf M d)
    (hprefix : ∀ z, (selectorEdge P z.1).IsPrefix (leaf z).val) :
    Function.Injective (fun z : LocalTrial W P =>
      terminalAddress (terminalEndpoints W) (leaf z)
        (x + t * ((2 : ℝ)⁻¹ ^ localIndex W P z))) := by
  change Function.Injective (trialAddress (terminalEndpoints W) leaf (localIndex W P) x t)
  apply TrialAddresses.terminalAddress_injective
    (fun z : LocalTrial W P => z.1) (localIndex W P) leaf
    (selectorEndpoints W P) (terminalEndpoints W) x t ht.1 ht.2
  · exact fun z => (localIndex_bounds W P z).1
  · exact fun z => (localIndex_bounds W P z).2
  · exact fun z => incoming_le_terminalEndpoints W P z.1 (leaf z) (hprefix z)
  · intro i j hij
    have hpath : (leaf i).val = (leaf j).val := congrArg Subtype.val hij
    obtain ⟨si, hsi⟩ := hprefix i
    obtain ⟨sj, hsj⟩ := hprefix j
    have heq : P.val ++ (i.1.castSucc :: si) = P.val ++ (j.1.castSucc :: sj) := by
      simpa only [selectorEdge, List.append_assoc, List.singleton_append] using
        hsi.trans (hpath.trans hsj.symm)
    have hchild := (List.cons.inj (List.append_cancel_left heq)).1
    exact Fin.ext (congrArg (fun v : Fin (M + 1) => v.val) hchild)
  · exact windowTrial_pair_injective (localStarts W P) id (fun _ _ h => h)

end Problem310.WindowTrialAddresses

end

end OAI
