import OAI.RepresentationTheory.FoulkesHowe.DiagonalPolarization
import OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear
import OAI.RepresentationTheory.FoulkesHowe.Polarization

namespace OAI

noncomputable section

namespace Problem346

universe u v

/-- Pure powers span each symmetric power, including degree zero. -/
theorem span_purePowers_eq_top (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    Submodule.span ℂ (Set.range (fun x : V => symMonomial b V (fun _ => x))) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm
  · intro f hf
    change f = 0
    apply linearMap_eq_zero_of_symMonomial b V f
    have hz : f.compMultilinearMap (symMonomialMultilinear b V) = 0 := by
      apply symmetric_multilinear_eq_zero_of_diagonal
      · intro σ x
        change f (symMonomial b V (fun i => x (σ i))) = f (symMonomial b V x)
        rw [symMonomial_permute]
      · intro x
        exact (Submodule.mem_dualAnnihilator f).mp hf _
          (Submodule.subset_span ⟨x, rfl⟩)
    intro x
    exact DFunLike.congr_fun hz x
  · exact bot_le

/-- Multilinearity extends vanishing on independent pure powers to vanishing everywhere. -/
theorem multilinear_eq_zero_of_pure_powers (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]
    (T : MultilinearMap ℂ (fun _ : Fin a => SymPow b V) W)
    (hT : ∀ x : Fin a → V, T (fun i => symMonomial b V (fun _ => x i)) = 0) :
    T = 0 := by
  apply MultilinearMap.ext_of_span_eq_top
    (g := fun {_ : Fin a} (x : V) => symMonomial b V (fun _ => x))
    (fun _ => span_purePowers_eq_top b V)
  exact hT

/-- Independent pure powers detect a symmetric multilinear form. -/
theorem symmetricMultilinearForm_eq_zero_of_pure_powers (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V)
    (hT : ∀ x : Fin a → V, T (fun i => symMonomial b V (fun _ => x i)) = 0) :
    T = 0 :=
  multilinear_eq_zero_of_pure_powers a b V T hT

end Problem346

end

end OAI
