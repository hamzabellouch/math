import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathAccuracy

namespace OAI

/-! The subdivision guarantee for arbitrary valid input tapes, with no
assumption that their bond lists came from a chosen abstract edge enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open MediatorListProgram

theorem bonds_list {n : ℕ} (xs : List Bond) (hb : SourceBondLists.bounded n xs) :
    (List.ofFn fun i => (((SourceBondLists.bonds n xs hb).left i).val,
      ((SourceBondLists.bonds n xs hb).right i).val,
      (SourceBondLists.bonds n xs hb).weight i)) = xs := by
  exact List.ofFn_get xs

theorem input_of_bonds (x : Input) (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2) :
    encodedInput (SourceBondLists.bonds x.1.1 x.2.1 hk).left
      (SourceBondLists.bonds x.1.1 x.2.1 hk).right
      (SourceBondLists.bonds x.1.1 x.2.1 hk).weight
      (fun i => ![(SourceBondLists.bonds x.1.1 x.2.2 hs).left i,
        (SourceBondLists.bonds x.1.1 x.2.2 hs).right i])
      (SourceBondLists.bonds x.1.1 x.2.2 hs).weight x.1.2.1 x.1.2.2.1 x.1.2.2.2 = x := by
  unfold encodedInput
  dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [bonds_list,bonds_list]

theorem energy_error_input (x : Input) (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2)
    (hnk : ∀ e ∈ x.2.1, e.1 ≠ e.2.1) (hns : ∀ e ∈ x.2.2, e.1 ≠ e.2.1)
    (hN : 0 < x.1.2.2.1) :
    |sourceMatrixBottom (count x) (SourceBondLists.matrix (count x) (bonds x)+(constant x:ℂ) • 1)-
      sourceMatrixBottom x.1.1 (SourceBondLists.matrix x.1.1 (x.2.1++x.2.2)+
        (x.1.2.2.2:ℂ) • 1)| ≤ 1/(x.1.2.2.1:ℝ) := by
  let k := SourceBondLists.bonds x.1.1 x.2.1 hk
  let s := SourceBondLists.bonds x.1.1 x.2.2 hs
  have hk' : ∀ i, k.left i ≠ k.right i := SourceBondLists.bonds_noLoops _ _ hk hnk
  have hs' : ∀ i, Function.Injective (![s.left i,s.right i] : Fin 2 → Fin x.1.1) := by
    intro i a b hab
    have hi : s.left i ≠ s.right i := SourceBondLists.bonds_noLoops _ _ hs hns i
    fin_cases a <;> fin_cases b <;> dsimp at hab ⊢
    all_goals simp_all
  have h := energy_error k.left k.right hk' k.weight (fun i => ![s.left i,s.right i]) hs'
    s.weight x.1.2.1 hN x.1.2.2.2
  rw [input_of_bonds x hk hs] at h
  exact h

theorem graph_energy_error (x : Input) (hk : SourceBondLists.bounded x.1.1 x.2.1)
    (hs : SourceBondLists.bounded x.1.1 x.2.2)
    (hnk : ∀ e ∈ x.2.1, e.1 ≠ e.2.1) (hns : ∀ e ∈ x.2.2, e.1 ≠ e.2.1)
    (hN : 0 < x.1.2.2.1) :
    |(graph x hk hs hnk).energy-sourceMatrixBottom x.1.1
      (SourceBondLists.matrix x.1.1 (x.2.1++x.2.2)+(x.1.2.2.2:ℂ) • 1)| ≤ 1/(x.1.2.2.1:ℝ) := by
  rw [graph,QuantumListGraph.ofBonds_energy]
  exact energy_error_input x hk hs hnk hns hN

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
