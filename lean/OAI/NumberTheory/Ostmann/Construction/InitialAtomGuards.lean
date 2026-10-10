import OAI.NumberTheory.Ostmann.Construction.ConstituentInitialAmplitude
import OAI.NumberTheory.Ostmann.Characters.NormalizedFourierProfile
import OAI.NumberTheory.Ostmann.Construction.PositiveFourierCutoff

namespace OAI

/-! # Exact prime-unit support and Fourier normalization at depth zero -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem initial_atom_units_iff {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) (v : ℤ) :
    (∀ a : CopyScheduleAtoms role 0, (∏ k, x ⟨a.val, k⟩).Coprime v.natAbs) ↔
      ∀ i, (x i).Coprime v.natAbs := by
  constructor
  · intro h i
    exact Nat.coprime_fintype_prod_left_iff.mp (h ⟨i.1, trivial⟩) i.2
  · intro h a
    exact Nat.coprime_fintype_prod_left_iff.mpr (fun k => h ⟨a.val, k⟩)

theorem initial_atom_pairwise {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ)
    (hx : Pairwise (fun i j => (x i).Coprime (x j))) :
    Pairwise (fun a b : CopyScheduleAtoms role 0 =>
      (∏ k, x ⟨a.val, k⟩).Coprime (∏ k, x ⟨b.val, k⟩)) := by
  intro a b hab
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro k
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro l
  apply hx
  intro he
  exact hab (Subtype.ext (congrArg Sigma.fst he))

theorem fullAtomTransferWeight_initial {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (x : (Σ i, Fin (size i)) → ℕ) (v : ℤ)
    (hx : Pairwise (fun i j => (x i).Coprime (x j)))
    (hrange : ∀ r ∈ ranges 0, r.Holds (fun a => ∏ k, x ⟨a.val, k⟩)) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf 0
      (fun a => ∏ k, x ⟨a.val, k⟩) v =
      if ∀ i, (x i).Coprime v.natAbs then leaf ⟨0, fun a => ∏ k, x ⟨a.val, k⟩⟩ v else 0 := by
  have hpair := initial_atom_pairwise role size x hx
  have hg : fullAtomWeightGuard role childBound pivotBound ranges 0
      (fun a => ∏ k, x ⟨a.val, k⟩) v ↔ ∀ i, (x i).Coprime v.natAbs := by
    constructor
    · intro hg
      exact (initial_atom_units_iff role size x v).mp
        ((totalAtomUnitRanges_iff role 0 _ v).mp hg.2.1)
    · intro hu
      exact ⟨hpair, (totalAtomUnitRanges_iff role 0 _ v).mpr
        ((initial_atom_units_iff role size x v).mpr hu), hrange⟩
  simp only [fullAtomTransferWeight, hg, recursiveTransferWeight]

theorem initial_atom_total {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) :
    scheduleAtomTotal role ⟨0, fun a => ∏ k, x ⟨a.val, k⟩⟩ = ∏ i, x i := by
  unfold scheduleAtomTotal
  trans ∏ i : I, ∏ k : Fin (size i), x ⟨i, k⟩
  · exact ((initialSurvivorEquiv role).prod_comp
      (fun a : CopyScheduleAtoms role 0 => ∏ k, x ⟨a.val, k⟩)).symm
  · exact (Fintype.prod_sigma (fun i => x i)).symm

/-- The chosen even cutoff makes the negative recursive Fourier convention
identical to the original positive-frequency Poisson convention. -/
theorem normalizedFourierProfile_even_original (ψ : ℝ → ℂ)
    (heven : ∀ t, ψ (-t) = ψ t) (X M v : ℝ) (hX : X ≠ 0) (hM : M ≠ 0) :
    normalizedFourierProfile ψ v (M / X) =
      (Real.sqrt (X / M) : ℂ) * ψ (v * X / M) := by
  rw [normalizedFourierProfile_original ψ X M v hX hM]
  unfold archimedeanLeafFactor
  rw [mul_one, show -v * X / M = -(v * X / M) by ring, heven]

end Ostmann

end OAI
