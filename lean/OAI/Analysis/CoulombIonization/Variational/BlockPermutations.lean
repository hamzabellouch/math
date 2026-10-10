import Mathlib
import OAI.Analysis.CoulombIonization.Variational.TensorLp

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

def blockPermHom (N M : ℕ) :
    Equiv.Perm (Fin N) × Equiv.Perm (Fin M) →* Equiv.Perm (Fin (N+M)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin N) (Fin M))

def blockPerm {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    Equiv.Perm (Fin (N+M)) := blockPermHom N M (π,ρ)

def blockSubgroup (N M : ℕ) : Subgroup (Equiv.Perm (Fin (N+M))) :=
  (blockPermHom N M).range

lemma blockSubgroup_mem {N M : ℕ} {κ : Equiv.Perm (Fin (N+M))} :
    κ ∈ blockSubgroup N M ↔ ∃ π ρ, blockPerm π ρ = κ := by
  simp only [blockSubgroup, MonoidHom.mem_range, Prod.exists, blockPerm]

lemma blockPerm_apply_left {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M))
    (i : Fin N) : blockPerm π ρ (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (π i)) := by
  simp [blockPerm,blockPermHom,Equiv.permCongr,Equiv.Perm.sumCongrHom_apply]

lemma blockPerm_apply_right {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M))
    (i : Fin M) : blockPerm π ρ (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr (ρ i)) := by
  simp [blockPerm,blockPermHom,Equiv.permCongr,Equiv.Perm.sumCongrHom_apply]

lemma blockPerm_sign {N M : ℕ} (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    Equiv.Perm.sign (blockPerm π ρ) = Equiv.Perm.sign π * Equiv.Perm.sign ρ := by
  simp [blockPerm,blockPermHom,Equiv.Perm.sign_sumCongr]

lemma blockSubgroup_mem_of_maps_left {N M : ℕ} (κ : Equiv.Perm (Fin (N+M)))
    (h : ∀ i : Fin N, ∃ j : Fin N,
      κ (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl j)) :
    κ ∈ blockSubgroup N M := by
  let σ : Equiv.Perm (Fin N ⊕ Fin M) := finSumFinEquiv.symm.permCongr κ
  have hs : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := h i
    refine ⟨j,?_⟩
    change Sum.inl j = finSumFinEquiv.symm (κ (finSumFinEquiv (Sum.inl i)))
    rw [hj,Equiv.symm_apply_apply]
  obtain ⟨⟨π,ρ⟩,he⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hs
  apply blockSubgroup_mem.mpr
  refine ⟨π,ρ,?_⟩
  apply finSumFinEquiv.symm.permCongr.injective
  calc
    _ = Equiv.Perm.sumCongrHom (Fin N) (Fin M) (π,ρ) := by
      ext i
      simp [blockPerm,blockPermHom,Equiv.permCongr]
    _ = _ := he

lemma leftList_blockPerm {α : Type*} {N M : ℕ} (x : Fin (N+M) → α)
    (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    leftList (x ∘ blockPerm π ρ) = leftList x ∘ π := by
  funext i
  simp only [leftList, Function.comp_apply, blockPerm_apply_left]

lemma rightList_blockPerm {α : Type*} {N M : ℕ} (x : Fin (N+M) → α)
    (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    rightList (x ∘ blockPerm π ρ) = rightList x ∘ ρ := by
  funext i
  simp only [rightList, Function.comp_apply, blockPerm_apply_right]

end CoulombAtom

end

end OAI
