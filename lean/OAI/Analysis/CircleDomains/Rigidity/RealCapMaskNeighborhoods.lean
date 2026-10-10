import OAI.Analysis.CircleDomains.Rigidity.LocalMaskNeighborhoods
import OAI.Analysis.CircleDomains.Transfer.GridCoordinateFilling

namespace OAI

/-! Convert the subordinate physical cap certificates into the open
real-plane mask/branch neighborhoods consumed by finite transfer. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem closure_realJordanInterior (H : ℂ ≃ₜ ℂ) :
    closure (realJordanInterior H) = Complex.equivRealProdCLM '' closure (jordanInterior H) :=
  (Complex.equivRealProdCLM.toHomeomorph.image_closure _).symm

 theorem exists_real_cap_mask_neighborhoods
    {I : Type*} {n : ℕ} (H : I → ℂ ≃ₜ ℂ)
    (q : ℂ → Sphere) (hq : Continuous q)
    (L : Fin n → Type*) (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l a, IsOpen (P l a))
    (hcap : ∀ i l, Disjoint (closure (jordanInterior (H i))) (q ⁻¹' M l) ∨
      ∃ a, closure (jordanInterior (H i)) ⊆ q ⁻¹' (interior (M l) ∩ P l a)) :
    ∃ N : I → Set (ℝ × ℝ),
      (∀ i, IsOpen (N i) ∧ frontier (realJordanInterior (H i)) ⊆ N i) ∧
      ∀ i l, Disjoint (N i) ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∨
        ∃ a, N i ⊆ interior ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∩
          ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' P l a) := by
  have hqr : Continuous (q ∘ Complex.equivRealProdCLM.symm) :=
    hq.comp Complex.equivRealProdCLM.symm.continuous
  have hlocal (i : I) : ∃ N : Set (ℝ × ℝ), IsOpen N ∧
      closure (realJordanInterior (H i)) ⊆ N ∧
      ∀ l, Disjoint N ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∨
        ∃ a, N ⊆ interior ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' M l) ∩
          ((q ∘ Complex.equivRealProdCLM.symm) ⁻¹' P l a) := by
    apply exists_common_mask_branch_neighborhood_of_subset L _ _
      (fun l => (hM l).preimage hqr) _ (fun l a => (hP l a).preimage hqr)
    intro l
    rcases hcap i l with hd | ⟨a, ha⟩
    · left
      apply Set.disjoint_left.mpr
      intro p hp hm
      rw [closure_realJordanInterior] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      exact Set.disjoint_left.mp hd hz (by simpa only [mem_preimage, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply] using hm)
    · right
      refine ⟨a, ?_⟩
      intro p hp
      rw [closure_realJordanInterior] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      have hm := ha hz
      refine ⟨preimage_interior_subset_interior_preimage hqr ?_, ?_⟩
      · simpa only [mem_preimage, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hm.1
      · simpa only [mem_preimage, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hm.2
  choose N hN hCN hchoice using hlocal
  exact ⟨N, fun i => ⟨hN i, frontier_subset_closure.trans (hCN i)⟩, hchoice⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
