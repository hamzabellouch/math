import OAI.GroupTheory.FiniteIndex.Characteristic

namespace OAI

/-! Finite generation of a group extension with finitely generated kernel and quotient. -/

namespace FiniteIndexRealization
lemma fg_of_surjective_with_fg_kernel {G A : Type*} [Group G] [Group A]
    [Group.FG A] (f : G →* A) (hf : Function.Surjective f) [Group.FG f.ker] :
    Group.FG G := by
  classical
  obtain ⟨S, hS, hSf⟩ := Group.fg_iff.mp (inferInstance : Group.FG f.ker)
  obtain ⟨T, hT, hTf⟩ := Group.fg_iff.mp (inferInstance : Group.FG A)
  choose lift hlift using hf
  let U : Set G := (Subtype.val '' S) ∪ (lift '' T)
  let H : Subgroup G := Subgroup.closure U
  have hker : f.ker ≤ H := by
    have h : Subgroup.closure S ≤ H.comap f.ker.subtype :=
      (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
    rw [hS] at h
    intro x hx
    exact h (show (⟨x, hx⟩ : f.ker) ∈ (⊤ : Subgroup f.ker) from trivial)
  have hmap : H.map f = ⊤ := by
    apply top_unique
    rw [← hT]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    exact ⟨lift a, Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩), hlift a⟩
  have htop : H = ⊤ := by
    apply top_unique
    intro x _
    have hx : f x ∈ H.map f := by rw [hmap]; trivial
    obtain ⟨y, hy, hxy⟩ := hx
    have hdiff : x * y⁻¹ ∈ f.ker := by
      change f (x * y⁻¹) = 1
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have := H.mul_mem (hker hdiff) hy
    simpa only [inv_mul_cancel_right] using this
  exact Group.fg_iff.mpr ⟨U, htop, (hSf.image _).union (hTf.image _)⟩
end FiniteIndexRealization

end OAI
