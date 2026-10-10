import OAI.GroupTheory.Kervaire.RelatorRigidity

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
lemma planar_vertex_join (σ θ : Perm D) {x y : D} (hxy : ¬ components σ θ x y)
    (hp : planar σ θ) : planar (swap x y * σ) θ := by
  have hσ : ¬ σ.SameCycle x y := fun h ↦ hxy ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) h)
  have hφ : ¬ (σ*θ).SameCycle x y := fun h ↦ hxy (cycles_mul_le σ θ (components σ θ) le_sup_left le_sup_right h)
  have hv := numCycles_swap_merge σ hσ
  have hf := numCycles_swap_merge (σ*θ) hφ
  have hc : components (swap x y*σ) θ x y :=
    (le_sup_left : SameCycle.setoid (swap x y*σ) ≤ components (swap x y*σ) θ) (sameCycle_swap_merges σ hσ)
  have hr := components_swap_sup σ θ x y
  rw [joinPair_eq _ hc] at hr
  have hcr := classes_joinPair (components σ θ) hxy
  unfold planar at hp ⊢
  rw [hr,mul_assoc]
  omega

omit [DecidableEq D] [DecidableEq E] in
lemma card_quotient_ker {B : Type*} [Fintype B] (f : D → B) (hf : Function.Surjective f) :
    classes (Setoid.ker f) = Fintype.card B := by
  let e : Quotient (Setoid.ker f) ≃ B := Equiv.ofBijective
    (Quotient.lift f (fun _ _ h ↦ h)) (by
      constructor
      · intro x y
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y =>
            exact fun h ↦ Quotient.sound h
      · intro b; obtain ⟨d,rfl⟩ := hf b; exact ⟨Quotient.mk _ d,rfl⟩)
  exact Fintype.card_congr e

omit [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma sumPerm_zpow (σ : Perm D) (τ : Perm E) (n : ℤ) :
    (σ.sumCongr τ)^n = (σ^n).sumCongr (τ^n) := by
  exact (map_zpow (sumCongrHom D E) (σ,τ) n).symm

omit [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma sameCycle_sumPerm (σ : Perm D) (τ : Perm E) (x y : D ⊕ E) :
    (σ.sumCongr τ).SameCycle x y ↔
      Sum.map (Quotient.mk (SameCycle.setoid σ)) (Quotient.mk (SameCycle.setoid τ)) x =
      Sum.map (Quotient.mk (SameCycle.setoid σ)) (Quotient.mk (SameCycle.setoid τ)) y := by
  cases x <;> cases y <;>
    simp only [SameCycle,sumPerm_zpow,Equiv.Perm.sumCongr_apply,Sum.map_inl,Sum.map_inr,
      Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,exists_const]
  · exact ⟨fun h ↦ Quotient.sound (s := SameCycle.setoid σ) h,fun h ↦ Quotient.exact h⟩
  · exact ⟨fun h ↦ Quotient.sound (s := SameCycle.setoid τ) h,fun h ↦ Quotient.exact h⟩

omit [DecidableEq D] [DecidableEq E] in
lemma numCycles_sumPerm (σ : Perm D) (τ : Perm E) :
    numCycles (σ.sumCongr τ) = numCycles σ + numCycles τ := by
  let f : D ⊕ E → Cycles σ ⊕ Cycles τ := Sum.map (Quotient.mk _) (Quotient.mk _)
  have hf : Function.Surjective f := by
    rintro (x|y)
    · exact ⟨Sum.inl x.out,congrArg Sum.inl x.out_eq⟩
    · exact ⟨Sum.inr y.out,congrArg Sum.inr y.out_eq⟩
  rw [numCycles_eq_card (σ.sumCongr τ) f hf (sameCycle_sumPerm σ τ),Fintype.card_sum]
  rfl

lemma components_sumPerm (σ θ : Perm D) (τ η : Perm E) :
    components (σ.sumCongr τ) (θ.sumCongr η) =
      Setoid.ker (Sum.map (Quotient.mk (components σ θ)) (Quotient.mk (components τ η))) := by
  let f := Sum.map (Quotient.mk (components σ θ)) (Quotient.mk (components τ η))
  apply le_antisymm
  · apply sup_le
    · apply cycle_le_of_step
      intro d
      cases d with
      | inl d => exact congrArg Sum.inl (Quotient.sound ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) SameCycle.rfl.apply_left))
      | inr d => exact congrArg Sum.inr (Quotient.sound ((le_sup_left : SameCycle.setoid τ ≤ components τ η) SameCycle.rfl.apply_left))
    · apply cycle_le_of_step
      intro d
      cases d with
      | inl d => exact congrArg Sum.inl (Quotient.sound ((le_sup_right : SameCycle.setoid θ ≤ components σ θ) SameCycle.rfl.apply_left))
      | inr d => exact congrArg Sum.inr (Quotient.sound ((le_sup_right : SameCycle.setoid η ≤ components τ η) SameCycle.rfl.apply_left))
  · intro x y h
    change f x = f y at h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact components_map Sum.inl σ θ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) (Quotient.exact (Sum.inl.inj h))
      | inr y => simp only [f,Sum.map_inl,Sum.map_inr,Sum.inl_ne_inr] at h
    | inr x =>
      cases y with
      | inl y => simp only [f,Sum.map_inl,Sum.map_inr,Sum.inr_ne_inl] at h
      | inr y =>
        exact components_map Sum.inr τ η _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) (Quotient.exact (Sum.inr.inj h))

lemma planar_sumPerm (σ θ : Perm D) (τ η : Perm E) (h₁ : planar σ θ) (h₂ : planar τ η) :
    planar (σ.sumCongr τ) (θ.sumCongr η) := by
  have hf : Function.Surjective (Sum.map (Quotient.mk (components σ θ)) (Quotient.mk (components τ η))) := by
    rintro (x|y)
    · exact ⟨Sum.inl x.out,congrArg Sum.inl x.out_eq⟩
    · exact ⟨Sum.inr y.out,congrArg Sum.inr y.out_eq⟩
  unfold planar at h₁ h₂ ⊢
  rw [components_sumPerm,card_quotient_ker _ hf,Fintype.card_sum]
  have he : (σ.sumCongr τ)*(θ.sumCongr η) = (σ*θ).sumCongr (τ*η) := by
    exact (map_mul (sumCongrHom D E) (σ,τ) (θ,η)).symm
  rw [he,numCycles_sumPerm,numCycles_sumPerm,numCycles_sumPerm,Fintype.card_sum]
  change _ = _ + 2*(classes (components σ θ)+classes (components τ η))
  omega

omit [Fintype E] [DecidableEq E] [DecidableEq D] in
lemma planar_one_right (σ : Perm D) : planar σ 1 := by
  have ho : SameCycle.setoid (1 : Perm D) = ⊥ := by ext x y; exact sameCycle_one
  unfold planar components
  rw [ho,sup_bot_eq,mul_one,numCycles_one]
  change numCycles σ + Fintype.card D + numCycles σ = Fintype.card D + 2*numCycles σ
  omega
end KervaireRibbon

end
end

end OAI
