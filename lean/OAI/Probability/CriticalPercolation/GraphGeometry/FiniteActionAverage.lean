import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
universe u v
variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

lemma sum_smul_orbit (g : G) (x : X) (hf : (MulAction.orbit G x).Finite) (f : X → ℝ) :
    (∑ y∈hf.toFinset, f (g • y))=∑ y∈hf.toFinset, f y := by
  apply Finset.sum_bij (fun y _ => g • y)
  · intro y hy
    apply hf.mem_toFinset.mpr
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    exact ⟨g*a,mul_smul g a x⟩
  · intro a _ b _ h
    exact MulAction.injective g h
  · intro y hy
    refine ⟨g⁻¹ • y,hf.mem_toFinset.mpr ?_,smul_inv_smul g y⟩
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    exact ⟨g⁻¹*a,mul_smul g⁻¹ a x⟩
  · intros; rfl

lemma finite_group_orbit_average [Fintype G] (x : X) (f : X → ℝ) :
    (MulAction.orbit G x).ncard * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℝ) * ∑ y∈(Set.finite_range (fun g : G => g • x)).toFinset, f y := by
  have hf : (MulAction.orbit G x).Finite := Set.finite_range (fun g : G => g • x)
  have hinv (y : X) (hy : y∈hf.toFinset) :
      (∑ g : G, f (g • y))=∑ g : G, f (g • x) := by
    obtain ⟨a,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    simp only [←mul_smul]
    exact Equiv.sum_comp (Equiv.mulRight a) (fun g : G => f (g • x))
  calc
    _ = ∑ y∈hf.toFinset, ∑ g : G, f (g • y) := by
      rw [Finset.sum_congr rfl hinv]
      simp only [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hf]
    _ = ∑ g : G, ∑ y∈hf.toFinset, f (g • y) := Finset.sum_comm
    _ = _ := by
      simp only [sum_smul_orbit,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rfl

def restrictedPermutation (B : Set X) (hB : ∀ g : G, ∀ x∈B, g • x∈B) (g : G) : Equiv.Perm B where
  toFun x := ⟨g • x.val,hB g x.val x.property⟩
  invFun x := ⟨g⁻¹ • x.val,hB g⁻¹ x.val x.property⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

def restrictionHom (B : Set X) (hB : ∀ g : G, ∀ x∈B, g • x∈B) : G →* Equiv.Perm B where
  toFun := restrictedPermutation B hB
  map_one' := by ext x; exact one_smul G x.val
  map_mul' g h := by ext x; exact mul_smul g h x.val

lemma exists_finite_restriction (B : Set X) (hfin : B.Finite)
    (hB : ∀ g : G, ∀ x∈B, g • x∈B) :
    ∃ (H : Type v) (_ : Group H) (_ : Fintype H) (r : H → G),
      (∀ h₁ h₂ x, x∈B → r (h₁*h₂) • x = r h₁ • (r h₂ • x)) ∧
      (∀ g : G, ∃ h : H, ∀ x∈B, r h • x=g • x) := by
  let := hfin.fintype
  let τ := restrictionHom B hB
  let H := τ.range
  let : Fintype H := Fintype.ofFinite H
  let r : H → G := fun h => Classical.choose h.property
  have hr (h : H) : τ (r h)=h.val := Classical.choose_spec h.property
  refine ⟨H,inferInstance,inferInstance,r,?_,?_⟩
  · intro a b x hx
    have he : τ (r (a*b))=τ (r a)*τ (r b) := by rw [hr,hr,hr]; rfl
    exact congrArg (fun e : Equiv.Perm B => (e ⟨x,hx⟩).val) he
  · intro g
    refine ⟨⟨τ g,⟨g,rfl⟩⟩,?_⟩
    intro x hx
    exact congrArg (fun e : Equiv.Perm B => (e ⟨x,hx⟩).val) (hr ⟨τ g,⟨g,rfl⟩⟩)

lemma restricted_orbit_average {H : Type*} [Group H] [Fintype H]
    (B : Set X) (r : H → G)
    (hmul : ∀ a b x, x∈B → r (a*b) • x=r a • (r b • x))
    (hsurj : ∀ g : G, ∃ h : H, ∀ x∈B, r h • x=g • x)
    (x : X) (hx : x∈B) (hf : (MulAction.orbit G x).Finite) (f : X → ℝ) :
    (MulAction.orbit G x).ncard * (∑ h : H, f (r h • x)) =
      (Fintype.card H : ℝ) * ∑ y∈hf.toFinset, f y := by
  have hinv (y : X) (hy : y∈hf.toFinset) :
      (∑ h : H, f (r h • y))=∑ h : H, f (r h • x) := by
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp (hf.mem_toFinset.mp hy)
    obtain ⟨a,ha⟩ := hsurj g
    rw [←ha x hx]
    simp_rw [←hmul _ _ x hx]
    exact Equiv.sum_comp (Equiv.mulRight a) (fun h : H => f (r h • x))
  calc
    _ = ∑ y∈hf.toFinset, ∑ h : H, f (r h • y) := by
      rw [Finset.sum_congr rfl hinv]
      simp only [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hf]
    _ = ∑ h : H, ∑ y∈hf.toFinset, f (r h • y) := Finset.sum_comm
    _ = _ := by
      simp only [sum_smul_orbit,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
