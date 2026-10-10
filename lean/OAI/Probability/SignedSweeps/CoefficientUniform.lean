import OAI.Probability.SignedSweeps.BlockRestriction

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]

lemma coefficientPush_comp (φ : G →* H) (ψ : H →* K) (f : G → ℂ) :
    coefficientPush ψ (coefficientPush φ f) = coefficientPush (ψ.comp φ) f := by
  apply coefficientAction_injective (G:=K)
  simp only [coefficientAction_push]
  rfl

omit [Fintype H] in
lemma coefficientPush_equiv [Fintype H] (e : G ≃* H) (f : G → ℂ) (h : H) :
    coefficientPush e.toMonoidHom f h = f (e.symm h) := by
  calc
    _ = coefficientPush e.toMonoidHom f (e.toMonoidHom (e.symm h)) := congrArg (coefficientPush e.toMonoidHom f) (e.apply_symm_apply h).symm
    _ = _ := coefficientPush_apply _ e.injective _ _

def subgroupAverageCoefficient (S : Subgroup G) : G → ℂ :=
  coefficientPush S.subtype (fun _ => (Fintype.card S : ℂ)⁻¹)

lemma subgroupAverageCoefficient_equiv (S : Subgroup G) (e : H ≃* S) :
    subgroupAverageCoefficient S =
      coefficientPush (S.subtype.comp e.toMonoidHom) (fun _ => (Fintype.card H : ℂ)⁻¹) := by
  unfold subgroupAverageCoefficient
  rw [← coefficientPush_comp]
  congr 1
  funext s
  rw [coefficientPush_equiv, Fintype.card_congr e.toEquiv]

lemma subgroupAverageCoefficient_image (S : Subgroup H) (φ : G →* H)
    (hi : Function.Injective φ) (he : ∀ h, h ∈ S ↔ ∃ g, φ g = h) :
    subgroupAverageCoefficient S = coefficientPush φ (fun _ => (Fintype.card G : ℂ)⁻¹) := by
  let ψ : G →* S := φ.codRestrict S (fun g => (he (φ g)).mpr ⟨g,rfl⟩)
  have hψ : Function.Bijective ψ := ⟨fun a b h => hi (congrArg Subtype.val h), by
    intro h
    obtain ⟨g,hg⟩ := (he h).mp h.2
    exact ⟨g,Subtype.ext hg⟩⟩
  have hh := subgroupAverageCoefficient_equiv S (MulEquiv.ofBijective ψ hψ)
  exact hh

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_subgroupAverage [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (S : Subgroup G) :
    coefficientAction ρ (subgroupAverageCoefficient S) =
      (Fintype.card S : ℂ)⁻¹ • ∑ g : S, ρ g := by
  rw [subgroupAverageCoefficient, coefficientAction_push]
  simp only [coefficientAction, Finset.smul_sum, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

lemma subgroupAverageCoefficient_support (S : Subgroup G) (g : G) (hg : g ∉ S) :
    subgroupAverageCoefficient S g = 0 := by
  exact coefficientPush_zero S.subtype _ g (by rintro ⟨h,rfl⟩; exact hg h.2)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G H : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)] [∀ j, Group (H j)] [∀ j, Fintype (H j)]

def piHom (φ : ∀ j, G j →* H j) : (∀ j, G j) →* (∀ j, H j) where
  toFun := fun g j => φ j (g j)
  map_one' := funext (fun j => map_one (φ j))
  map_mul' a b := funext (fun j => map_mul (φ j) (a j) (b j))

omit [Fintype J] [∀ index, Fintype (G index)] [∀ index, Fintype (H index)] in
lemma piHom_injective [Fintype J] [∀ index, Fintype (G index)]
    [∀ index, Fintype (H index)]
    (φ : ∀ j, G j →* H j) (hφ : ∀ j, Function.Injective (φ j)) :
    Function.Injective (piHom φ) := by
  intro g h he
  exact funext (fun j => hφ j (congrFun he j))

omit [∀ index, Fintype (H index)] in
lemma productCoefficient_push [∀ index, Fintype (H index)]
    (φ : ∀ j, G j →* H j) (f : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientPush (φ j) (f j)) =
      coefficientPush (piHom φ) (productCoefficient f) := by
  funext h
  simp only [productCoefficient, coefficientPush, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases he : piHom φ g = h
  · rw [ite_eq_left he]
    apply Finset.prod_congr rfl
    intro j _
    exact ite_eq_left (congrFun he j)
  · rw [ite_eq_right he]
    have hn : ∃ j, φ j (g j) ≠ h j := by
      by_contra hn
      push Not at hn
      exact he (funext hn)
    obtain ⟨j,hj⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma product_subgroupAverage (S : ∀ j, Subgroup (G j)) :
    productCoefficient (fun j => subgroupAverageCoefficient (S j)) =
      coefficientPush (piHom (fun j => (S j).subtype))
        (fun _ => (Fintype.card (∀ j, S j) : ℂ)⁻¹) := by
  rw [show (fun j => subgroupAverageCoefficient (S j)) =
    (fun j => coefficientPush (S j).subtype (fun _ => (Fintype.card (S j) : ℂ)⁻¹)) from rfl,
    productCoefficient_push]
  congr 1
  funext g
  simp only [productCoefficient, ← Finset.prod_inv_distrib, Fintype.card_pi, Nat.cast_prod]

end SignedSweeps
end

end OAI
