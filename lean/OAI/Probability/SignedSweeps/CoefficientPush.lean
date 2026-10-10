import OAI.Probability.SignedSweeps.CoefficientAlgebra
import OAI.Probability.SignedSweeps.SignedBlockTrace

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

def coefficientPush (φ : G →* H) (f : G → ℂ) (h : H) : ℂ :=
  ∑ g, if φ g = h then f g else 0

omit [Fintype H] in
lemma coefficientPush_apply (φ : G →* H) (hφ : Function.Injective φ)
    (f : G → ℂ) (g : G) : coefficientPush φ f (φ g) = f g := by
  simp [coefficientPush, hφ.eq_iff]

omit [Fintype H] in
lemma coefficientPush_zero (φ : G →* H) (f : G → ℂ) (h : H)
    (hh : h ∉ Set.range φ) : coefficientPush φ f h = 0 := by
  apply Finset.sum_eq_zero
  intro g _
  exact ite_eq_right (fun he => hh ⟨g,he⟩)

lemma coefficientAction_injective : Function.Injective
    (coefficientAction (finiteRegularRepresentation (G:=G))) := by
  intro f k he
  funext g
  have h := congrArg (fun T : EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G =>
    T (EuclideanSpace.basisFun G ℂ 1) g) he
  simpa only [finiteRegular_coefficient_kernel, inv_one, mul_one] using h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_push (ρ : Representation ℂ H E) (φ : G →* H) (f : G → ℂ) :
    coefficientAction ρ (coefficientPush φ f) = coefficientAction (ρ.comp φ) f := by
  simp only [coefficientAction, coefficientPush, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul, zero_smul]
  simp

lemma coefficientPush_product (φ : G →* H) (f k : G → ℂ) :
    coefficientPush φ (coefficientProduct f k) =
      coefficientProduct (coefficientPush φ f) (coefficientPush φ k) := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_mul]

lemma coefficientPush_one (φ : G →* H) :
    coefficientPush φ (coefficientOne (G:=G)) = coefficientOne := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_one]

omit [Fintype H] in
lemma coefficientPush_star (φ : G →* H) (f : G → ℂ) :
    coefficientPush φ (coefficientStar f) = coefficientStar (coefficientPush φ f) := by
  funext h
  unfold coefficientPush coefficientStar
  rw [star_sum, ← Equiv.sum_comp (Equiv.inv G)]
  simp only [Equiv.inv_apply, inv_inv, map_inv, apply_ite, star_zero, inv_eq_iff_eq_inv]

omit [Fintype H] in
lemma coefficientPush_support (φ : G →* H) (f : G → ℂ) (K : Subgroup H)
    (hK : φ.range ≤ K) : ∀ h, h ∉ K → coefficientPush φ f h = 0 := by
  intro h hh
  exact coefficientPush_zero φ f h (fun ⟨g,hg⟩ => hh (hK ⟨g,hg⟩))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)]

def productCoefficient (f : ∀ j, G j → ℂ) (g : ∀ j, G j) : ℂ := ∏ j, f j (g j)

lemma productCoefficient_product (f k : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientProduct (f j) (k j)) =
      coefficientProduct (productCoefficient f) (productCoefficient k) := by
  funext g
  simp only [productCoefficient, coefficientProduct, Pi.mul_apply, Pi.inv_apply,
    ← Finset.prod_mul_distrib, Fintype.prod_sum]

omit [∀ j, Fintype (G j)] in
lemma productCoefficient_star (f : ∀ j, G j → ℂ) :
    productCoefficient (fun j => coefficientStar (f j)) = coefficientStar (productCoefficient f) := by
  funext g
  simp only [productCoefficient, coefficientStar, Pi.inv_apply, star_prod]

omit [∀ j, Fintype (G j)] in
lemma productCoefficient_one :
    productCoefficient (fun j => coefficientOne (G:=G j)) = coefficientOne := by
  funext g
  by_cases hg : g = 1
  · subst g
    simp [productCoefficient, coefficientOne]
  · have hn : ∃ j, g j ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨j,hj⟩ := hn
    rw [coefficientOne, ite_eq_right hg]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

def coefficientPower (f : G → ℂ) : ℕ → G → ℂ
  | 0 => coefficientOne
  | r+1 => coefficientProduct (coefficientPower f r) f

def coefficientListProduct : List (G → ℂ) → G → ℂ
  | [] => coefficientOne
  | f::fs => coefficientProduct f (coefficientListProduct fs)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_power (ρ : Representation ℂ G E) (f : G → ℂ) (r : ℕ) :
    coefficientAction ρ (coefficientPower f r) = coefficientAction ρ f ^ r := by
  induction r with
  | zero => simp only [coefficientPower, coefficientAction_one, pow_zero]
  | succ r ih => rw [coefficientPower, coefficientAction_mul, ih, pow_succ]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_listProduct (ρ : Representation ℂ G E) (fs : List (G → ℂ)) :
    coefficientAction ρ (coefficientListProduct fs) = (fs.map (coefficientAction ρ)).prod := by
  induction fs with
  | nil => simp only [coefficientListProduct, coefficientAction_one, List.map_nil, List.prod_nil]
  | cons f fs ih => rw [coefficientListProduct, coefficientAction_mul, ih, List.map_cons, List.prod_cons]

lemma coefficientPush_power {H : Type*} [Group H] [Fintype H]
    (φ : G →* H) (f : G → ℂ) (r : ℕ) :
    coefficientPush φ (coefficientPower f r) = coefficientPower (coefficientPush φ f) r := by
  apply coefficientAction_injective (G:=H)
  simp only [coefficientAction_push, coefficientAction_power]

lemma productCoefficient_power {J : Type*} [Fintype J] {H : J → Type*}
    [∀ j, Group (H j)] [∀ j, Fintype (H j)] (f : ∀ j, H j → ℂ) (r : ℕ) :
    productCoefficient (fun j => coefficientPower (f j) r) = coefficientPower (productCoefficient f) r := by
  induction r with
  | zero => exact productCoefficient_one
  | succ r ih => simp only [coefficientPower, productCoefficient_product, ih]

end SignedSweeps
end

end OAI
