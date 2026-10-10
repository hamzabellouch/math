import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersPrimitive

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset Ostmann.ZeroDensity
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
  (K pmax : ℕ) (hmax : 1 ≤ pmax) (hbound : ∀ i, p i ≤ pmax)
local instance (i : ι) : Fintype (DirichletCharacter ℂ (p i)) := Fintype.ofFinite _

theorem boundedCharacter_squarefree (ρ : supportedCharacters (fun i => ZMod (p i)) K) :
    Squarefree ((boundedCharacter p hp K pmax hmax hbound ρ).1.val+1) := by
  rw [boundedCharacter_conductor]
  apply squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    change IsRelPrime (p i) (p j)
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
      (fun he => hij (hp he))
  · intro i hi
    exact (Fact.out : (p i).Prime).squarefree

theorem primitiveCoefficient_squarefree (b : ∀ i, ZMod (p i) → ℝ)
    (χ : PrimitiveFamily (pmax^(2*K))) (hc : primitiveCoefficient p hp K pmax hmax hbound b χ ≠ 0) :
    Squarefree (χ.1.val+1) := by
  have hm : χ ∈ univ.image (boundedCharacter p hp K pmax hmax hbound) := by
    by_contra hn
    exact hc (groupedCoefficient_not_mem _ _ _ hn)
  obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hm
  exact boundedCharacter_squarefree p hp K pmax hmax hbound ρ

theorem primitiveCoefficient_eq_zero_of_excludedPrime (b : ∀ i, ZMod (p i) → ℝ)
    (χ : PrimitiveFamily (pmax^(2*K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ χ.1.val+1) (hne : ∀ i, p i ≠ ℓ) :
    primitiveCoefficient p hp K pmax hmax hbound b χ = 0 := by
  apply groupedCoefficient_not_mem
  intro hm
  obtain ⟨ρ, hρ, hρχ⟩ := mem_image.mp hm
  have hd : ℓ ∣ ∏ i ∈ characterSupport (fun i => ZMod (p i)) ρ.val, p i := by
    rw [← boundedCharacter_conductor p hp K pmax hmax hbound ρ, hρχ]
    exact hdvd
  exact prime_not_dvd_coordinateProduct _ p (fun i hi => Fact.out) hℓ (fun i hi => hne i) hd

variable (S : ∀ i, Finset (ZMod (p i)))

theorem actualPrimitiveCoefficient_principal :
    primitiveCoefficient p hp K pmax hmax hbound (fun i => localKernel (S i) sparseKernelScale)
      (principalCharacter K pmax hmax) = (unitWeightMean p S K : ℂ) := by
  rw [primitiveCoefficient_principal, localWeightCoefficient_one_eq_mean]

theorem norm_primitiveCoefficient_le_exp_band
    (hlo : ∀ i, (1/3 : ℝ) ≤ density (S i)) (hhi : ∀ i, density (S i) ≤ 2/3)
    (hg : ∀ i, gamma (S i) ≤ supplyEpsilon^2) {L : ℝ} (hL : 1 ≤ L)
    (hH : (∑ i, 1/(p i : ℝ)) ≤ L) (χ : PrimitiveFamily (pmax^(2*K))) :
    ‖primitiveCoefficient p hp K pmax hmax hbound
      (fun i => localKernel (S i) sparseKernelScale) χ‖ ≤
      Real.exp ((Real.log 1200 + 8*supplyEpsilon)*L) := by
  apply norm_groupedCoefficient_le _ _ _ (boundedCharacter_injective p hp K pmax hmax hbound).injOn
    (Real.exp_pos _).le
  intro ρ hρ
  exact norm_localWeightCoefficient_le_exp_band p S K ρ.val hlo hhi hg hL hH

theorem actual_grouped_primitive_error_le
    (hlo : ∀ i, (1/3 : ℝ) ≤ density (S i)) (hhi : ∀ i, density (S i) ≤ 2/3)
    (hg : ∀ i, gamma (S i) ≤ supplyEpsilon^2) {L : ℝ} (hL : 1 ≤ L)
    (hH : (∑ i, 1/(p i : ℝ)) ≤ L) (χ₀ : PrimitiveFamily (pmax^(2*K)))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ∣ χ₀.1.val+1) (hne : ∀ i, p i ≠ ℓ)
    (φ : ℝ → ℝ) (X : ℝ) :
    ‖∑ χ : PrimitiveFamily (pmax^(2*K)),
      primitiveCoefficient p hp K pmax hmax hbound (fun i => localKernel (S i) sparseKernelScale) χ *
        smoothError χ.2.1 φ X‖ ≤
      Real.exp ((Real.log 1200 + 8*supplyEpsilon)*L) *
        totalPrimitiveError (pmax^(2*K)) (some χ₀) φ X := by
  apply weighted_primitive_error_le
  · exact norm_primitiveCoefficient_le_exp_band p hp K pmax hmax hbound S hlo hhi hg hL hH
  · intro χ hχ
    have he : χ = χ₀ := Option.some.inj hχ
    subst χ
    exact primitiveCoefficient_eq_zero_of_excludedPrime p hp K pmax hmax hbound _ χ₀ hℓ hdvd hne

end Ostmann.Supply.GroupedCharacters

end

end OAI
