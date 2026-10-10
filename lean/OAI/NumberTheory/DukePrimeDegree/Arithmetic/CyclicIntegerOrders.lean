import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ZetaIsomorphism

namespace OAI

/-!
# Integer fixed-field orders at a simple cyclic zero

For a cyclic extension with the actual even ray realizations, a simple
zero selects one real character. Every intermediate-field zero order is
the indicator that this character is trivial on the fixing subgroup.
-/

noncomputable section
open Module
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

lemma realLinearCharacter_eq_one_iff {C : Type*} [Group C]
    (χ : C →* ℂˣ) (hr : ∀ g, (χ g : ℂ).im = 0) (g : C) :
    realLinearCharacter χ hr g = 1 ↔ χ g = 1 := by
  constructor
  · intro h
    apply Units.ext
    apply Complex.ext
    · have he := congrArg (fun z : ℝˣ => (z : ℝ)) h
      exact he
    · simpa only [Units.val_one, Complex.one_im] using hr g
  · intro h
    apply Units.ext
    change (χ g : ℂ).re = 1
    rw [h]
    rfl

lemma realLinearCharacter_ker {C : Type*} [Group C]
    (χ : C →* ℂˣ) (hr : ∀ g, (χ g : ℂ).im = 0) :
    (realLinearCharacter χ hr).ker = χ.ker := by
  ext g
  exact realLinearCharacter_eq_one_iff χ hr g

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)] [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
local instance : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _
local instance (L : IntermediateField F E) : NumberField.IsTotallyReal L :=
  NumberField.IsTotallyReal.of_algebra _ E

/-- Nonnegative orders in the cyclic factorization show that the base
field's zero multiplicity cannot exceed the extension's. -/
theorem zetaMultiplicity_le_of_cyclic_ray_family
    {N : ℕ} [NeZero N]
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaMultiplicity F β ≤ zetaMultiplicity E β := by
  let σ := canonicalRealEmbeddings F
  let τ := canonicalRealEmbeddings E
  choose m hm using fun χ => cyclicHeckeFactor_finite_nonnegative_order
    σ (degreePred_spec F) ψ hψ χ hβ0 hβ1
  have hsum := cyclicHeckeFactor_sum_orders σ (degreePred_spec F)
    τ (degreePred_spec E) ψ hid hψ hD hβ0 hβ1
  rw [← zetaZeroOrder_eq_completed_order τ (degreePred_spec E) hβ0 hβ1,
    zetaZeroOrder_eq_multiplicity E hβ0 hβ1] at hsum
  simp only [hm] at hsum
  have hsum' : (∑ χ, (m χ : ℤ)) = zetaMultiplicity E β := by exact_mod_cast hsum
  have hone := hm 1
  simp only [cyclicHeckeFactor, ite_true] at hone
  rw [← zetaZeroOrder_eq_coset_order σ (degreePred_spec F) N hβ0 hβ1,
    zetaZeroOrder_eq_multiplicity F hβ0 hβ1] at hone
  have hone' : zetaMultiplicity F β = (m 1 : ℤ) := by exact_mod_cast hone
  rw [hone', ← hsum']
  exact Finset.single_le_sum (fun χ _ => Int.natCast_nonneg (m χ)) (Finset.mem_univ _)

/-- The cyclic analytic step expressed with the actual integer zeta
multiplicities used in odd-degree descent. -/
theorem exists_real_character_of_simple_zeta
    {N : ℕ} [NeZero N]
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsimple : zetaMultiplicity E β = 1) :
    ∃ χ : (E ≃ₐ[F] E) →* ℝˣ,
      ∀ L : IntermediateField F E,
        zetaMultiplicity L β = if L.fixingSubgroup ≤ χ.ker then 1 else 0 := by
  let σ := canonicalRealEmbeddings F
  let τ := canonicalRealEmbeddings E
  have hsum : (∑ χ, meromorphicOrderAt
      (cyclicHeckeFactor σ (degreePred_spec F) ψ χ) (β : ℂ)) = 1 := by
    rw [cyclicHeckeFactor_sum_orders σ (degreePred_spec F) τ (degreePred_spec E)
      ψ hid hψ hD hβ0 hβ1,
      ← zetaZeroOrder_eq_completed_order τ (degreePred_spec E) hβ0 hβ1,
      zetaZeroOrder_eq_multiplicity E hβ0 hβ1, hsimple]
    rfl
  obtain ⟨χ, hχ, hrest, hr⟩ := real_character_of_simple_cyclic_zero
    σ (degreePred_spec F) ψ hid hψ hβ0 hβ1 hsum
  refine ⟨realLinearCharacter χ hr, fun L => ?_⟩
  have ho := cyclic_subfield_order_of_unique_character L σ (degreePred_spec F)
    (canonicalRealEmbeddings L) (degreePred_spec L) ψ hid hψ hD hβ0 hβ1 χ hχ hrest
  rw [← zetaZeroOrder_eq_completed_order (canonicalRealEmbeddings L)
    (degreePred_spec L) hβ0 hβ1, zetaZeroOrder_eq_multiplicity L hβ0 hβ1] at ho
  rw [realLinearCharacter_ker]
  split_ifs with hL
  · rw [ite_eq_left hL] at ho
    exact_mod_cast ho
  · rw [ite_eq_right hL] at ho
    exact_mod_cast ho

end DukePrimeDegree

end

end OAI
