import OAI.AlgebraicGeometry.SurfaceCones.KummerTripleOpen

namespace OAI

/-! The five line ratios are independent modulo p-th powers, by their line valuations. -/
noncomputable section
open scoped BigOperators
namespace KummerLines

lemma lineForm_not_dvd (i j : Fin 5) (h : i ≠ j) : ¬ lineForm i ∣ lineForm j := by
  intro hd
  obtain ⟨a, ha⟩ := hd
  have hh := congrArg (MvPolynomial.eval (point i)) ha
  rw [map_mul, eval_at_self, zero_mul] at hh
  exact eval_at_other i j h hh

lemma emultiplicity_lineProduct (e : Fin 5 → ℕ) (i : Fin 5) :
    emultiplicity (lineForm i) (∏ j, lineForm j ^ e j) = e i := by
  rw [Finset.emultiplicity_prod (prime_lineForm i)]
  rw [Finset.sum_eq_single i]
  · exact emultiplicity_pow_self_of_prime (prime_lineForm i) (e i)
  · intro j _ hji
    rw [emultiplicity_pow (prime_lineForm i),
      emultiplicity_eq_zero.mpr (lineForm_not_dvd i j hji.symm), mul_zero]
  · simp

lemma radicand_ne_zero (i : Fin 5) : radicand i ≠ 0 := by
  simpa only [radicand, map_zero] using (IsFractionRing.injective R K).ne (prime_lineForm i).ne_zero

/-- affine-line valuation independence, with bounded exponents.
If two radical monomials differ by a p-th power in the rational
function field, their vectors of exponents modulo p agree. -/
lemma radicand_pow_independent (p : ℕ) (hp : 0 < p)
    (e f : Fin 5 → Fin p) (z : K)
    (hz : ∏ i, radicand i ^ (e i).val = z ^ p * ∏ i, radicand i ^ (f i).val) :
    e = f := by
  have hprod (g : Fin 5 → Fin p) : (∏ i, radicand i ^ (g i).val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (radicand_ne_zero i))
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne', zero_mul] at hz
    exact hprod e hz
  obtain ⟨b,c,hc,hbc⟩ := IsFractionRing.div_surjective R z
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hbc
    exact hz0 hbc.symm
  have hbK : algebraMap R K b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hb0
  have hcK : algebraMap R K c ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hc0
  have hint : (∏ i, lineForm i ^ (e i).val) * c ^ p =
      b ^ p * ∏ i, lineForm i ^ (f i).val := by
    apply (IsFractionRing.injective R K)
    simp only [map_mul, map_pow, map_prod]
    change (∏ i, radicand i ^ (e i).val) * (algebraMap R K c)^p =
      (algebraMap R K b)^p * ∏ i, radicand i ^ (f i).val
    rw [← hbc, div_pow] at hz
    exact (eq_div_iff (pow_ne_zero p hcK)).mp (by
      rw [hz]; field_simp)
  funext i
  apply Fin.ext
  have hm := congrArg (emultiplicity (lineForm i)) hint
  rw [emultiplicity_mul (prime_lineForm i), emultiplicity_mul (prime_lineForm i),
    emultiplicity_lineProduct, emultiplicity_lineProduct,
    emultiplicity_pow (prime_lineForm i), emultiplicity_pow (prime_lineForm i),
    (FiniteMultiplicity.of_prime_left (prime_lineForm i) hc0).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left (prime_lineForm i) hb0).emultiplicity_eq_multiplicity] at hm
  have hn : (e i).val + p * multiplicity (lineForm i) c =
      p * multiplicity (lineForm i) b + (f i).val := by exact_mod_cast hm
  have he := (e i).isLt
  have hf := (f i).isLt
  have hh := congrArg (fun n => n % p) hn
  simpa [Nat.add_mod, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf] using hh

end KummerLines

end


/-! Characters of radical monomials in the Galois Kummer extension. -/
noncomputable section
open scoped BigOperators
namespace KummerLines
open Polynomial
variable (p : ℕ) [Fact p.Prime]

abbrev actualRoot (i : Fin 5) : L p := KummerCover.fieldRoot (p := p) radicand i

lemma actualRoot_pow (i : Fin 5) : actualRoot p i ^ p = algebraMap K (L p) (radicand i) :=
  KummerCover.fieldRoot_pow radicand i

lemma actualRoot_ne_zero (i : Fin 5) : actualRoot p i ≠ 0 := by
  intro h
  have hh := actualRoot_pow p i
  rw [h, zero_pow (NeZero.ne p)] at hh
  exact radicand_ne_zero i ((algebraMap K (L p)).injective (by simpa using hh.symm))

abbrev primitiveScalar : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
lemma primitiveScalar_root : IsPrimitiveRoot (primitiveScalar p) p :=
  Complex.isPrimitiveRoot_exp p (NeZero.ne p)

lemma primitiveScalar_map_root :
    IsPrimitiveRoot (algebraMap ℂ (L p) (primitiveScalar p)) p :=
  (primitiveScalar_root p).map_of_injective (algebraMap ℂ (L p)).injective

lemma rootPolynomial_splits (i : Fin 5) :
    ((X ^ p - C (radicand i)).map (algebraMap K (L p))).Splits := by
  simpa using X_pow_sub_C_splits_of_isPrimitiveRoot (primitiveScalar_map_root p)
    (actualRoot_pow p i)

instance actual_rootField_normal : Normal K (L p) := by
  apply normal_iff.mpr
  intro x
  refine ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
  apply IntermediateField.splits_of_mem_adjoin (F := K) (K := L p) (L := L p)
    (S := Set.range (actualRoot p))
  · rintro _ ⟨i,rfl⟩
    refine ⟨Algebra.IsIntegral.isIntegral _, ?_⟩
    apply (rootPolynomial_splits p i).of_dvd
    · exact Polynomial.map_ne_zero (X_pow_sub_C_ne_zero (NeZero.pos p) _)
    · apply Polynomial.map_dvd
      exact minpoly.dvd K _ (by simp [actualRoot_pow])
  · have hh : Algebra.adjoin K (Set.range (actualRoot p)) ≤
        (IntermediateField.adjoin K (Set.range (actualRoot p))).toSubalgebra := by
      apply Algebra.adjoin_le
      exact IntermediateField.subset_adjoin K _
    rw [KummerCover.fieldRoot_generates] at hh
    exact hh (by trivial : x ∈ (⊤ : Subalgebra K (L p)))

instance actual_rootField_galois : IsGalois K (L p) where

/-- Every p-th root of unity in the extension is a complex scalar,
hence fixed by every base-field automorphism. -/
lemma aut_fixes_rootUnity (σ : L p ≃ₐ[K] L p) (x : L p) (hx : x ^ p = 1) :
    σ x = x := by
  obtain ⟨j,_,hj⟩ := (primitiveScalar_map_root p).eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow]
  congr 1
  rw [IsScalarTower.algebraMap_apply ℂ K (L p), σ.commutes]

lemma aut_quotient_pow (x : L p) (hx : x ≠ 0) (a : K)
    (ha : x ^ p = algebraMap K (L p) a) (σ : L p ≃ₐ[K] L p) :
    (σ x / x)^p = 1 := by
  rw [div_pow, ← map_pow, ha, σ.commutes]
  exact div_self (ha ▸ pow_ne_zero _ hx)

/-- The action character of a radical monomial. -/
def radicalCharacter (x : L p) (hx : x ≠ 0) (a : K)
    (ha : x ^ p = algebraMap K (L p) a) : (L p ≃ₐ[K] L p) →* L p where
  toFun σ := σ x / x
  map_one' := by simp [hx]
  map_mul' σ τ := by
    have h := aut_fixes_rootUnity p σ (τ x / x) (aut_quotient_pow p x hx a ha τ)
    change σ (τ x) / x = (σ x / x) * (τ x / x)
    rw [map_div₀] at h
    have hσx : σ x ≠ 0 := by simpa only [map_zero] using σ.injective.ne hx
    apply (div_eq_iff hx).mpr
    calc
      σ (τ x) = (τ x / x) * σ x := (div_eq_iff hσx).mp h
      _ = (σ x / x * (τ x / x)) * x := by field_simp

abbrev radicalMonomial (e : Fin 5 → Fin p) : L p := ∏ i, actualRoot p i ^ (e i).val
abbrev radicandMonomial (e : Fin 5 → Fin p) : K := ∏ i, radicand i ^ (e i).val
lemma radicalMonomial_ne_zero (e : Fin 5 → Fin p) : radicalMonomial p e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (actualRoot_ne_zero p i))
lemma radicalMonomial_pow (e : Fin 5 → Fin p) :
    radicalMonomial p e ^ p = algebraMap K (L p) (radicandMonomial p e) := by
  dsimp only [radicalMonomial, radicandMonomial]
  rw [← Finset.prod_pow, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, Nat.mul_comm, pow_mul, actualRoot_pow, map_pow]

def monomialCharacter (e : Fin 5 → Fin p) : (L p ≃ₐ[K] L p) →* L p :=
  radicalCharacter p (radicalMonomial p e) (radicalMonomial_ne_zero p e)
    (radicandMonomial p e) (radicalMonomial_pow p e)

lemma monomialCharacter_injective : Function.Injective (monomialCharacter p) := by
  intro e f hef
  have hfixed : ∀ σ : L p ≃ₐ[K] L p,
      σ (radicalMonomial p e / radicalMonomial p f) =
        radicalMonomial p e / radicalMonomial p f := by
    intro σ
    have hh := DFunLike.congr_fun hef σ
    change σ (radicalMonomial p e) / radicalMonomial p e =
      σ (radicalMonomial p f) / radicalMonomial p f at hh
    rw [map_div₀]
    apply (div_eq_div_iff (by simpa only [map_zero] using σ.injective.ne (radicalMonomial_ne_zero p f))
      (radicalMonomial_ne_zero p f)).mpr
    exact ((div_eq_div_iff (radicalMonomial_ne_zero p e)
      (radicalMonomial_ne_zero p f)).mp hh).trans (mul_comm _ _)
  obtain ⟨z,hz⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfixed
  apply radicand_pow_independent p (NeZero.pos p) e f z
  apply (algebraMap K (L p)).injective
  change algebraMap K (L p) (radicandMonomial p e) =
    algebraMap K (L p) (z ^ p * radicandMonomial p f)
  rw [map_mul, map_pow, ← radicalMonomial_pow p e, ← radicalMonomial_pow p f, hz,
    div_pow, div_mul_cancel₀ _ (pow_ne_zero p (radicalMonomial_ne_zero p f))]

end KummerLines

end

/-! The five independent radicals generate a field extension of degree p^5. -/
noncomputable section
open scoped BigOperators
namespace KummerLines
variable (p : ℕ) [Fact p.Prime]

lemma radicalMonomial_linearIndependent :
    LinearIndependent K (radicalMonomial p) := by
  have hchar : LinearIndependent (L p) (fun e : Fin 5 → Fin p =>
      (monomialCharacter p e : (L p ≃ₐ[K] L p) → L p)) :=
    (linearIndependent_monoidHom (L p ≃ₐ[K] L p) (L p)).comp
      (monomialCharacter p) (monomialCharacter_injective p)
  rw [linearIndependent_iff'] at hchar ⊢
  intro s g hg e he
  have hc : (∑ i ∈ s, (fun σ : L p ≃ₐ[K] L p =>
      (algebraMap K (L p) (g i) * radicalMonomial p i) * monomialCharacter p i σ)) =
        (0 : (L p ≃ₐ[K] L p) → L p) := by
    funext σ
    simp only [Finset.sum_apply, Pi.zero_apply]
    change (∑ i ∈ s, (algebraMap K (L p) (g i) * radicalMonomial p i) *
      (σ (radicalMonomial p i) / radicalMonomial p i)) = 0
    have hσ := congrArg σ hg
    rw [map_sum, map_zero] at hσ
    convert hσ using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, map_mul, σ.commutes]
    field_simp [radicalMonomial_ne_zero p i]
  have hh := hchar s (fun i => algebraMap K (L p) (g i) * radicalMonomial p i) hc e he
  exact (algebraMap K (L p)).injective (by
    simpa only [map_zero] using (mul_eq_zero.mp hh).resolve_right (radicalMonomial_ne_zero p e))

lemma radicalMonomial_degree_lower : p ^ 5 ≤ Module.finrank K (L p) := by
  simpa using (radicalMonomial_linearIndependent p).fintype_card_le_finrank

/-- action on the five chosen radicals, with values in the roots of unity. -/
def rootAction (σ : L p ≃ₐ[K] L p) (i : Fin 5) : rootsOfUnity p (L p) :=
  ⟨Units.mk0 (σ (actualRoot p i) / actualRoot p i)
    (div_ne_zero (by simpa only [map_zero] using σ.injective.ne (actualRoot_ne_zero p i))
      (actualRoot_ne_zero p i)), by
    apply (mem_rootsOfUnity p _).mpr
    apply Units.ext
    exact aut_quotient_pow p _ (actualRoot_ne_zero p i) _ (actualRoot_pow p i) σ⟩

lemma rootAction_injective : Function.Injective (rootAction p) := by
  intro σ τ h
  have hhom : (σ : L p →ₐ[K] L p) = (τ : L p →ₐ[K] L p) := by
    apply AlgHom.ext_of_adjoin_eq_top (KummerCover.fieldRoot_generates radicand)
    rintro _ ⟨i,rfl⟩
    have hh := congrArg (fun f => ((f i : (L p)ˣ) : L p)) h
    change σ (actualRoot p i) / actualRoot p i =
      τ (actualRoot p i) / actualRoot p i at hh
    exact (div_left_inj' (actualRoot_ne_zero p i)).mp hh
  exact AlgEquiv.ext (fun x => DFunLike.congr_fun hhom x)

lemma actual_rootField_degree : Module.finrank K (L p) = p ^ 5 := by
  apply le_antisymm _ (radicalMonomial_degree_lower p)
  rw [← IsGalois.card_aut_eq_finrank K (L p)]
  have h := Nat.card_le_card_of_injective (rootAction p) (rootAction_injective p)
  simpa only [Nat.card_fun, Nat.card_fin, (primitiveScalar_map_root p).card_rootsOfUnity]
    using h

end KummerLines

end

/-! Radical monomial bases and the degree of the off-branch cover. -/
noncomputable section
open scoped BigOperators
namespace KummerLines
variable (p : ℕ) [Fact p.Prime]

lemma rootAction_bijective : Function.Bijective (rootAction p) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨rootAction_injective p, ?_⟩
  rw [IsGalois.card_aut_eq_finrank K (L p), actual_rootField_degree,
    Nat.card_fun, Nat.card_fin, (primitiveScalar_map_root p).card_rootsOfUnity]

/-- Basis of the source field by its radical monomials. -/
def radicalBasis : Module.Basis (Fin 5 → Fin p) K (L p) :=
  basisOfLinearIndependentOfCardEqFinrank (radicalMonomial_linearIndependent p)
    (by simpa using (actual_rootField_degree p).symm)

local instance : Algebra U (offBranchCover p) := (integralClosure U (L p)).algebra
local instance : SMul U (offBranchCover p) :=
  @Algebra.toSMul U (offBranchCover p) _ _ (integralClosure U (L p)).algebra
local instance : Module U (offBranchCover p) := (integralClosure U (L p)).toSubmodule.module

local instance : Algebra (offBranchCover p) (L p) :=
  (integralClosure U (L p)).toAlgebra
local instance : IsScalarTower U (offBranchCover p) (L p) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower U K (L p) :=
  IsScalarTower.of_algebraMap_eq' rfl

lemma offBranchCover_degree : Module.finrank U (offBranchCover p) = p ^ 5 := by
  let : IsFractionRing (offBranchCover p) (L p) :=
    KummerEtale.fractionRing_of_generators (K := K) _
      (Set.range (KummerCover.fieldRoot (p := p) radicand))
      (KummerCover.fieldRoot_generates radicand) (by
        change _ ⊆ (integralClosure U (L p) : Set (L p))
        rw [offBranch_normalization]
        exact Algebra.subset_adjoin)
  exact (IsFractionRing.finrank_eq U K (offBranchCover p) (L p)).symm.trans
    (actual_rootField_degree p)

end KummerLines

end

/-! The extension over the two ramified coordinates has degree p^3. -/
noncomputable section
open scoped BigOperators
namespace KummerLines
variable (p : ℕ) [Fact p.Prime]

abbrev coordinateField : IntermediateField K (L p) :=
  IntermediateField.adjoin K (Set.range fun i : Fin 2 => actualRoot p (Fin.castAdd 3 i))

lemma rootAction_eq_one_iff (σ : L p ≃ₐ[K] L p) (i : Fin 5) :
    rootAction p σ i = 1 ↔ σ (actualRoot p i) = actualRoot p i := by
  constructor
  · intro h
    have hh := congrArg (fun x : rootsOfUnity p (L p) => ((x : (L p)ˣ) : L p)) h
    change σ (actualRoot p i) / actualRoot p i = 1 at hh
    exact (div_eq_one_iff_eq (actualRoot_ne_zero p i)).mp hh
  · intro h
    apply Subtype.ext
    apply Units.ext
    change σ (actualRoot p i) / actualRoot p i = 1
    rw [h, div_self (actualRoot_ne_zero p i)]

lemma mem_coordinateFix_iff (σ : L p ≃ₐ[K] L p) :
    σ ∈ (coordinateField p).fixingSubgroup ↔
      ∀ i : Fin 2, rootAction p σ (Fin.castAdd 3 i) = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h i
    exact (rootAction_eq_one_iff p σ _).mpr
      (h _ (IntermediateField.subset_adjoin K _ (Set.mem_range_self i)))
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact (rootAction_eq_one_iff p σ _).mp (h i)
    | algebraMap x => exact σ.commutes x
    | add x y hx hy h₁ h₂ => simp [map_add, h₁, h₂]
    | mul x y hx hy h₁ h₂ => simp [map_mul, h₁, h₂]
    | inv x hx h₁ => simp [map_inv₀, h₁]

/-- The fixing subgroup, with precisely the three remaining scalars. -/
def coordinateAction (σ : (coordinateField p).fixingSubgroup)
    (i : Fin 3) : rootsOfUnity p (L p) := rootAction p σ.val (Fin.natAdd 2 i)

lemma coordinateAction_injective : Function.Injective (coordinateAction p) := by
  intro σ τ h
  apply Subtype.ext
  apply rootAction_injective p
  funext i
  refine Fin.addCases (m := 2) (n := 3) ?_ ?_ i
  · intro j
    rw [(mem_coordinateFix_iff p σ.val).mp σ.property,
      (mem_coordinateFix_iff p τ.val).mp τ.property]
  · intro j
    exact congrFun h j

lemma coordinateAction_surjective : Function.Surjective (coordinateAction p) := by
  intro f
  obtain ⟨σ, hσ⟩ := (rootAction_bijective p).surjective (fun i : Fin 5 => Fin.addCases (m := 2) (n := 3) (fun _ : Fin 2 => 1) f i)
  have hf : σ ∈ (coordinateField p).fixingSubgroup := by
    apply (mem_coordinateFix_iff p σ).mpr
    intro i
    rw [hσ]
    simp
  refine ⟨⟨σ, hf⟩, ?_⟩
  funext i
  change rootAction p σ (Fin.natAdd 2 i) = f i
  rw [hσ]
  simp

lemma coordinateField_degree : Module.finrank (coordinateField p) (L p) = p ^ 3 := by
  rw [← IsGalois.card_fixingSubgroup_eq_finrank]
  rw [Nat.card_congr (Equiv.ofBijective (coordinateAction p)
    ⟨coordinateAction_injective p, coordinateAction_surjective p⟩),
    Nat.card_fun, Nat.card_fin, (primitiveScalar_map_root p).card_rootsOfUnity]

end KummerLines

end

end OAI
