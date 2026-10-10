import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets

section

open AddChar MulChar

theorem primitive_gaussSum_mul_inv {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = q := by
  classical
  calc
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ =
        ∑ a : ZMod q, gaussSum χ (e.mulShift a) * e (-a) := by
      simp_rw [gaussSum_mulShift_of_isPrimitive e hχ]
      change gaussSum χ e * (∑ a : ZMod q, χ⁻¹ a * e (-a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q, e (a * (b - 1)) := by
      simp only [gaussSum, mulShift_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext b
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = q := by
      simp_rw [sum_mulShift _ he]
      simp [sub_eq_zero]

theorem primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * q := by
  rw [pow_two, ← primitive_gaussSum_mul_inv hχ he, hquad.inv, mul_rotate']
  congr 1
  rw [mul_comm, ← gaussSum_mulShift χ e (-1 : (ZMod q)ˣ), e.inv_mulShift]
  rfl

theorem primitive_gaussSum_ne_zero {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) : gaussSum χ e ≠ 0 := by
  intro h
  have hq := primitive_gaussSum_mul_inv hχ he
  rw [h, zero_mul] at hq
  exact (Nat.cast_ne_zero.mpr (NeZero.ne q)) hq.symm

theorem primitive_quadratic_gaussSum_integer_square {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    ∃ D : ℤ, D.natAbs = q ∧ gaussSum χ e ^ 2 = (D : R) := by
  have hnonzero : χ (-1) ≠ 0 := (isUnit_neg_one.map χ).ne_zero
  rcases hquad (-1) with h | h | h
  · exact (hnonzero h).elim
  · exact ⟨q, by simp, by simp [primitive_quadratic_gaussSum_sq hχ hquad he, h]⟩
  · exact ⟨-q, by simp, by simp [primitive_quadratic_gaussSum_sq hχ hquad he, h]⟩

end

theorem factorsThrough_ringHomComp_iff {q d : ℕ} [NeZero q]
    {R S : Type*} [CommRing R] [CommRing S] (χ : DirichletCharacter R q)
    (f : R →+* S) (hf : Function.Injective f) :
    DirichletCharacter.FactorsThrough (χ.ringHomComp f) d ↔ χ.FactorsThrough d := by
  by_cases hd : d ∣ q
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    change (∀ a, a ∈ (ZMod.unitsMap hd).ker → _ = 1) ↔
      (∀ a, a ∈ (ZMod.unitsMap hd).ker → _ = 1)
    simp only [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one,
      MulChar.ringHomComp_apply, ← f.map_one, hf.eq_iff]
  · exact iff_of_false (fun h ↦ hd h.dvd) (fun h ↦ hd h.dvd)

theorem conductor_ringHomComp {q : ℕ} [NeZero q]
    {R S : Type*} [CommRing R] [CommRing S] (χ : DirichletCharacter R q)
    (f : R →+* S) (hf : Function.Injective f) :
    DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact factorsThrough_ringHomComp_iff χ f hf

noncomputable def integerCharacter {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) : DirichletCharacter ℤ q := by
  let v : ZMod q → ℤ := fun a ↦ ⌊(χ a).re⌋
  have hv (a : ZMod q) : (v a : ℂ) = χ a := by
    rcases hquad a with h | h | h <;> norm_num [v, h]
  exact
    { toFun := v
      map_one' := by
        apply Int.cast_injective (α := ℂ)
        rw [hv, map_one, Int.cast_one]
      map_mul' := fun a b ↦ by
        apply Int.cast_injective (α := ℂ)
        rw [Int.cast_mul, hv, hv, hv, map_mul]
      map_nonunit' := fun a ha ↦ by
        apply Int.cast_injective (α := ℂ)
        rw [hv, MulChar.map_nonunit χ ha, Int.cast_zero] }

@[simp]
theorem integerCharacter_cast {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (a : ZMod q) : (integerCharacter χ hquad a : ℂ) = χ a := by
  change (⌊(χ a).re⌋ : ℂ) = χ a
  rcases hquad a with h | h | h <;> norm_num [h]

theorem integerCharacter_ringHomComp {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) :
    (integerCharacter χ hquad).ringHomComp (Int.castRingHom ℂ) = χ := by
  ext a
  exact integerCharacter_cast χ hquad a

theorem integerCharacter_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    (integerCharacter χ hquad).IsPrimitive := by
  change DirichletCharacter.conductor (integerCharacter χ hquad) = q
  rw [← conductor_ringHomComp (integerCharacter χ hquad) (Int.castRingHom ℂ)
    (Int.cast_injective (α := ℂ)), integerCharacter_ringHomComp]
  exact hprim

theorem integerCharacter_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) : (integerCharacter χ hquad).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply MulChar.injective_ringHomComp (f := Int.castRingHom ℂ) (Int.cast_injective (α := ℂ))
  dsimp only
  rw [← MulChar.ringHomComp_pow, integerCharacter_ringHomComp,
    MulChar.ringHomComp_one, hquad.sq_eq_one]

open NumberField IsCyclotomicExtension.Rat

theorem cyclotomic_gaussSum_action {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (χ : DirichletCharacter K n) (hχ : χ.IsQuadratic)
    (e : AddChar (ZMod n) K) (σ : Gal(K/ℚ)) :
    σ (gaussSum χ e) = χ (galEquivZMod n K σ) * gaussSum χ e := by
  have hroot (x : ZMod n) : e x ^ n = 1 := by
    rw [← e.map_nsmul_eq_pow, nsmul_eq_mul]
    simp
  have he (x : ZMod n) : σ (e x) = e ((galEquivZMod n K σ) * x) := by
    rw [galEquivZMod_apply_of_pow_eq n K σ (hroot x), ← e.map_nsmul_eq_pow,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc
    σ (gaussSum χ e) = gaussSum χ (e.mulShift (galEquivZMod n K σ)) := by
      simp only [gaussSum, map_sum, map_mul, AddChar.mulShift_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [he]
      congr 1
      rcases hχ x with h | h | h <;> simp [h]
    _ = χ (galEquivZMod n K σ) * gaussSum χ e := by
      rw [gaussSum_mulShift_eq, hχ.inv]

section

open NumberField IsCyclotomicExtension.Rat

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

noncomputable def characterField (χ : DirichletCharacter R n) : IntermediateField ℚ K :=
  (intermediateFieldEquivSubgroupChar n K R).symm (Subgroup.zpowers χ)

theorem characterField_finrank (χ : DirichletCharacter R n) (hχ : χ.IsQuadratic)
    (hne : χ ≠ 1) : Module.finrank ℚ (characterField n K R χ) = 2 := by
  rw [← card_intermediateFieldEquivSubgroupChar n K R, characterField,
    OrderIso.apply_symm_apply, Nat.card_zpowers]
  exact orderOf_eq_prime hχ.sq_eq_one hne

theorem mem_characterField_fixingSubgroup (χ : DirichletCharacter R n)
    (hχ : χ.IsQuadratic) (σ : Gal(K/ℚ)) :
    σ ∈ (characterField n K R χ).fixingSubgroup ↔ χ (galEquivZMod n K σ) = 1 := by
  change σ ∈ (IntermediateField.fixedField
    ((subgroupGalEquivSubgroupChar n K R).symm
      (OrderDual.toDual (Subgroup.zpowers χ)))).fixingSubgroup ↔ _
  rw [IntermediateField.fixingSubgroup_fixedField, mem_subgroupGalEquivSubgroupChar_symm_iff]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simp only [zpow_natCast, MulChar.pow_apply_coe, h, one_pow]
    · simp only [zpow_neg, zpow_natCast, ← inv_pow, hχ.inv, MulChar.pow_apply_coe, h, one_pow]

theorem characterField_changeLevel [IsDomain R] {m : ℕ} [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [IsAbelianGalois ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)]
    (hdiv : n ∣ m) (χ : DirichletCharacter R n) (hχ : χ.IsQuadratic) :
    characterField m L R (DirichletCharacter.changeLevel hdiv χ) =
      (characterField n K R χ).map (IsScalarTower.toAlgHom ℚ K L) := by
  have hχ' : (DirichletCharacter.changeLevel hdiv χ).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow, hχ.sq_eq_one, map_one]
  apply (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := L)).injective
  change (characterField m L R (DirichletCharacter.changeLevel hdiv χ)).fixingSubgroup =
    ((characterField n K R χ).map (IsScalarTower.toAlgHom ℚ K L)).fixingSubgroup
  ext σ
  have hm : σ ∈ ((characterField n K R χ).map
      (IsScalarTower.toAlgHom ℚ K L)).fixingSubgroup ↔
      σ.restrictNormal K ∈ (characterField n K R χ).fixingSubgroup := by
    simp only [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      apply (algebraMap K L).injective
      rw [AlgEquiv.restrictNormal_commutes]
      exact h _ ⟨x, hx, rfl⟩
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := hy
      change σ (algebraMap K L x) = algebraMap K L x
      rw [← AlgEquiv.restrictNormal_commutes, h x hx]
  rw [hm, mem_characterField_fixingSubgroup n K R χ hχ,
    mem_characterField_fixingSubgroup m L R _ hχ']
  rw [galEquivZMod_restrictNormal_apply m L K hdiv σ]
  simp [DirichletCharacter.changeLevel_def]

end

section

open NumberField IsCyclotomicExtension.Rat

theorem mem_adjoin_fixingSubgroup_iff {F K : Type*} [Field F] [Field K] [Algebra F K]
    (g : K) (σ : Gal(K/F)) :
    σ ∈ (IntermediateField.adjoin F {g}).fixingSubgroup ↔ σ g = g := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le,
    IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff,
    Subgroup.forall_mem_zpowers]
  simpa only [MulAction.mem_fixedBy, AlgEquiv.smul_def] using
    (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ) (a := g))

theorem gaussSum_adjoin_eq_characterField {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℤ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod n) K) (he : e.IsPrimitive) :
    IntermediateField.adjoin ℚ {gaussSum (χ.ringHomComp (Int.castRingHom K)) e} =
      characterField n K ℂ (χ.ringHomComp (Int.castRingHom ℂ)) := by
  have hprimK : DirichletCharacter.IsPrimitive (χ.ringHomComp (Int.castRingHom K)) := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χ (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hprim
  have hg := primitive_gaussSum_ne_zero hprimK he
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  change (IntermediateField.adjoin ℚ {_}).fixingSubgroup =
    (characterField n K ℂ (χ.ringHomComp (Int.castRingHom ℂ))).fixingSubgroup
  ext σ
  rw [mem_adjoin_fixingSubgroup_iff, mem_characterField_fixingSubgroup _ _ _ _
    (hχ.comp (Int.castRingHom ℂ)), cyclotomic_gaussSum_action _
    (hχ.comp (Int.castRingHom K)), mul_eq_right₀ hg]
  change ((χ (galEquivZMod n K σ) : K) = 1) ↔
    ((χ (galEquivZMod n K σ) : ℂ) = 1)
  norm_cast

end

theorem exists_squarefree_generator {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    {D : ℤ} (hD : D ≠ 0) {g : K} (hg : g ^ 2 = (D : K)) :
    ∃ (d c : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ D.natAbs ∧ c ≠ 0 ∧
      D = c ^ 2 * d ∧ a ^ 2 = (d : K) ∧ IsIntegral ℤ a ∧ g = (c : K) * a ∧
      IntermediateField.adjoin ℚ {a} = IntermediateField.adjoin ℚ {g} := by
  obtain ⟨c, d, hcd, hd⟩ := exists_sq_mul_squarefree D
  have hc : c ≠ 0 := by
    intro h
    apply hD
    rw [← hcd, h]
    simp
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have had : (g / (c : K)) ^ 2 = (d : K) := by
    rw [div_pow, hg, ← hcd]
    push_cast
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hcK)
  refine ⟨d, c, g / (c : K), hd, ?_, hc, hcd.symm, had, ?_, ?_, ?_⟩
  · apply Nat.le_of_dvd (Int.natAbs_pos.mpr hD)
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [← hcd, mul_comm]⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [had]
    exact isIntegral_algebraMap
  · exact (mul_div_cancel₀ g hcK).symm
  · simpa only [div_eq_mul_inv, map_inv₀, map_intCast] using
      IntermediateField.adjoin_simple_mul_algebraMap (F := ℚ) g ((c : ℚ)⁻¹)
        (inv_ne_zero (Int.cast_ne_zero.mpr hc))

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem not_isSquare_of_quadratic_adjoin {K : Type*} [Field K] [Algebra ℚ K]
    {d : ℤ} {a : K} (ha : a ^ 2 = (d : K))
    (hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2) :
    ¬ IsSquare (d : ℚ) := by
  rintro ⟨r, hr⟩
  have hs : a ^ 2 = (algebraMap ℚ K r) ^ 2 := by
    calc
      a ^ 2 = (d : K) := ha
      _ = algebraMap ℚ K (d : ℚ) := by simp
      _ = (algebraMap ℚ K r) ^ 2 := by rw [hr, map_mul, pow_two]
  have hmem : a ∈ (⊥ : IntermediateField ℚ K) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
    · rw [h]
      exact IntermediateField.algebraMap_mem _ _
    · rw [h]
      exact (⊥ : IntermediateField ℚ K).neg_mem (IntermediateField.algebraMap_mem _ _)
  rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem,
    IntermediateField.finrank_bot] at hdim
  norm_num at hdim

theorem exists_squarefree_characterField_generator {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ σ : Gal(K/ℚ), σ a = (integerCharacter χ hχ (galEquivZMod n K σ) : K) * a := by
  let χI := integerCharacter χ hχ
  let χK := χI.ringHomComp (Int.castRingHom K)
  have hI := integerCharacter_isQuadratic χ hχ
  have hpI := integerCharacter_isPrimitive χ hχ hprim
  have hK : χK.IsQuadratic := hI.comp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χI (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hpI
  let e := AddChar.zmodChar n (zeta_spec n ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root n (zeta_spec n ℚ K)
  obtain ⟨D, hDabs, hgD⟩ := primitive_quadratic_gaussSum_integer_square hpK hK he
  have hD : D ≠ 0 := by
    intro h
    have := hDabs
    rw [h, Int.natAbs_zero] at this
    exact (NeZero.ne n) this.symm
  obtain ⟨d, c, a, hd, hbound, hc, hdc, ha, hint, hga, hadj⟩ :=
    exists_squarefree_generator hD hgD
  have hadjχ : IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ := by
    rw [hadj, gaussSum_adjoin_eq_characterField χI hI hpI e he]
    congr 1
    exact integerCharacter_ringHomComp χ hχ
  have hdiv : d.natAbs ∣ n := by
    rw [← hDabs]
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [hdc, mul_comm]⟩
  have hnsq : ¬ IsSquare (d : ℚ) := by
    apply not_isSquare_of_quadratic_adjoin ha
    rw [hadjχ]
    exact characterField_finrank n K ℂ χ hχ hne
  refine ⟨d, a, hd, hDabs ▸ hbound, hdiv, hnsq, ha, hint, hadjχ, ?_⟩
  intro σ
  have hact := cyclotomic_gaussSum_action χK hK e σ
  rw [hga, map_mul, map_intCast] at hact
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : K) ≠ 0)
  change (c : K) * σ a = (χI (galEquivZMod n K σ) : K) * ((c : K) * a) at hact
  simpa only [χI, mul_left_comm] using hact

section

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem galEquivZMod_arithFrob (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {p : ℕ} (hp : p.Prime) (hpn : p.Coprime n)
    (P : Ideal (𝓞 K)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    galEquivZMod n K σ = ZMod.unitOfCoprime p hpn := by
  have hn : (n : 𝓞 K) ∉ P := by
    intro hn
    have hn' : (n : ℤ) ∈ P.under ℤ := by simpa [Ideal.under, Ideal.mem_comap] using hn
    rw [hP, Ideal.mem_span_singleton] at hn'
    exact hp.not_dvd_one (hpn ▸ Nat.dvd_gcd (dvd_refl p) (Int.natCast_dvd_natCast.mp hn'))
  have hc : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hP, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  let ζ := (zeta_spec n ℚ K).toInteger
  have hζ : IsPrimitiveRoot ζ n := (zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  have he : ζ ^ (galEquivZMod n K σ).val.val = ζ ^ p := by
    rw [← galEquivZMod_smul_of_pow_eq n K σ hζ.pow_eq_one]
    simpa only [hc, MulSemiringAction.toAlgHom_apply] using hσ.apply_of_pow_eq_one hζ.pow_eq_one hn
  have hmod := (hζ.isOfFinOrder (NeZero.ne n)).pow_inj_mod.mp he
  rw [← hζ.eq_orderOf] at hmod
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (galEquivZMod n K σ).val]
  exact (ZMod.natCast_eq_natCast_iff' _ _ n).mpr hmod

theorem arithFrob_map_character_eigenvector (n m : ℕ) [NeZero n] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] (hdiv : n ∣ m)
    (χ : DirichletCharacter ℤ n) (a : K)
    (ha : ∀ τ : Gal(K/ℚ), τ a = (χ (galEquivZMod n K τ) : K) * a)
    {p : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    (P : Ideal (𝓞 L)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    σ (algebraMap K L a) = (χ p : L) * algebraMap K L a := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  rw [← AlgEquiv.restrictNormal_commutes, ha, map_mul, map_intCast]
  congr 2
  rw [galEquivZMod_restrictNormal_apply m L K hdiv σ,
    galEquivZMod_arithFrob m L hp hpm P hP σ hσ]
  simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hdiv]

theorem exists_squarefree_generator_frobenius_sign (n m : ℕ) [NeZero n] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] (hdiv : n ∣ m)
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ (p : ℕ), p.Prime → p.Coprime m →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 →
            σ (algebraMap K L a) = -algebraMap K L a := by
  obtain ⟨d, a, hd, hbound, hddiv, hdns, ha, hint, hadj, hact⟩ :=
    exists_squarefree_characterField_generator (K := K) χ hχ hprim hne
  refine ⟨d, a, hd, hbound, hddiv, hdns, ha, hint, hadj, ?_⟩
  intro p hp hpm P hP σ hσ hχp
  have hi : integerCharacter χ hχ (p : ZMod n) = -1 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_neg, Int.cast_one] using
      (integerCharacter_cast χ hχ (p : ZMod n)).trans hχp
  have he := arithFrob_map_character_eigenvector n m K L hdiv
    (integerCharacter χ hχ) a hact hp hpm P hP σ hσ
  simpa only [hi, Int.cast_neg, Int.cast_one, neg_one_mul] using he

end

section

open NumberField IsCyclotomicExtension

noncomputable def cyclotomicDivisorField (n m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L] :
    IntermediateField ℚ L :=
  IntermediateField.adjoin ℚ {zeta m ℚ L ^ (m / n)}

theorem cyclotomicDivisorField_isCyclotomicExtension (n m : ℕ) [NeZero n] [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L] (hdiv : n ∣ m) :
    IsCyclotomicExtension {n} ℚ (cyclotomicDivisorField n m L) := by
  have hζ : IsPrimitiveRoot (zeta m ℚ L ^ (m / n)) n :=
    IsPrimitiveRoot.pow (NeZero.pos m) (zeta_spec m ℚ L) (Nat.div_mul_cancel hdiv).symm
  exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ

end

theorem primitive_eighth_root_difference_sq {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 8) : (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h4 : ζ ^ 4 = -1 := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    simpa using hζ.pow_div_gcd 4 (by decide : Nat.gcd 8 4 ≠ 0)
  linear_combination (ζ ^ 2 - 2) * h4

end WeightedTorusJets

open scoped Pointwise

end SiegelZeros

end OAI
