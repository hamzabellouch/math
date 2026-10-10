import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import OAI.NumberTheory.SiegelZeros.Characters.CharacterLegendre

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W09

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem exists_unit_apply_neg_one (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    ∃ u : (ZMod q)ˣ, χ u = -1 := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hn
  rcases hq u with h | h | h
  · exact ((u.isUnit.map χ).ne_zero h).elim
  · exact (hu h).elim
  · exact ⟨u, h⟩

omit [NeZero q] in
theorem quadratic_unitHom_range (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    χ.toUnitHom.range = rootsOfUnity 2 ℂ := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_rootsOfUnity, Units.ext_iff]
    change χ u ^ 2 = 1
    rcases hq u with h | h | h
    · exact ((u.isUnit.map χ).ne_zero h).elim
    · simp [h]
    · simp [h]
  · intro hz
    have hs : (z : ℂ) ^ 2 = 1 := (mem_rootsOfUnity' 2 z).mp hz
    rcases sq_eq_one_iff.mp hs with h | h
    · refine ⟨1, ?_⟩
      apply Units.ext
      simpa using h.symm
    · obtain ⟨u, hu⟩ := exists_unit_apply_neg_one χ hq hn
      refine ⟨u, ?_⟩
      apply Units.ext
      exact hu.trans h.symm

omit [NeZero q] in
theorem quadratic_kernel_index (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    χ.toUnitHom.ker.index = 2 := by
  rw [Subgroup.index_ker, quadratic_unitHom_range χ hq hn,
    Complex.card_rootsOfUnity]

theorem actualCyclotomicField_isCyclotomic (q : ℕ) [NeZero q] :
    IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := by
  let nonzeroRational : NeZero (q : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne q)⟩
  exact CyclotomicField.isCyclotomicExtension q ℚ

noncomputable def cyclotomicGaloisEquiv (q : ℕ) [NeZero q] :
    (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) ≃* (ZMod q)ˣ := by
  letI := actualCyclotomicField_isCyclotomic q
  exact IsCyclotomicExtension.autEquivPow (CyclotomicField q ℚ)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos q))

noncomputable def cyclotomicCharacter (χ : DirichletCharacter ℂ q) :
    (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) →* ℂˣ :=
  χ.toUnitHom.comp (cyclotomicGaloisEquiv q).toMonoidHom

noncomputable def quadraticFixedField (χ : DirichletCharacter ℂ q) :
    IntermediateField ℚ (CyclotomicField q ℚ) :=
  IntermediateField.fixedField (cyclotomicCharacter χ).ker

theorem cyclotomicCharacter_kernel_index (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    (cyclotomicCharacter χ).ker.index = 2 := by
  rw [Subgroup.index_ker]
  have hr : (cyclotomicCharacter χ).range = χ.toUnitHom.range := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨cyclotomicGaloisEquiv q g, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨(cyclotomicGaloisEquiv q).symm u, ?_⟩
      simp [cyclotomicCharacter]
  rw [hr, quadratic_unitHom_range χ hq hn, Complex.card_rootsOfUnity]

theorem quadraticFixedField_finrank (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    Module.finrank ℚ (quadraticFixedField χ) = 2 := by
  let cyclotomicExtension := actualCyclotomicField_isCyclotomic q
  let galoisExtension : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  change (IntermediateField.fixingSubgroup
    (IntermediateField.fixedField (cyclotomicCharacter χ).ker)).index = 2
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact cyclotomicCharacter_kernel_index χ hq hn

end SiegelZerosAwei.W09



namespace SiegelZerosAwei.W09

open Polynomial

variable {q : ℕ} [NeZero q]

theorem characterField_finiteDimensional (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    FiniteDimensional ℚ (characterField χ) := by
  exact IntermediateField.adjoin.finiteDimensional
    ((characterGaussSum_isIntegral χ hp hq).tower_top : IsIntegral ℚ _)

theorem finrank_adjoin_le_two_of_sq_eq_rat (z : ℂ) (r : ℚ)
    (hz : z ^ 2 = (r : ℂ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {z}) ≤ 2 := by
  let p : ℚ[X] := X ^ 2 - C r
  have hm : p.Monic := monic_X_pow_sub_C r (by decide : 2 ≠ 0)
  have he : aeval z p = 0 := by simp [p, hz]
  have hi : IsIntegral ℚ z := ⟨p, hm, by simpa only [aeval_def] using he⟩
  rw [IntermediateField.adjoin.finrank hi]
  have hd := Polynomial.natDegree_le_natDegree
    (minpoly.degree_le_of_ne_zero ℚ z hm.ne_zero he)
  simpa [p] using hd

theorem characterField_finrank_le_two (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    Module.finrank ℚ (characterField χ) ≤ 2 := by
  have hs := characterGaussSum_sq χ hp hq
  rcases hq (-1) with h | h | h
  · exact finrank_adjoin_le_two_of_sq_eq_rat _ 0 (by simpa [h] using hs)
  · exact finrank_adjoin_le_two_of_sq_eq_rat _ q (by simpa [h] using hs)
  · exact finrank_adjoin_le_two_of_sq_eq_rat _ (-q) (by simpa [h] using hs)

theorem characterGaussSum_norm_sq (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ‖characterGaussSum χ‖ ^ 2 = (q : ℝ) := by
  have hs := congrArg norm (characterGaussSum_sq χ hp hq)
  have hn : ‖χ (-1)‖ = 1 := by
    simpa using χ.unit_norm_eq_one (-1 : (ZMod q)ˣ)
  simpa only [norm_pow, norm_mul, hn, one_mul, Complex.norm_natCast] using hs

end SiegelZerosAwei.W09



namespace SiegelZerosAwei.W09

variable {q : ℕ} [NeZero q]

noncomputable def standardRoot (q : ℕ) [NeZero q] : ℂ :=
  ZMod.stdAddChar (1 : ZMod q)

noncomputable def complexCyclotomicField (q : ℕ) [NeZero q] : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {standardRoot q}

theorem standardRoot_isPrimitive (q : ℕ) [NeZero q] :
    IsPrimitiveRoot (standardRoot q) q := by
  have hs := ZMod.stdAddChar_coe (N := q) (1 : ℤ)
  simp only [Int.cast_one, mul_one] at hs
  rw [standardRoot, hs]
  exact Complex.isPrimitiveRoot_exp q (NeZero.ne q)

theorem standardAddChar_eq_pow (j : ZMod q) :
    ZMod.stdAddChar j = standardRoot q ^ j.val := by
  rw [standardRoot, ← AddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]

theorem standardAddChar_mem (j : ZMod q) :
    ZMod.stdAddChar j ∈ complexCyclotomicField q := by
  rw [standardAddChar_eq_pow]
  have hroot : standardRoot q ∈ complexCyclotomicField q :=
    IntermediateField.subset_adjoin ℚ {standardRoot q} (Set.mem_singleton (standardRoot q))
  exact (complexCyclotomicField q).pow_mem hroot j.val

noncomputable def liftedAddChar (j : ZMod q) : complexCyclotomicField q :=
  ⟨ZMod.stdAddChar j, standardAddChar_mem j⟩

theorem quadraticCharacterValue_mem (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (j : ZMod q) : χ j ∈ complexCyclotomicField q := by
  rcases hq j with h | h | h
  · rw [h]; exact (complexCyclotomicField q).zero_mem
  · rw [h]; exact (complexCyclotomicField q).one_mem
  · rw [h]; exact (complexCyclotomicField q).neg_mem (complexCyclotomicField q).one_mem

noncomputable def liftedCharacterValue (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (j : ZMod q) : complexCyclotomicField q :=
  ⟨χ j, quadraticCharacterValue_mem χ hq j⟩

noncomputable def liftedGaussSum (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) : complexCyclotomicField q :=
  ∑ j : ZMod q, liftedCharacterValue χ hq j * liftedAddChar j

@[simp] theorem coe_liftedGaussSum (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) :
    (liftedGaussSum χ hq : ℂ) = characterGaussSum χ := by
  simp [liftedGaussSum, liftedCharacterValue, liftedAddChar, characterGaussSum, gaussSum]

theorem standardRoot_lift_isPrimitive :
    IsPrimitiveRoot (liftedAddChar (1 : ZMod q)) q := by
  apply (standardRoot_isPrimitive q).of_map_of_injective
    (f := (complexCyclotomicField q).val) (complexCyclotomicField q).val.injective

theorem complexCyclotomicField_isCyclotomic :
    IsCyclotomicExtension {q} ℚ (complexCyclotomicField q) := by
  change IsCyclotomicExtension {q} ℚ (complexCyclotomicField q).toSubalgebra
  rw [complexCyclotomicField,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (((standardRoot_isPrimitive q).isIntegral (NeZero.pos q)).tower_top :
        IsIntegral ℚ (standardRoot q)).isAlgebraic]
  exact (standardRoot_isPrimitive q).adjoin_isCyclotomicExtension ℚ

theorem automorphism_liftedCharacterValue
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q)
    (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) (j : ZMod q) :
    g (liftedCharacterValue χ hq j) = liftedCharacterValue χ hq j := by
  rcases hq j with h | h | h
  · have hl : liftedCharacterValue χ hq j = 0 := Subtype.ext h
    simp [hl]
  · have hl : liftedCharacterValue χ hq j = 1 := Subtype.ext h
    simp [hl]
  · have hl : liftedCharacterValue χ hq j = -1 := Subtype.ext h
    simp [hl]

theorem automorphism_liftedAddChar
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q)
    (u : (ZMod q)ˣ)
    (hgen : g (liftedAddChar (1 : ZMod q)) = liftedAddChar (u : ZMod q))
    (j : ZMod q) : g (liftedAddChar j) = liftedAddChar ((u : ZMod q) * j) := by
  have hp : liftedAddChar j = liftedAddChar (1 : ZMod q) ^ j.val := by
    apply Subtype.ext
    exact standardAddChar_eq_pow j
  rw [hp, map_pow, hgen]
  apply Subtype.ext
  change ZMod.stdAddChar (u : ZMod q) ^ j.val = ZMod.stdAddChar ((u : ZMod q) * j)
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

theorem automorphism_liftedGaussSum
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q)
    (u : (ZMod q)ˣ)
    (hgen : g (liftedAddChar (1 : ZMod q)) = liftedAddChar (u : ZMod q))
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    (g (liftedGaussSum χ hq) : ℂ) = χ u * characterGaussSum χ := by
  have he : (g (liftedGaussSum χ hq) : ℂ) =
      gaussSum χ (ZMod.stdAddChar.mulShift (u : ZMod q)) := by
    simp only [liftedGaussSum, map_sum, map_mul,
      automorphism_liftedCharacterValue, automorphism_liftedAddChar g u hgen]
    simp [gaussSum, liftedCharacterValue, liftedAddChar, AddChar.mulShift_apply]
  rw [he, gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hp, hq.inv]
  rfl

noncomputable def complexCyclotomicGaloisEquiv :
    (complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) ≃* (ZMod q)ˣ := by
  letI : IsCyclotomicExtension {q} ℚ (complexCyclotomicField q) :=
    complexCyclotomicField_isCyclotomic (q := q)
  let e : (complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) ≃* (ZMod q)ˣ :=
    IsCyclotomicExtension.autEquivPow (complexCyclotomicField q)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos q))
  let f : (complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) →* (ZMod q)ˣ :=
    (standardRoot_lift_isPrimitive (q := q)).autToPow ℚ
  have hf : Function.Injective f :=
    (standardRoot_lift_isPrimitive (q := q)).autToPow_injective ℚ
  have hsurj : Function.Surjective f := by
    have hh : Function.Injective (fun u : (ZMod q)ˣ ↦ f (e.symm u)) := hf.comp e.symm.injective
    have hh' := Finite.surjective_of_injective hh
    intro u
    obtain ⟨v, hv⟩ := hh' u
    exact ⟨e.symm v, hv⟩
  exact MulEquiv.ofBijective f ⟨hf, hsurj⟩

theorem complexCyclotomicGaloisEquiv_apply
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) :
    complexCyclotomicGaloisEquiv (q := q) g =
      (standardRoot_lift_isPrimitive (q := q)).autToPow ℚ g := rfl

theorem complexCyclotomicGaloisEquiv_spec
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) :
    g (liftedAddChar (1 : ZMod q)) =
      liftedAddChar (complexCyclotomicGaloisEquiv (q := q) g : ZMod q) := by
  rw [complexCyclotomicGaloisEquiv_apply (q := q)]
  rw [← (standardRoot_lift_isPrimitive (q := q)).autToPow_spec ℚ g]
  apply Subtype.ext
  exact (standardAddChar_eq_pow _).symm

noncomputable def complexCyclotomicCharacter (χ : DirichletCharacter ℂ q) :
    (complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) →* ℂˣ :=
  χ.toUnitHom.comp (complexCyclotomicGaloisEquiv (q := q)).toMonoidHom

theorem gaussSum_galois_action
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) :
    (g (liftedGaussSum χ hq) : ℂ) =
      (complexCyclotomicCharacter χ g : ℂ) * characterGaussSum χ := by
  exact automorphism_liftedGaussSum g (complexCyclotomicGaloisEquiv (q := q) g)
    (complexCyclotomicGaloisEquiv_spec (q := q) g) χ hp hq

theorem fixes_gaussSum_iff_kernel
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hq : χ.IsQuadratic)
    (g : complexCyclotomicField q ≃ₐ[ℚ] complexCyclotomicField q) :
    g (liftedGaussSum χ hq) = liftedGaussSum χ hq ↔
      g ∈ (complexCyclotomicCharacter χ).ker := by
  rw [Subtype.ext_iff, coe_liftedGaussSum, gaussSum_galois_action χ hp hq]
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (complexCyclotomicCharacter χ g : ℂ) * characterGaussSum χ =
      characterGaussSum χ ↔ (complexCyclotomicCharacter χ g : ℂ) = 1
  exact mul_eq_right₀ (characterGaussSum_ne_zero χ hp hq)

end SiegelZerosAwei.W09



namespace SiegelZerosAwei.W09

variable {q : ℕ} [NeZero q]

noncomputable def liftedGaussField (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) :
    IntermediateField ℚ (complexCyclotomicField q) :=
  IntermediateField.adjoin ℚ {liftedGaussSum χ hq}

theorem liftedGaussField_fixingSubgroup (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    (liftedGaussField χ hq).fixingSubgroup = (complexCyclotomicCharacter χ).ker := by
  ext g
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    apply (fixes_gaussSum_iff_kernel χ hp hq g).mp
    exact h _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
  · intro hg
    have hτ := (fixes_gaussSum_iff_kernel χ hp hq g).mpr hg
    have he : g.toAlgHom.comp (liftedGaussField χ hq).val =
        (liftedGaussField χ hq).val := by
      apply IntermediateField.adjoin_algHom_ext ℚ
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hτ
    intro x hx
    exact DFunLike.congr_fun he ⟨x, hx⟩

theorem liftedGaussField_eq_fixedField (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    liftedGaussField χ hq =
      IntermediateField.fixedField (complexCyclotomicCharacter χ).ker := by
  let cyclotomicExtension : IsCyclotomicExtension {q} ℚ (complexCyclotomicField q) :=
    complexCyclotomicField_isCyclotomic (q := q)
  let finiteDimension : FiniteDimensional ℚ (complexCyclotomicField q) :=
    IsCyclotomicExtension.finiteDimensional {q} ℚ (complexCyclotomicField q)
  let galoisExtension : IsGalois ℚ (complexCyclotomicField q) :=
    IsCyclotomicExtension.isGalois {q} ℚ (complexCyclotomicField q)
  rw [← liftedGaussField_fixingSubgroup χ hp hq]
  exact (IsGalois.fixedField_fixingSubgroup (liftedGaussField χ hq)).symm

theorem liftedGaussField_map (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) :
    (liftedGaussField χ hq).map (complexCyclotomicField q).val = characterField χ := by
  simpa only [liftedGaussField, characterField, Set.image_singleton,
    IntermediateField.coe_val, coe_liftedGaussSum] using
    (IntermediateField.adjoin_map ℚ {liftedGaussSum χ hq}
      (complexCyclotomicField q).val)

theorem characterField_eq_fixedField_map (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    characterField χ =
      (IntermediateField.fixedField (complexCyclotomicCharacter χ).ker).map
        (complexCyclotomicField q).val := by
  rw [← liftedGaussField_eq_fixedField χ hp hq, liftedGaussField_map]

theorem complexCyclotomicCharacter_kernel_index (χ : DirichletCharacter ℂ q)
    (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    (complexCyclotomicCharacter χ).ker.index = 2 := by
  rw [Subgroup.index_ker]
  have hr : (complexCyclotomicCharacter χ).range = χ.toUnitHom.range := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨complexCyclotomicGaloisEquiv (q := q) g, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨(complexCyclotomicGaloisEquiv (q := q)).symm u, ?_⟩
      simp [complexCyclotomicCharacter]
  rw [hr, quadratic_unitHom_range χ hq hn, Complex.card_rootsOfUnity]

theorem characterField_finrank (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    Module.finrank ℚ (characterField χ) = 2 := by
  let cyclotomicExtension : IsCyclotomicExtension {q} ℚ (complexCyclotomicField q) :=
    complexCyclotomicField_isCyclotomic (q := q)
  let galoisExtension : IsGalois ℚ (complexCyclotomicField q) :=
    IsCyclotomicExtension.isGalois {q} ℚ (complexCyclotomicField q)
  have hi : Module.finrank ℚ (liftedGaussField χ hq) = 2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      liftedGaussField_fixingSubgroup χ hp hq,
      complexCyclotomicCharacter_kernel_index χ hq hn]
  let e : liftedGaussField χ hq ≃ₐ[ℚ] characterField χ :=
    (IntermediateField.equivMap (liftedGaussField χ hq)
      (complexCyclotomicField q).val).trans
        (IntermediateField.equivOfEq (liftedGaussField_map χ hq))
  exact e.toLinearEquiv.finrank_eq.symm.trans hi

end SiegelZerosAwei.W09


end SiegelZeros

end OAI
