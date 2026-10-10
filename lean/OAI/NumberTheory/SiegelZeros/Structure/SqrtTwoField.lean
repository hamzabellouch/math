import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.QuadraticAdjoinBasis

namespace OAI

namespace SiegelZeros

open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets

theorem primitive_mod_four_character_neg_one (χ : DirichletCharacter ℤ 4)
    (hprim : χ.IsPrimitive) : χ (-1) = -1 := by
  have hne : χ ≠ 1 := by
    intro h
    have hc := hprim
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hc
    norm_num at hc
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  have hu_cases : u = 1 ∨ u = -1 := by
    exact (by decide : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1) u
  rcases hu_cases with rfl | rfl
  · simp at hu
  · have hval := Int.isUnit_eq_one_or ((isUnit_neg_one : IsUnit (-1 : ZMod 4)).map χ)
    exact hval.resolve_left (by simpa only [Units.val_neg, Units.val_one] using hu)



theorem primitive_four_mul_exists_odd_part {u : ℕ} [NeZero u] (hu : Odd u)
    (χ : DirichletCharacter ℤ (4 * u)) (hprim : χ.IsPrimitive) :
    ∃ η : DirichletCharacter ℤ u, η.IsPrimitive ∧ χ (-1) = -η (-1) := by
  have hc : Nat.Coprime 4 u := by
    simpa using hu.coprime_two_left.pow_left 2
  refine ⟨crtCharacterRight hc χ, crtCharacterRight_isPrimitive hc χ hprim, ?_⟩
  rw [crtCharacter_neg_one hc χ, primitive_mod_four_character_neg_one _
    (crtCharacterLeft_isPrimitive hc χ hprim), neg_one_mul]



theorem primitive_four_mul_quadratic_signed_part_mod_four {u : ℕ} [NeZero u]
    (χ : DirichletCharacter ℤ (4 * u)) (hprim : χ.IsPrimitive) (hu : Odd u) :
    (χ (-1) * (u : ℤ)) % 4 = 3 := by
  obtain ⟨η, hηprim, hneg⟩ := primitive_four_mul_exists_odd_part hu χ hprim
  have hηquad : η.IsQuadratic := by
    intro a
    by_cases ha : IsUnit a
    · exact Or.inr (Int.isUnit_eq_one_or (ha.map η))
    · exact Or.inl (η.map_nonunit ha)
  have hodd := primitive_odd_quadratic_signed_level_mod_four η hηquad hηprim hu
  rw [hneg, neg_mul]
  omega



theorem fundamentalDiscr_eight_odd_case {D d : ℤ} {u : ℕ} (hu : Odd u)
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d) (hD : D.natAbs = 8 * u) :
    Int.IsFundamentalDiscr D := by
  rcases hDd with rfl | hDd
  · have hf := Nat.squarefree_iff_prime_squarefree.mp (Int.squarefree_natAbs.mpr hd)
    exact (hf 2 Nat.prime_two ⟨2 * u, by omega⟩).elim
  · rw [hDd, Int.isFundamentalDiscr_four_mul]
    refine ⟨hd, Or.inl ?_⟩
    have heq : 4 * d.natAbs = 8 * u := by simpa [hDd, Int.natAbs_mul] using hD
    have hn : d.natAbs = 2 * u := by omega
    have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) hn
    rw [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_ofNat] at hh
    obtain ⟨k, hk⟩ := hu
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h] at hh
      omega
    · rw [abs_of_nonpos h] at hh
      omega

theorem fundamentalDiscr_four_parity_case {D d s : ℤ} {u : ℕ}
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d)
    (hD : D = s * (4 * (u : ℤ))) (hparity : (s * (u : ℤ)) % 4 = 3) :
    Int.IsFundamentalDiscr D := by
  rcases hDd with rfl | hDd
  · have hf := Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
    apply (hf ?_).elim
    refine ⟨s * (u : ℤ), ?_⟩
    rw [hD]
    ring
  · rw [hDd, Int.isFundamentalDiscr_four_mul]
    refine ⟨hd, Or.inr ?_⟩
    have heq : d = s * (u : ℤ) := by
      apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
      calc
        4 * d = D := hDd.symm
        _ = s * (4 * (u : ℤ)) := hD
        _ = 4 * (s * (u : ℤ)) := by ring
    rwa [heq]



open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem exists_signed_squarefree_characterField_generator {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ (D d : ℤ) (a : K), D = integerCharacter χ hχ (-1) * (n : ℤ) ∧
      D.natAbs = n ∧ Squarefree d ∧ (D = d ∨ D = 4 * d) ∧
      d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
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
  have hDchar : D = χI (-1) * (n : ℤ) := by
    apply Int.cast_injective (α := K)
    push_cast
    calc
      (D : K) = gaussSum χK e ^ 2 := hgD.symm
      _ = χK (-1) * (n : K) := primitive_quadratic_gaussSum_sq hpK hK he
      _ = (χI (-1) : K) * (n : K) := rfl
  have hcases := primitive_quadratic_radicand_eq_or_four_mul χ hχ hprim hDabs hdc
  refine ⟨D, d, a, hDchar, hDabs, hd, hcases, hDabs ▸ hbound, hdiv, hnsq,
    ha, hint, hadjχ, ?_⟩
  intro σ
  have hact := cyclotomic_gaussSum_action χK hK e σ
  rw [hga, map_mul, map_intCast] at hact
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : K) ≠ 0)
  change (c : K) * σ a = (χI (galEquivZMod n K σ) : K) * ((c : K) * a) at hact
  simpa only [χI, mul_left_comm] using hact

end WeightedTorusJets

namespace WeightedTorusJets

open Module NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem normalized_signed_conductor_isFundamentalDiscr {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {D d : ℤ} (hDsign : D = χ (-1) * (q : ℤ)) (hDabs : D.natAbs = q)
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d) : Int.IsFundamentalDiscr D := by
  obtain ⟨u, hu, hsfu, hq | hq | hq⟩ := primitive_quadratic_conductor_shape χ hχ hprim
  · have hodd : Odd q := hq ▸ hu
    apply Int.isFundamentalDiscr_iff_squarefree.mpr
    refine Or.inl ⟨?_, Int.squarefree_natAbs.mp ?_⟩
    · rw [hDsign]
      exact primitive_odd_quadratic_signed_level_mod_four χ hχ hprim hodd
    · rwa [hDabs, hq]
  · subst hq
    let : NeZero u := ⟨hsfu.ne_zero⟩
    exact fundamentalDiscr_four_parity_case hd hDd
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDsign)
      (primitive_four_mul_quadratic_signed_part_mod_four χ hprim hu)
  · exact fundamentalDiscr_eight_odd_case hu hd hDd (hDabs.trans hq)

theorem characterField_discr_eq_signed_conductor {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    NumberField.discr (characterField n K ℂ χ) = integerCharacter χ hχ (-1) * (n : ℤ) := by
  obtain ⟨D, d, a, hDsign, hDabs, hd, hDd, _, _, _, ha, hint, hadj, _⟩ :=
    exists_signed_squarefree_characterField_generator (K := K) χ hχ hprim hne
  have hfund := normalized_signed_conductor_isFundamentalDiscr (integerCharacter χ hχ)
    (integerCharacter_isQuadratic χ hχ) (integerCharacter_isPrimitive χ hχ hprim)
    hDsign hDabs hd hDd
  have hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2 := by
    rw [hadj]
    exact characterField_finrank n K ℂ χ hχ hne
  have hai : IsIntegral ℚ a := hint.tower_top
  let u := quadraticAdjoinBasis a hai hdim
  let a' := IntermediateField.AdjoinSimple.gen ℚ a
  have hu : (u : Fin 2 → IntermediateField.adjoin ℚ {a}) = ![1, a'] := by
    funext i
    exact quadraticAdjoinBasis_apply a hai hdim i
  have ha' : a' ^ 2 = (d : IntermediateField.adjoin ℚ {a}) := by
    apply Subtype.ext
    exact ha
  have hdiscr : NumberField.discr (IntermediateField.adjoin ℚ {a}) = D := by
    rcases hDd with hDd | hDd
    · rw [hDd] at hfund ⊢
      have hd4 : d % 4 ≠ 0 := by
        intro h
        exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
          (by simpa using Int.dvd_of_emod_eq_zero h)
      exact numberField_discr_quadratic_eq_self u a' d hu ha' hd
        (hfund.emod_four_eq_zero_or_one.resolve_left hd4)
    · rw [hDd] at hfund ⊢
      exact numberField_discr_quadratic_eq_four_mul u a' d hu ha' hd
        (Int.isFundamentalDiscr_four_mul.mp hfund).2
  rw [hadj, hDsign] at hdiscr
  exact hdiscr

end WeightedTorusJets


namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem characterField_changeLevel_discr_eq_signed_conductor {q m : ℕ}
    [NeZero q] [NeZero m] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L]
    (hdiv : q ∣ m) (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    NumberField.discr (characterField m L ℂ (DirichletCharacter.changeLevel hdiv χ)) =
      integerCharacter χ hχ (-1) * (q : ℤ) := by
  let K := cyclotomicDivisorField q m L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q m L hdiv
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  rw [characterField_changeLevel q K ℂ L hdiv χ hχ]
  exact (NumberField.discr_eq_discr_of_algEquiv (characterField q K ℂ χ)
    ((characterField q K ℂ χ).equivMap (IsScalarTower.toAlgHom ℚ K L))).symm.trans
      (characterField_discr_eq_signed_conductor χ hχ hprim hne)

theorem characterField_changeLevel_discr_natAbs {q m : ℕ}
    [NeZero q] [NeZero m] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L]
    (hdiv : q ∣ m) (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    (NumberField.discr
      (characterField m L ℂ (DirichletCharacter.changeLevel hdiv χ))).natAbs = q := by
  rw [characterField_changeLevel_discr_eq_signed_conductor hdiv χ hχ hprim hne]
  rcases Int.isUnit_eq_one_or ((isUnit_neg_one : IsUnit (-1 : ZMod q)).map
    (integerCharacter χ hχ)) with h | h <;> simp [h]

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

theorem quadraticAdjoin_discriminant {L : Type*} [Field L] [NumberField L]
    (a : L) (d : ℤ) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hns : ¬ IsSquare (d : ℚ)) :
    NumberField.discr (IntermediateField.adjoin ℚ {a}) =
      (if d % 4 = 1 then d else 4 * d) ∧
    Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
    (Algebra.IsUnramifiedIn (𝓞 (IntermediateField.adjoin ℚ {a}))
      (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1) := by
  let F := IntermediateField.adjoin ℚ {a}
  let A : F := IntermediateField.AdjoinSimple.gen ℚ a
  have hroot : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hi : IsIntegral ℚ a := IsIntegral.of_pow (by decide : 0 < 2)
    (hroot ▸ isIntegral_algebraMap)
  have hdim := finrank_adjoin_sqrt a (d : ℚ) hroot hns
  let u : Module.Basis (Fin 2) ℚ F := quadraticAdjoinBasis a hi hdim
  have hu : (u : Fin 2 → F) = ![1, A] := by
    funext i
    exact quadraticAdjoinBasis_apply a hi hdim i
  have hA : A ^ 2 = (d : F) := by
    apply Subtype.ext
    exact ha
  refine ⟨?_, isFundamentalDiscr_quadratic u A d hu hA hd,
    isUnramifiedIn_two_iff_radical_mod_four u A d hu hA hd⟩
  by_cases hd1 : d % 4 = 1
  · simp only [ite_eq_left hd1]
    exact numberField_discr_quadratic_eq_self u A d hu hA hd hd1
  · simp only [ite_eq_right hd1]
    have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    exact numberField_discr_quadratic_eq_four_mul u A d hu hA hd (by omega)



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

namespace WeightedTorusJets

open IsCyclotomicExtension IsCyclotomicExtension.Rat

noncomputable def sourceSqrtTwoField (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L] :
    IntermediateField ℚ L :=
  let ζ := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  IntermediateField.adjoin ℚ ({ζ - ζ ^ 3} : Set L)

theorem sourceSqrtTwoField_root_sq (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L] :
    let ζ := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
    (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  exact primitive_eighth_root_difference_sq
    ((zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm)

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem exists_auxiliary_sqrt_pair_of_field_ne (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IsIntegral ℤ a ∧ IsIntegral ℤ b ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} ∧
      ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 → σ a = -a := by
  have hqm : q ∣ 8 * q := dvd_mul_left q 8
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  let K := cyclotomicDivisorField q (8 * q) L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q (8 * q) L hqm
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  obtain ⟨d, aK, hd, hbound, hddiv, hdns, haK, _, hadjK, hsign⟩ :=
    exists_squarefree_generator_frobenius_sign q (8 * q) K L hqm χ hχ hprim hne
  let a : L := algebraMap K L aK
  have ha : a ^ 2 = (d : L) := by
    change (algebraMap K L aK) ^ 2 = _
    rw [← map_pow, haK, map_intCast]
  let ζ : L := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  have hζ : IsPrimitiveRoot ζ 8 :=
    (zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm
  let b := ζ - ζ ^ 3
  have hb : b ^ 2 = 2 := primitive_eighth_root_difference_sq hζ
  have hadj : IntermediateField.adjoin ℚ {a} =
      characterField (8 * q) L ℂ (DirichletCharacter.changeLevel hqm χ) := by
    rw [characterField_changeLevel q K ℂ L hqm χ hχ, ← hadjK,
      IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hneq : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} := by
    intro heq
    exact hfield (hadj.symm.trans heq)
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, ?_, ?_, hadj, hneq, ?_⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [ha]
    exact isIntegral_algebraMap
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [hb]
    exact isIntegral_natCast 2
  · intro p hp hpn P hP σ hσ hχp
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    exact hsign p hp (h8.mul_right hq) P hP σ hσ hχp

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

theorem source_biquadratic_arithmetic_of_field_ne (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  have hquad := real_character_isQuadratic χ hreal
  obtain ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, _, _, hadj, hfields, hsign⟩ :=
    exists_auxiliary_sqrt_pair_of_field_ne q L χ hquad hprim hne hfield
  have haRat : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hbRat : b ^ 2 = algebraMap ℚ L (2 : ℚ) := by simpa using hb
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
  have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
  have hint := biquadratic_monomials_integral a' b' d 2 ha' (by simpa using hb')
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hdesc⟩ :=
    sqrtPair_frobenius_directions a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  obtain ⟨hformula, hfund, _⟩ := quadraticAdjoin_discriminant a d ha hd hdns
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, hadj, ?_, hfund, hformula, v, hv, ?_, ?_,
    σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  · rw [hadj]
    exact characterField_changeLevel_discr_natAbs (dvd_mul_left q 8) χ hquad hprim hne
  · intro i
    rw [hv]
    fin_cases i
    · exact hint.1
    · exact hint.2.1
    · exact hint.2.2.1
    · exact hint.2.2.2
  · exact finrank_adjoin_pair_sqrt a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  · intro p hp hpn hχp
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero (8 * q) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    have hpm : ¬ p ∣ 8 * q := hp.coprime_iff_not_dvd.mp (h8.mul_right hq)
    obtain ⟨φ, hfrob, hglobal⟩ := exists_cyclotomic_frobenius_congruence (8 * q) L p hpm
    obtain ⟨P, hP, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    exact hdesc p φ (hsign p hp hpn P hover.over.symm φ (hfrob P inferInstance hover) hχp) hglobal

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_biquadratic_arithmetic_canonical_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    let L := CyclotomicField (8 * q) ℚ
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  exact source_biquadratic_arithmetic_of_field_ne q (CyclotomicField (8 * q) ℚ)
    χ hreal hprim hne hfield

end WeightedTorusJets


end SiegelZeros

end OAI
