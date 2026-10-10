import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.SqrtTwoField

namespace OAI

namespace SiegelZeros

open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets

lemma exists_root_normalizing_automorphism {K L : Type*} [Field K] [Field L]
    [Algebra ℚ K] [Algebra ℚ L] (ν : K →ₐ[ℚ] L) (a b : K) (A B : L)
    (σ τ : K ≃ₐ[ℚ] K) (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b)
    (ha : (ν a) ^ 2 = A ^ 2) (hb : (ν b) ^ 2 = B ^ 2) :
    ∃ h : K ≃ₐ[ℚ] K, (h = 1 ∨ h = σ ∨ h = τ ∨ h = σ * τ) ∧
      ν (h a) = A ∧ ν (h b) = B := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with ha | ha <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with hb | hb
  · exact ⟨1, Or.inl rfl, ha, hb⟩
  · refine ⟨τ, Or.inr (Or.inr (Or.inl rfl)), ?_, ?_⟩
    · simpa [hτa] using ha
    · simp [hτb, hb]
  · refine ⟨σ, Or.inr (Or.inl rfl), ?_, ?_⟩
    · simp [hσa, ha]
    · simpa [hσb] using hb
  · refine ⟨σ * τ, Or.inr (Or.inr (Or.inr rfl)), ?_, ?_⟩
    · simp [AlgEquiv.mul_apply, hτa, hσa, ha]
    · simp [AlgEquiv.mul_apply, hτb, hσb, hb]

lemma exists_embedding_principal_roots {K : Type*} [Field K] [NumberField K]
    (a b : K) (d : ℤ) (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (σ τ : K ≃ₐ[ℚ] K) (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b) :
    ∃ ν : K →ₐ[ℚ] ℂ, ν a = Complex.sqrt (d : ℂ) ∧ ν b = (Real.sqrt 2 : ℂ) := by
  let : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
  let ν : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hA : (Complex.sqrt (d : ℂ)) ^ 2 = (d : ℂ) := by
    exact Complex.cpow_nat_inv_pow _ (by decide : (2 : ℕ) ≠ 0)
  have hB : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    rfl
  have ha' : (ν a) ^ 2 = (Complex.sqrt (d : ℂ)) ^ 2 := by
    rw [hA, ← map_pow, ha, map_intCast]
  have hb' : (ν b) ^ 2 = (Real.sqrt 2 : ℂ) ^ 2 := by
    rw [hB, ← map_pow, hb, map_ofNat]
  obtain ⟨h, _, hha, hhb⟩ := exists_root_normalizing_automorphism ν a b
    (Complex.sqrt (d : ℂ)) (Real.sqrt 2 : ℂ) σ τ hσa hσb hτa hτb ha' hb'
  exact ⟨ν.comp h.toAlgHom, hha, hhb⟩

lemma basis_fieldRange_eq_adjoin {K L : Type*} [Field K] [Field L]
    [Algebra ℚ K] [Algebra ℚ L] (v : Module.Basis (Fin 4) ℚ K) (a b : K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (ν : K →ₐ[ℚ] L) :
    ν.fieldRange = IntermediateField.adjoin ℚ ({ν a, ν b} : Set L) := by
  let F := IntermediateField.adjoin ℚ ({a, b} : Set K)
  have haF : a ∈ F := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hbF : b ∈ F := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hF : F = ⊤ := by
    apply top_unique
    intro x _
    rw [← v.sum_repr x]
    apply F.toSubalgebra.sum_mem
    intro i _
    apply F.toSubalgebra.smul_mem
    rw [hv]
    fin_cases i
    · exact F.one_mem
    · exact haF
    · exact hbF
    · exact F.mul_mem haF hbF
  have htop : (⊤ : IntermediateField ℚ K).map ν = ν.fieldRange := by
    ext x
    simp [IntermediateField.mem_map]
  rw [← htop, ← hF, IntermediateField.adjoin_map]
  simp

lemma exists_principal_root_field_equiv {K : Type*} [Field K] [NumberField K]
    (v : Module.Basis (Fin 4) ℚ K) (a b : K) (d : ℤ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (σ τ : K ≃ₐ[ℚ] K) (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b) :
    ∃ e : K ≃ₐ[ℚ] IntermediateField.adjoin ℚ
        ({Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} : Set ℂ),
      (e a : ℂ) = Complex.sqrt (d : ℂ) ∧ (e b : ℂ) = (Real.sqrt 2 : ℂ) := by
  obtain ⟨ν, hνa, hνb⟩ := exists_embedding_principal_roots a b d ha hb σ τ hσa hσb hτa hτb
  have hrange : ν.fieldRange = IntermediateField.adjoin ℚ
      ({Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} : Set ℂ) := by
    rw [basis_fieldRange_eq_adjoin v a b hv ν, hνa, hνb]
  refine ⟨ν.equivFieldRange.trans (IntermediateField.equivOfEq hrange), ?_, ?_⟩
  · simpa using hνa
  · simpa using hνb

end WeightedTorusJets

open scoped NumberField

namespace WeightedTorusJets

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

lemma integral_autCongr_equivariant (e : K ≃ₐ[ℚ] L) (σ : K ≃ₐ[ℚ] K) (x : 𝓞 K) :
    NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv (σ • x) =
      AlgEquiv.autCongr e σ • NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv x := by
  apply NumberField.RingOfIntegers.ext
  change e (σ (x : K)) = AlgEquiv.autCongr e σ (e (x : K))
  simp [AlgEquiv.autCongr_apply]

lemma integer_frobenius_transport (e : K ≃ₐ[ℚ] L) (σ : K ≃ₐ[ℚ] K) (p : ℕ)
    (hfrob : ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) :
    ∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - AlgEquiv.autCongr e σ • y := by
  let E := NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv
  intro y
  have h := map_dvd E (hfrob (E.symm y))
  dsimp only [E] at h
  simpa only [map_natCast, map_sub, map_pow, integral_autCongr_equivariant,
    RingEquiv.apply_symm_apply] using h

lemma integer_two_direction_frobenius_transport (e : K ≃ₐ[ℚ] L)
    (σ τ : K ≃ₐ[ℚ] K) (p : ℕ)
    (hfrob : (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) :
    (∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - AlgEquiv.autCongr e σ • y) ∨
      (∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p -
        (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) • y) := by
  rcases hfrob with h | h
  · exact Or.inl (integer_frobenius_transport e σ p h)
  · right
    simpa only [map_mul] using integer_frobenius_transport e (σ * τ) p h

lemma transported_sign_actions (e : K ≃ₐ[ℚ] L) (a b : K) (σ τ : K ≃ₐ[ℚ] K)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b) :
    AlgEquiv.autCongr e σ (e a) = -e a ∧
      AlgEquiv.autCongr e σ (e b) = e b ∧
      AlgEquiv.autCongr e τ (e a) = e a ∧
      AlgEquiv.autCongr e τ (e b) = -e b := by
  simp [AlgEquiv.autCongr_apply, hσa, hσb, hτa, hτb]

lemma transported_four_automorphisms (e : K ≃ₐ[ℚ] L) (σ τ : K ≃ₐ[ℚ] K)
    (hcard : Nat.card (K ≃ₐ[ℚ] K) = 4)
    (hall : ∀ f : K ≃ₐ[ℚ] K, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ)
    (hcomm : ∀ f g : K ≃ₐ[ℚ] K, Commute f g) :
    Nat.card (L ≃ₐ[ℚ] L) = 4 ∧
      (∀ f : L ≃ₐ[ℚ] L, f = 1 ∨ f = AlgEquiv.autCongr e σ ∨
        f = AlgEquiv.autCongr e τ ∨ f = AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) ∧
      (∀ f g : L ≃ₐ[ℚ] L, Commute f g) := by
  refine ⟨(Nat.card_congr (AlgEquiv.autCongr e).toEquiv).symm.trans hcard, ?_, ?_⟩
  · intro f
    obtain ⟨g, rfl⟩ := (AlgEquiv.autCongr e).surjective f
    rcases hall g with h | h | h | h <;> simp only [h, map_one, map_mul, true_or, or_true]
  · intro f g
    obtain ⟨f', rfl⟩ := (AlgEquiv.autCongr e).surjective f
    obtain ⟨g', rfl⟩ := (AlgEquiv.autCongr e).surjective g
    exact (hcomm f' g').map (AlgEquiv.autCongr e).toMonoidHom

end WeightedTorusJets

namespace WeightedTorusJets

theorem adjoin_simple_eq_of_sq_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    {a b : E} (h : a ^ 2 = b ^ 2) :
    IntermediateField.adjoin F {a} = IntermediateField.adjoin F {b} := by
  rcases eq_or_eq_neg_of_sq_eq_sq a b h with hab | hab
  · rw [hab]
  · subst a
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      simpa using (IntermediateField.adjoin F {b}).neg_mem
        (IntermediateField.mem_adjoin_simple_self F b)
    · apply IntermediateField.adjoin_le_iff.mpr
      simpa using (IntermediateField.adjoin F {-b}).neg_mem
        (IntermediateField.mem_adjoin_simple_self F (-b))

theorem adjoin_sqrt_two_map {L : Type*} [Field L] [CharZero L]
    (ν : L →ₐ[ℚ] ℂ) (b : L) (hb : b ^ 2 = 2) :
    (IntermediateField.adjoin ℚ {b}).map ν =
      IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} := by
  rw [IntermediateField.adjoin_map, Set.image_singleton]
  apply adjoin_simple_eq_of_sq_eq
  rw [← map_pow, hb, map_ofNat]
  have h : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h.symm

theorem sqrt_two_field_exclusion_map_iff {L : Type*} [Field L] [CharZero L]
    (F : IntermediateField ℚ L) (ν : L →ₐ[ℚ] ℂ) (b : L) (hb : b ^ 2 = 2) :
    F.map ν ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} ↔
      F ≠ IntermediateField.adjoin ℚ {b} := by
  rw [← adjoin_sqrt_two_map ν b hb]
  constructor
  · intro h heq
    exact h (congrArg (fun E : IntermediateField ℚ L => E.map ν) heq)
  · intro h heq
    exact h (IntermediateField.map_injective ν heq)

theorem sourceSqrtTwoField_exclusion_map_iff (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    (F : IntermediateField ℚ L) (ν : L →ₐ[ℚ] ℂ) :
    F.map ν ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} ↔
      F ≠ sourceSqrtTwoField q L := by
  exact sqrt_two_field_exclusion_map_iff F ν _ (sourceSqrtTwoField_root_sq q L)



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_biquadratic_arithmetic_principal_of_field_ne (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ d : ℤ, Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧ ¬ IsSquare (d : ℚ) ∧
      Int.IsFundamentalDiscr (if d % 4 = 1 then d else 4 * d) ∧
      (if d % 4 = 1 then d else 4 * d).natAbs = q ∧
      let Kχ := IntermediateField.adjoin ℚ ({Complex.sqrt (d : ℂ)} : Set ℂ)
      let K := IntermediateField.adjoin ℚ
        ({Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} : Set ℂ)
      let a : K := ⟨Complex.sqrt (d : ℂ), IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b : K := ⟨(Real.sqrt 2 : ℂ), IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ hKχ : NumberField Kχ, ∃ hK : NumberField K,
      letI := hKχ
      letI := hK
      NumberField.discr Kχ = (if d % 4 = 1 then d else 4 * d) ∧
      Kχ ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} ∧ IsGalois ℚ K ∧
      (∃ ν : CyclotomicField (8 * q) ℚ →ₐ[ℚ] ℂ,
        (characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
          (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)).map ν = Kχ) ∧
      ∃ v : Module.Basis (Fin 4) ℚ K,
        (∀ i, v i = ![1, a, b, a * b] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ K = 4 ∧
        ∃ σ τ : K ≃ₐ[ℚ] K,
          σ a = -a ∧ σ b = b ∧ τ a = a ∧ τ b = -b ∧
          Nat.card (K ≃ₐ[ℚ] K) = 4 ∧
          (∀ f : K ≃ₐ[ℚ] K, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : K ≃ₐ[ℚ] K, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) := by
  let L := CyclotomicField (8 * q) ℚ
  obtain ⟨d, aL, bL, hd, hbound, hddiv, hdns, haL, hbL, hχfield, hdiscrabs,
    hfund, hdiscrformula, v, hv, hint, hdim, σ, τ, hσa, hσb, hτa, hτb,
    hcard, hall, hcomm, hfrob⟩ :=
    source_biquadratic_arithmetic_canonical_of_field_ne q χ hreal hprim hne hfield
  let B := IntermediateField.adjoin ℚ ({aL, bL} : Set L)
  let aB : B := ⟨aL, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let bB : B := ⟨bL, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have haB : aB ^ 2 = (d : B) := by apply Subtype.ext; exact haL
  have hbB : bB ^ 2 = 2 := by apply Subtype.ext; exact hbL
  let Kχ := IntermediateField.adjoin ℚ ({Complex.sqrt (d : ℂ)} : Set ℂ)
  let K := IntermediateField.adjoin ℚ
    ({Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} : Set ℂ)
  let aK : K := ⟨Complex.sqrt (d : ℂ), IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let bK : K := ⟨(Real.sqrt 2 : ℂ), IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  obtain ⟨e, heaC, hebC⟩ := exists_principal_root_field_equiv v aB bB d hv haB hbB
    σ τ hσa hσb hτa hτb
  have hea : e aB = aK := Subtype.ext heaC
  have heb : e bB = bK := Subtype.ext hebC
  let hK : NumberField K := NumberField.of_ringEquiv B K e.toRingEquiv
  let : NumberField K := hK
  let νB : B →ₐ[ℚ] ℂ := K.val.comp e.toAlgHom
  obtain ⟨νL, hνL⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := ℚ) (L := B) (M := ℂ) (E := L) νB
  have hνLa : νL aL = Complex.sqrt (d : ℂ) := by
    have h := AlgHom.congr_fun hνL aB
    change νL aL = (e aB : ℂ) at h
    exact h.trans heaC
  have hχmap : (characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)).map νL = Kχ := by
    rw [← hχfield, IntermediateField.adjoin_map, Set.image_singleton, hνLa]
  have hKχne : Kχ ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} := by
    rw [← hχmap]
    exact (sourceSqrtTwoField_exclusion_map_iff q L _ νL).2 hfield
  let Q := IntermediateField.adjoin ℚ ({aL} : Set L)
  have hQmap : Q.map νL = Kχ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hνLa]
  let eχ : Q ≃ₐ[ℚ] Kχ := (Q.equivMap νL).trans (IntermediateField.equivOfEq hQmap)
  let hKχ : NumberField Kχ := NumberField.of_ringEquiv Q Kχ eχ.toRingEquiv
  let : NumberField Kχ := hKχ
  have hdiscrKχ : NumberField.discr Kχ = (if d % 4 = 1 then d else 4 * d) :=
    (NumberField.discr_eq_discr_of_algEquiv Q eχ).symm.trans hdiscrformula
  rw [hdiscrformula] at hfund hdiscrabs
  let w := v.map e.toLinearEquiv
  have hw (i : Fin 4) : w i = ![1, aK, bK, aK * bK] i := by
    change e (v i) = _
    have hv' : v i = ![1, aB, bB, aB * bB] i := hv i
    rw [hv']
    fin_cases i
    · exact map_one e
    · exact hea
    · exact heb
    · change e (aB * bB) = aK * bK
      rw [map_mul, hea, heb]
  have haK : aK ^ 2 = (d : K) := by rw [← hea, ← map_pow, haB, map_intCast]
  have hbK : bK ^ 2 = 2 := by rw [← heb, ← map_pow, hbB, map_ofNat]
  have hgal : IsGalois ℚ K := biquadratic_isGalois w aK bK (d : ℚ) 2 hw
    (by simpa [pow_two] using haK) (by simpa [pow_two] using hbK)
  have hsign := transported_sign_actions e aB bB σ τ hσa hσb hτa hτb
  rw [hea, heb] at hsign
  obtain ⟨hcardK, hallK, hcommK⟩ := transported_four_automorphisms e σ τ hcard hall hcomm
  refine ⟨d, hd, hbound, hddiv, hdns, hfund, hdiscrabs, hKχ, hK, hdiscrKχ, hKχne, hgal,
    ⟨νL, hχmap⟩, w, hw, ?_, ?_, AlgEquiv.autCongr e σ, AlgEquiv.autCongr e τ,
    hsign.1, hsign.2.1, hsign.2.2.1, hsign.2.2.2, hcardK, hallK, hcommK, ?_⟩
  · intro i
    exact map_isIntegral_int e.toRingHom (hint i)
  · simpa using Module.finrank_eq_card_basis w
  · intro p hp hpn hχp
    exact integer_two_direction_frobenius_transport e σ τ p (hfrob p hp hpn hχp)

end WeightedTorusJets

namespace WeightedTorusJets

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem characterField_ne_sourceSqrtTwoField_of_ne_eight (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hne : χ ≠ 1) (hq8 : q ≠ 8) :
    characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ) := by
  intro hfield
  have hdiscr := characterField_changeLevel_discr_natAbs
    (L := CyclotomicField (8 * q) ℚ) (dvd_mul_left q 8) χ hquad hprim hne
  have htwo := (quadraticAdjoin_discriminant _ 2
    (sourceSqrtTwoField_root_sq q (CyclotomicField (8 * q) ℚ))
    (Int.squarefree_natAbs.mp Nat.prime_two.squarefree) not_isSquare_rat_two).1
  change NumberField.discr (sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) = _ at htwo
  norm_num at htwo
  rw [hfield, htwo] at hdiscr
  exact hq8 (by simpa using hdiscr.symm)

end WeightedTorusJets

namespace WeightedTorusJets

variable {K : Type*} [Field K] [Algebra ℚ K]

def quadraticEigencharacter (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (ha0 : a ≠ 0) : (K ≃ₐ[ℚ] K) →* K where
  toFun f := f a / a
  map_one' := by simp [ha0]
  map_mul' f g := by
    rcases quadratic_algEquiv_dichotomy a d ha g with hg | hg <;>
      simp [AlgEquiv.mul_apply, hg, ha0, neg_div]

lemma quadraticEigencharacter_apply_mul (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (ha0 : a ≠ 0) (f : K ≃ₐ[ℚ] K) :
    quadraticEigencharacter a d ha ha0 f * a = f a :=
  div_mul_cancel₀ _ ha0

lemma quadraticEigencharacter_range (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (ha0 : a ≠ 0) (f : K ≃ₐ[ℚ] K) :
    quadraticEigencharacter a d ha ha0 f = 1 ∨ quadraticEigencharacter a d ha ha0 f = -1 := by
  rcases quadratic_algEquiv_dichotomy a d ha f with hf | hf <;>
    simp [quadraticEigencharacter, hf, ha0]

lemma quadraticEigencharacter_eq_neg_one_iff (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (ha0 : a ≠ 0) (f : K ≃ₐ[ℚ] K) :
    quadraticEigencharacter a d ha ha0 f = -1 ↔ f a = -a := by
  change f a / a = -1 ↔ f a = -a
  rw [div_eq_iff ha0]
  simp

end WeightedTorusJets
namespace WeightedTorusJets

theorem source_quadratic_group_character {K : Type*} [Field K] [Algebra ℚ K]
    (a : K) (d : ℚ) (ha : a ^ 2 = algebraMap ℚ K d) (hd : ¬ IsSquare d)
    (σ τ : K ≃ₐ[ℚ] K) (hσ : σ a = -a) (hτ : τ a = a) :
    ∃ ξ : (K ≃ₐ[ℚ] K) →* K,
      (∀ f, f a = ξ f * a) ∧
      (∀ f, ξ f = 1 ∨ ξ f = -1) ∧
      ξ σ = -1 ∧ ξ τ = 1 ∧ ξ (σ * τ) = -1 := by
  have ha0 : a ≠ 0 := by
    intro h
    have hd0 : d = 0 := (algebraMap ℚ K).injective (by simpa [h] using ha.symm)
    exact hd ⟨0, by simp [hd0]⟩
  have ha' : a * a = algebraMap ℚ K d := by simpa [pow_two] using ha
  let ξ := quadraticEigencharacter a d ha' ha0
  have hξσ : ξ σ = -1 := (quadraticEigencharacter_eq_neg_one_iff a d ha' ha0 σ).mpr hσ
  have hξτ : ξ τ = 1 := by simp [ξ, quadraticEigencharacter, hτ, ha0]
  refine ⟨ξ, fun f => (quadraticEigencharacter_apply_mul a d ha' ha0 f).symm,
    quadraticEigencharacter_range a d ha' ha0, hξσ, hξτ, ?_⟩
  rw [map_mul, hξσ, hξτ, mul_one]

end WeightedTorusJets


end SiegelZeros

end OAI
