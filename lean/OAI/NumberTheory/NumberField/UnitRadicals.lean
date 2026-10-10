import Mathlib

namespace OAI

/-! Finite fields containing radicals of all algebraic integer units. -/

noncomputable section

open NumberField

namespace IntegralCharacterVarieties.Arithmetic

def unitRootExtension (F : Type*) [Field F] [Algebra F ℂ]
    (ζ : ℂ) (v : (𝓞 F)ˣ → ℂ) : IntermediateField F ℂ :=
  IntermediateField.adjoin F (insert ζ (Set.range v))

theorem root_of_unit_is_ringOfIntegers_unit
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {r : ℕ} (hr : 0 < r) (u : (𝓞 F)ˣ) {x : E}
    (hx : x ^ r = algebraMap F E (u : F)) :
    ∃ w : (𝓞 E)ˣ, (w : E) = x := by
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow hr
    rw [hx]
    exact map_isIntegral_int (algebraMap F E)
      (RingOfIntegers.isIntegral_coe (u : 𝓞 F))
  let y : 𝓞 E := ⟨x, hint⟩
  have hpow : y ^ r = RingOfIntegers.mapRingHom (algebraMap F E) (u : 𝓞 F) := by
    apply RingOfIntegers.ext
    change x ^ r = algebraMap F E (u : F)
    exact hx
  have hy : IsUnit (y ^ r) := by
    rw [hpow]
    exact u.isUnit.map (RingOfIntegers.mapRingHom (algebraMap F E))
  obtain ⟨w, hw⟩ := (isUnit_pow_iff hr.ne').mp hy
  refine ⟨w, ?_⟩
  rw [hw]
  rfl

theorem finiteDimensional_unitRootExtension_and_roots
    (F : Type*) [Field F] [NumberField F] [Algebra F ℂ]
    {r : ℕ} (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (v : (𝓞 F)ˣ → ℂ) (hv : ∀ u, v u ^ r = algebraMap F ℂ (u : F)) :
    FiniteDimensional F (unitRootExtension F ζ v) ∧
      ∀ (u : (𝓞 F)ˣ) (x : ℂ), x ^ r = algebraMap F ℂ (u : F) →
        x ∈ unitRootExtension F ζ v := by
  classical
  let : NeZero r := ⟨hr.ne'⟩
  obtain ⟨S, hSgen, hSfin⟩ :=
    Monoid.fg_iff.mp (inferInstance : Monoid.FG (𝓞 F)ˣ)
  let E : IntermediateField F ℂ := IntermediateField.adjoin F (insert ζ (v '' S))
  have hζE : ζ ∈ E := IntermediateField.subset_adjoin F _ (Set.mem_insert _ _)
  let H : Submonoid (𝓞 F)ˣ :=
    { carrier := {u | ∃ a : ℂ, a ∈ E ∧ a ^ r = algebraMap F ℂ (u : F)}
      one_mem' := by
        refine ⟨1, E.one_mem, ?_⟩
        simp
      mul_mem' := by
        rintro u w ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
        refine ⟨a * b, E.mul_mem ha hb, ?_⟩
        simp [mul_pow, har, hbr] }
  have hSH : S ⊆ H := by
    intro u hu
    exact ⟨v u, IntermediateField.subset_adjoin F _
      (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩), hv u⟩
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hSgen]
    exact Submonoid.closure_le.mpr hSH
  have hroots : ∀ (u : (𝓞 F)ˣ) (x : ℂ),
      x ^ r = algebraMap F ℂ (u : F) → x ∈ E := by
    intro u x hx
    have hu : u ∈ H := by rw [hH]; trivial
    obtain ⟨a, ha, har⟩ := hu
    have humap : algebraMap F ℂ (u : F) ≠ 0 :=
      (map_ne_zero (algebraMap F ℂ)).mpr (NumberField.Units.coe_ne_zero u)
    have ha0 : a ≠ 0 := by
      intro h
      apply humap
      rw [← har, h, zero_pow hr.ne']
    have hquot : (x / a) ^ r = 1 := by
      rw [div_pow, hx, har, div_self humap]
    obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one hquot
    have hxa : x = ζ ^ i * a := (div_eq_iff ha0).mp hi.symm
    rw [hxa]
    exact E.mul_mem (E.pow_mem hζE i) ha
  have hLE : unitRootExtension F ζ v ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases hx with rfl | ⟨u, rfl⟩
    · exact hζE
    · exact hroots u (v u) (hv u)
  have hEL : E ≤ unitRootExtension F ζ v := by
    apply IntermediateField.adjoin.mono
    intro x hx
    rcases hx with rfl | ⟨u, _, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨u, rfl⟩
  have hEq : unitRootExtension F ζ v = E := le_antisymm hLE hEL
  constructor
  · rw [hEq]
    let : Fintype ↥(insert ζ (v '' S)) := ((hSfin.image v).insert ζ).fintype
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    rcases hx with rfl | ⟨u, _, rfl⟩
    · apply IsIntegral.of_pow hr
      rw [hζ.pow_eq_one]
      exact isIntegral_one
    · apply IsIntegral.of_pow hr
      rw [hv]
      exact isIntegral_algebraMap
  · intro u x hx
    rw [hEq]
    exact hroots u x hx

theorem uniform_field
    (F : Type*) [Field F] [NumberField F] [Algebra F ℂ]
    {r : ℕ} (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (v : (𝓞 F)ˣ → ℂ) (hv : ∀ u, v u ^ r = algebraMap F ℂ (u : F)) :
    FiniteDimensional F (unitRootExtension F ζ v) ∧
      ∀ (u : (𝓞 F)ˣ) (x : ℂ), x ^ r = algebraMap F ℂ (u : F) →
        ∃ w : (𝓞 (unitRootExtension F ζ v))ˣ,
          algebraMap (unitRootExtension F ζ v) ℂ
            (w : unitRootExtension F ζ v) = x := by
  obtain ⟨hfin, hroots⟩ := finiteDimensional_unitRootExtension_and_roots F hr ζ hζ v hv
  refine ⟨hfin, ?_⟩
  intro u x hx
  let y : unitRootExtension F ζ v := ⟨x, hroots u x hx⟩
  have hy : y ^ r = algebraMap F (unitRootExtension F ζ v) (u : F) := by
    apply Subtype.ext
    change x ^ r = algebraMap F ℂ (u : F)
    exact hx
  obtain ⟨w, hw⟩ := root_of_unit_is_ringOfIntegers_unit hr u hy
  refine ⟨w, ?_⟩
  rw [hw]
  rfl

def primitiveRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem primitiveRoot_isPrimitiveRoot {n : ℕ} (hn : 0 < n) :
    IsPrimitiveRoot (primitiveRoot n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

def unitRootChoice (F : Type*) [Field F] [Algebra F ℂ]
    (r : ℕ) (hr : 0 < r) (u : (𝓞 F)ˣ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap F ℂ (u : F)) hr)

theorem unitRootChoice_pow (F : Type*) [Field F] [Algebra F ℂ]
    (r : ℕ) (hr : 0 < r) (u : (𝓞 F)ˣ) :
    unitRootChoice F r hr u ^ r = algebraMap F ℂ (u : F) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap F ℂ (u : F)) hr)

def radicalField (F : Type*) [Field F] [Algebra F ℂ]
    (r : ℕ) (hr : 0 < r) : IntermediateField F ℂ :=
  unitRootExtension F (primitiveRoot r) (unitRootChoice F r hr)

theorem radicalField_finite_and_units
    (F : Type*) [Field F] [NumberField F] [Algebra F ℂ]
    {r : ℕ} (hr : 0 < r) :
    FiniteDimensional F (radicalField F r hr) ∧
      ∀ (u : (𝓞 F)ˣ) (x : ℂ), x ^ r = algebraMap F ℂ (u : F) →
        ∃ w : (𝓞 (radicalField F r hr))ˣ,
          algebraMap (radicalField F r hr) ℂ (w : radicalField F r hr) = x :=
  uniform_field F hr (primitiveRoot r) (primitiveRoot_isPrimitiveRoot hr)
    (unitRootChoice F r hr) (unitRootChoice_pow F r hr)

def auxiliaryField (K : Type*) [Field K] [Algebra K ℂ]
    (p q : ℕ) : IntermediateField K ℂ :=
  IntermediateField.adjoin K
    {((Real.sqrt 2 : ℝ) : ℂ), primitiveRoot (p * q)}

theorem auxiliaryField_finite
    (K : Type*) [Field K] [Algebra K ℂ]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    FiniteDimensional K (auxiliaryField K p q) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x hx
  rcases hx with rfl | rfl
  · apply IsIntegral.of_pow (n := 2) (by norm_num)
    have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = algebraMap K ℂ (2 : K) := by
      rw [map_ofNat]
      norm_cast
      norm_num [Real.sq_sqrt]
    rw [hsqrt]
    exact isIntegral_algebraMap
  · apply IsIntegral.of_pow (Nat.mul_pos hp.pos hq.pos)
    rw [(primitiveRoot_isPrimitiveRoot (Nat.mul_pos hp.pos hq.pos)).pow_eq_one]
    exact isIntegral_one

theorem specified_field_finite_and_units
    (K : Type*) [Field K] [NumberField K] [Algebra K ℂ]
    {r p q : ℕ} (hr : 0 < r) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    FiniteDimensional K (radicalField (auxiliaryField K p q) r hr) ∧
      ∀ (u : (𝓞 (auxiliaryField K p q))ˣ) (x : ℂ),
        x ^ r = algebraMap (auxiliaryField K p q) ℂ (u : auxiliaryField K p q) →
        ∃ w : (𝓞 (radicalField (auxiliaryField K p q) r hr))ˣ,
          algebraMap (radicalField (auxiliaryField K p q) r hr) ℂ
            (w : radicalField (auxiliaryField K p q) r hr) = x := by
  let : FiniteDimensional K (auxiliaryField K p q) := auxiliaryField_finite K hp hq
  let : NumberField (auxiliaryField K p q) :=
    NumberField.of_module_finite K (auxiliaryField K p q)
  obtain ⟨hfin, hunits⟩ := radicalField_finite_and_units (auxiliaryField K p q) hr
  let : FiniteDimensional (auxiliaryField K p q)
      (radicalField (auxiliaryField K p q) r hr) := hfin
  exact ⟨FiniteDimensional.trans K (auxiliaryField K p q)
    (radicalField (auxiliaryField K p q) r hr), hunits⟩

theorem exists_distinct_primes_gt (r : ℕ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ r < p ∧ r < q ∧ p ≠ q := by
  obtain ⟨p, hrp, hp⟩ := Nat.exists_infinite_primes (r + 1)
  obtain ⟨q, hpq, hq⟩ := Nat.exists_infinite_primes (p + 1)
  exact ⟨p, q, hp, hq, by omega, by omega, by omega⟩

end IntegralCharacterVarieties.Arithmetic

namespace IntegralCharacterVarieties

theorem density_transfer
    {ι Y : Type*} [TopologicalSpace Y]
    (B T : ι → Type*) [∀ i, TopologicalSpace (B i)]
    [∀ i, TopologicalSpace (T i)]
    (p : ∀ i, T i → B i) (f : ∀ i, T i → Y)
    (hp : ∀ i, IsOpenMap (p i)) (hf : ∀ i, Continuous (f i))
    (hcover : ∀ y : Y, ∃ (i : ι) (t : T i), f i t = y)
    (I : ∀ i, Set (B i)) (hI : ∀ i, Dense (I i))
    (J : Set Y)
    (hfiber : ∀ (i : ι) (b : B i), b ∈ I i →
      Dense {t : {t : T i // p i t = b} | f i t.1 ∈ J}) :
    Dense J := by
  rw [dense_iff_inter_open]
  intro U hU hUnon
  obtain ⟨y, hy⟩ := hUnon
  obtain ⟨i, t, hty⟩ := hcover y
  have hV : IsOpen (f i ⁻¹' U) := (hf i).isOpen_preimage U hU
  have htV : t ∈ f i ⁻¹' U := by
    change f i t ∈ U
    rw [hty]
    exact hy
  have hnon : (p i '' (f i ⁻¹' U)).Nonempty := ⟨p i t, t, htV, rfl⟩
  obtain ⟨b, hbI, t', ht'V, ht'b⟩ :=
    (hI i).exists_mem_open (hp i _ hV) hnon
  let t₀ : {t : T i // p i t = b} := ⟨t', ht'b⟩
  have hW : IsOpen {t : {t : T i // p i t = b} | f i t.1 ∈ U} :=
    ((hf i).comp continuous_subtype_val).isOpen_preimage U hU
  have hWnon : {t : {t : T i // p i t = b} | f i t.1 ∈ U}.Nonempty :=
    ⟨t₀, ht'V⟩
  obtain ⟨s, hsJ, hsU⟩ := (hfiber i b hbI).exists_mem_open hW hWnon
  exact ⟨f i s.1, hsU, hsJ⟩

end IntegralCharacterVarieties

end

end OAI
