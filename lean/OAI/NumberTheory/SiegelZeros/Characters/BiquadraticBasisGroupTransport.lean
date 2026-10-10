import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.BiquadraticGoodPrimeUnramifiedSameWitnessEquiv
import OAI.NumberTheory.SiegelZeros.Characters.BiquadraticThetaMap
import OAI.NumberTheory.SiegelZeros.Characters.CharacterGlobalGreedyDeterminantMasterBounds
import OAI.NumberTheory.SiegelZeros.Characters.FrobeniusRetainedCharacterField
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.GreedyPivotsRingEquiv
import OAI.NumberTheory.SiegelZeros.Structure.QuadraticEigencharacterAutCongr

namespace OAI

namespace SiegelZeros


open scoped NumberField

namespace WeightedTorusJets

theorem biquadratic_basis_group_transport {B K : Type*}
    [Field B] [Field K] [NumberField B] [NumberField K]
    (eB : B ≃ₐ[ℚ] K) (v : Module.Basis (Fin 4) ℚ B) (a b : B)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (hint : ∀ i, IsIntegral ℤ (v i))
    (hdegree : Module.finrank ℚ B = 4) (σ τ : B ≃ₐ[ℚ] B)
    (hσa : σ a = -a) (hσb : σ b = b) (hτa : τ a = a) (hτb : τ b = -b)
    (hcard : Nat.card (B ≃ₐ[ℚ] B) = 4)
    (hall : ∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ)
    (hcomm : ∀ f g : B ≃ₐ[ℚ] B, Commute f g) :
    let A := eB a
    let bK := eB b
    let w := v.map eB.toLinearEquiv
    (∀ i, w i = ![1, A, bK, A * bK] i) ∧
    (∀ i, IsIntegral ℤ (w i)) ∧ Module.finrank ℚ K = 4 ∧ IsGalois ℚ K ∧
    (AlgEquiv.autCongr eB σ A = -A ∧ AlgEquiv.autCongr eB σ bK = bK ∧
      AlgEquiv.autCongr eB τ A = A ∧ AlgEquiv.autCongr eB τ bK = -bK) ∧
    Nat.card (K ≃ₐ[ℚ] K) = 4 ∧
    (∀ f : K ≃ₐ[ℚ] K, f = 1 ∨ f = AlgEquiv.autCongr eB σ ∨
      f = AlgEquiv.autCongr eB τ ∨ f = AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) ∧
    (∀ f g : K ≃ₐ[ℚ] K, Commute f g) := by
  have hw (i : Fin 4) : v.map eB.toLinearEquiv i = ![1, eB a, eB b, eB a * eB b] i := by
    rw [Module.Basis.map_apply, hv]
    fin_cases i <;> simp
  have hwDegree : Module.finrank ℚ K = 4 := eB.toLinearEquiv.finrank_eq.symm.trans hdegree
  obtain ⟨hcardK, hallK, hcommK⟩ := transported_four_automorphisms eB σ τ hcard hall hcomm
  exact ⟨hw, fun i => map_isIntegral_int eB.toRingHom (hint i), hwDegree,
    IsGalois.of_card_aut_eq_finrank ℚ K (hcardK.trans hwDegree.symm),
    transported_sign_actions eB a b σ τ hσa hσb hτa hτb, hcardK, hallK, hcommK⟩


theorem biquadratic_directions_eq_of_galois_coordinates
    {K : Type*} [Field K] [CharZero K] (a b : K) (φ : K →+* ℂ)
    (σ τ : K ≃ₐ[ℚ] K) (hσa : σ a = -a) (hσb : σ b = b)
    (hτa : τ a = a) (hτb : τ b = -b) {a₀ b₀ : ℂ}
    (hφa : φ a = a₀) (hφb : φ b = b₀) (D : Fin 3 → Fin 4 → ℂ)
    (hD : ∀ j i, D j i =
      φ ((![![1, a, b, a * b], (fun i => σ (![1, a, b, a * b] i)),
        (fun i => (σ * τ) (![1, a, b, a * b] i))] : Fin 3 → Fin 4 → K) j i)) :
    ∀ j, D j = biquadraticDirections a₀ b₀ j := by
  intro j
  funext i
  rw [hD]
  fin_cases j <;> fin_cases i <;>
    simp [biquadraticDirections, AlgEquiv.mul_apply, hσa, hσb, hτa, hτb, hφa, hφb]



attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_master_principal_opaque_prefix (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : (CyclotomicField (8 * q) ℚ)), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : (CyclotomicField (8 * q) ℚ)) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      ∃ (B : IntermediateField ℚ (CyclotomicField (8 * q) ℚ))
        (principalK : IntermediateField ℚ ℂ),
        B = IntermediateField.adjoin ℚ {a, b} ∧
        principalK = IntermediateField.adjoin ℚ {Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} ∧
      ∃ a' b' : B, (a' : CyclotomicField (8 * q) ℚ) = a ∧
        (b' : CyclotomicField (8 * q) ℚ) = b ∧ a' ^ 2 = (d : B) ∧ b' ^ 2 = 2 ∧
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∃ eB : B ≃ₐ[ℚ] principalK,
            (eB a' : ℂ) = Complex.sqrt (d : ℂ) ∧
            (eB b' : ℂ) = (Real.sqrt 2 : ℂ) ∧
          ∃ hPrincipal : NumberField principalK, letI := hPrincipal
          (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x))) ∧
          (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q →
            Algebra.IsUnramifiedIn (𝓞 principalK) (Ideal.span {(p : ℤ)})) ∧
          ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ : Fin (N ^ 4) → B := fun j =>
                ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
              let R : (Fin 3 → ℕ) → Fin (N ^ 4) → B := fun β j =>
                θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
              ∀ order : ℕ ≃ (Fin 3 → ℕ),
                Monotone (fun i => order i 0 + H * order i 1 + H * order i 2) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ order)
                    (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
                  (∀ i, α i = order (g i)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧ Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p)) := by
  classical
  obtain ⟨_C, _hC, _hC4, _CH, hmaster⟩ :=
    source_character_global_greedy_determinant_master_bounds
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hsource⟩ :=
    hmaster q χ hreal hprim hne hfield
  clear hmaster
  let L := CyclotomicField (8 * q) ℚ
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
  have hb' : b' ^ 2 = 2 := by apply Subtype.ext; exact hb
  let principalK := IntermediateField.adjoin ℚ
    ({Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} : Set ℂ)
  obtain ⟨eB, heBa, heBb⟩ := exists_principal_root_field_equiv
    (K := B) v a' b' d hv ha' hb' σ τ hσa hσb hτa hτb
  have hPrincipal : NumberField principalK :=
    NumberField.of_ringEquiv B principalK eB.toRingEquiv
  let : NumberField principalK := hPrincipal
  have hfrob := source_frobenius_of_retained_character_field q L χ hreal
    a b hchar hdegree σ τ hτa hcard hall
  have hunram (p : ℕ) (hp : p.Prime) (hgood : ¬ p ∣ 2 * q) :
      Algebra.IsUnramifiedIn (𝓞 principalK) (Ideal.span {(p : ℤ)}) :=
    source_biquadratic_good_prime_unramified_same_witness_equiv q p a b eB hp hgood
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    B, principalK, rfl, rfl, a', b', rfl, rfl, ha', hb',
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm,
    eB, heBa, heBb, hPrincipal, hfrob, hunram, ?_⟩
  intro N H hH hHN n
  dsimp only
  intro order horder
  obtain ⟨g, α, hg, hα, _hrange, _hmono, _hweight, _hstable, Δ, hΔ, hΔne,
    harch, hdiv, _hraw, _hfinite, _hlarge⟩ := hsource N H hH hHN n order horder
  exact ⟨g, α, hg, hα, Δ, hΔ, hΔne, harch, hdiv⟩

theorem source_principal_character_field_transport (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ))
    (d : ℤ) (a : CyclotomicField (8 * q) ℚ)
    (hchar : IntermediateField.adjoin ℚ {a} =
      characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ))
    (hdisc : (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q)
    (hfund : Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})))
    (hformula : NumberField.discr (IntermediateField.adjoin ℚ {a}) =
      (if d % 4 = 1 then d else 4 * d))
    (B : IntermediateField ℚ (CyclotomicField (8 * q) ℚ))
    (K : IntermediateField ℚ ℂ) (aB : B)
    (hcoeA : (aB : CyclotomicField (8 * q) ℚ) = a)
    (eB : B ≃ₐ[ℚ] K) (heBa : (eB aB : ℂ) = Complex.sqrt (d : ℂ)) :
    ∃ (Kχ : IntermediateField ℚ ℂ) (νL : CyclotomicField (8 * q) ℚ →ₐ[ℚ] ℂ),
      Kχ = IntermediateField.adjoin ℚ {Complex.sqrt (d : ℂ)} ∧
      (∀ x : B, νL x = (eB x : ℂ)) ∧
      (characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)).map νL = Kχ ∧
    ∃ eχ : IntermediateField.adjoin ℚ ({a} : Set (CyclotomicField (8 * q) ℚ)) ≃ₐ[ℚ] Kχ,
      (∀ x, (eχ x : ℂ) = νL x) ∧
    ∃ hKχ : NumberField Kχ, letI := hKχ
      NumberField.discr Kχ = (if d % 4 = 1 then d else 4 * d) ∧
      NumberField.discr Kχ =
        integerCharacter χ (real_character_isQuadratic χ hreal) (-1) * (q : ℤ) ∧
      Int.IsFundamentalDiscr (NumberField.discr Kχ) ∧
      (NumberField.discr Kχ).natAbs = q ∧
      Kχ ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} := by
  classical
  let L := CyclotomicField (8 * q) ℚ
  let Kχ := IntermediateField.adjoin ℚ ({Complex.sqrt (d : ℂ)} : Set ℂ)
  let νB : B →ₐ[ℚ] ℂ := K.val.comp eB.toAlgHom
  obtain ⟨νL, hνL⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := ℚ) (L := B) (M := ℂ) (E := L) νB
  have hνLa : νL a = Complex.sqrt (d : ℂ) :=
    (congrArg νL hcoeA).symm.trans ((AlgHom.congr_fun hνL aB).trans heBa)
  have hχmap : (characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)).map νL = Kχ := by
    rw [← hchar, IntermediateField.adjoin_map, Set.image_singleton, hνLa]
  have hKχne : Kχ ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} := by
    rw [← hχmap]
    exact (sourceSqrtTwoField_exclusion_map_iff q L _ νL).2 hfield
  let Qχ := IntermediateField.adjoin ℚ ({a} : Set L)
  have hQχmap : Qχ.map νL = Kχ := by
    simpa only [Qχ, hchar] using hχmap
  let eχ : Qχ ≃ₐ[ℚ] Kχ := (Qχ.equivMap νL).trans (IntermediateField.equivOfEq hQχmap)
  let hKχ : NumberField Kχ := NumberField.of_ringEquiv Qχ Kχ eχ.toRingEquiv
  let : NumberField Kχ := hKχ
  have hdiscrTransport : NumberField.discr Kχ = NumberField.discr Qχ :=
    (NumberField.discr_eq_discr_of_algEquiv Qχ eχ).symm
  have hdiscrKχ : NumberField.discr Kχ = (if d % 4 = 1 then d else 4 * d) :=
    hdiscrTransport.trans hformula
  have hfundKχ : Int.IsFundamentalDiscr (NumberField.discr Kχ) :=
    hdiscrTransport.symm ▸ hfund
  have habsKχ : (NumberField.discr Kχ).natAbs = q :=
    (congrArg Int.natAbs hdiscrTransport).trans hdisc
  have hquad := real_character_isQuadratic χ hreal
  have hsignKχ : NumberField.discr Kχ = integerCharacter χ hquad (-1) * (q : ℤ) := by
    rw [hdiscrTransport]
    change NumberField.discr (IntermediateField.adjoin ℚ {a}) = _
    rw [hchar]
    exact characterField_changeLevel_discr_eq_signed_conductor
      (dvd_mul_left q 8) χ hquad hprim hne
  have hνB (x : B) : νL x = (eB x : ℂ) := AlgHom.congr_fun hνL x
  have heχ (x : Qχ) : (eχ x : ℂ) = νL x := rfl
  exact ⟨Kχ, νL, rfl, hνB, hχmap, eχ, heχ, hKχ,
    hdiscrKχ, hsignKχ, hfundKχ, habsKχ, hKχne⟩

theorem source_principal_determinant_suffix
    {B principalK : Type*} [Field B] [Field principalK]
    [Algebra ℚ B] [Algebra ℚ principalK]
    (q : ℕ) (χ : DirichletCharacter ℂ q) (d : ℤ)
    (a' b' : B) (A bK : principalK) (σ τ : B ≃ₐ[ℚ] B)
    (eB : B ≃ₐ[ℚ] principalK) (heA : eB a' = A) (heB : eB b' = bK)
    (ha' : a' ^ 2 = (d : B)) (hb' : b' ^ 2 = 2)
    (hdreal : |(d : ℝ)| ≤ q) (hq : 1 ≤ q)
    (hsource :
      ∀ N H : ℕ, 0 < H → H ≤ N →
        ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
          let θ : Fin (N ^ 4) → B := fun j =>
            ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
          let R : (Fin 3 → ℕ) → Fin (N ^ 4) → B := fun β j =>
            θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
          ∀ order : ℕ ≃ (Fin 3 → ℕ),
            Monotone (fun i => order i 0 + H * order i 1 + H * order i 2) →
            ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
              Set.range g = (greedyPivots B (R ∘ order)
                (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
              (∀ i, α i = order (g i)) ∧
              ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧ Δ ≠ 0 ∧
                ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                  (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                    ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                      (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                  Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p))) :
    ∀ N H : ℕ, 0 < H → H ≤ N → ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
      let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
      let θK := fun j => ∑ i : Fin 4, ((n j i : ℕ) : principalK) * ![1, A, bK, A * bK] i
      let R := fun β : Fin 3 → ℕ => fun j =>
        θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
      let RK := fun β : Fin 3 → ℕ => fun j =>
        θK j ^ β 0 * (AlgEquiv.autCongr eB σ) (θK j) ^ β 1 *
          (AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) (θK j) ^ β 2
      ∀ order : ℕ ≃ (Fin 3 → ℕ),
        Monotone (fun i => order i 0 + H * order i 1 + H * order i 2) →
        ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)) (Δ : 𝓞 B),
          Set.range g = (greedyPivots B (R ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
          Set.range g = (greedyPivots principalK (RK ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
          (∀ T : ℕ, greedyPivots principalK (RK ∘ order) T = greedyPivots B (R ∘ order) T) ∧
          (∀ i, α i = order (g i)) ∧
          (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
          let ΔK := NumberField.RingOfIntegers.mapRingEquiv eB.toRingEquiv Δ
          (∀ j, eB (θ j) = θK j) ∧ (∀ β j, eB (R β j) = RK β j) ∧
          (ΔK : principalK) = eB (Δ : B) ∧
          (ΔK : principalK) = Matrix.det (fun i j => RK (α i) j) ∧ ΔK ≠ 0 ∧
          Algebra.norm ℚ (ΔK : principalK) = Algebra.norm ℚ (Δ : B) ∧
          Algebra.norm ℤ ΔK = Algebra.norm ℤ Δ ∧
          (∀ p r : ℕ,
            ((p : 𝓞 principalK) ^ r ∣ ΔK ↔ (p : 𝓞 B) ^ r ∣ Δ) ∧
            (ΔK ∈ (Ideal.span {(p : 𝓞 principalK)}) ^ r ↔ Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ r)) ∧
          (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
            ΔK ∈ (Ideal.span {(p : 𝓞 principalK)}) ^ (∑ i, α i 0 / p)) ∧
          (∀ νK : principalK →+* ℂ, ∀ j, ‖νK (θK j)‖ ≤ 8 * N * Real.sqrt q) ∧
          (∀ νK : principalK →+* ℂ, ∀ β j,
            ‖νK (RK β j)‖ ≤ (8 * N * Real.sqrt q) ^ (β 0 + β 1 + β 2)) ∧
          (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (ΔK : principalK) : ℝ)| ≤
            (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
              ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  classical
  intro N H hH hHN n
  dsimp only
  intro order horder
  obtain ⟨g, α, hg, hα, Δ, hΔ, hΔne, harch, hdiv⟩ := hsource N H hH hHN n order horder
  clear hsource
  let θ : Fin (N ^ 4) → B := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
  let θK : Fin (N ^ 4) → principalK := fun j => ∑ i : Fin 4, ((n j i : ℕ) : principalK) * ![1, A, bK, A * bK] i
  let R : (Fin 3 → ℕ) → Fin (N ^ 4) → B := fun β j =>
    θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
  let RK : (Fin 3 → ℕ) → Fin (N ^ 4) → principalK := fun β j =>
    θK j ^ β 0 * (AlgEquiv.autCongr eB σ) (θK j) ^ β 1 *
      (AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) (θK j) ^ β 2
  let ΔK : NumberField.RingOfIntegers principalK :=
    NumberField.RingOfIntegers.mapRingEquiv eB.toRingEquiv Δ
  have htransport :=
    source_existing_integral_jet_witness_transport
      (K := B) (L := principalK) (ι := Fin (N ^ 4)) eB σ τ a' b' A bK heA heB
      (fun j i => (n j i : ℕ)) θ (fun _ => rfl) α Δ hΔ hΔne
  obtain ⟨hθe, hrow, hdetK, hneK, hnormQ, hnormZ, hprimepowers⟩ := htransport
  change ∀ j, eB (θ j) = θK j at hθe
  change ∀ β j, eB (R β j) = RK β j at hrow
  change Algebra.norm ℚ (ΔK : principalK) = Algebra.norm ℚ (Δ : B) at hnormQ
  have hgreedyAll (T : ℕ) :
      greedyPivots principalK (RK ∘ order) T =
        greedyPivots B (R ∘ order) T :=
    source_greedy_indices_transport eB.toRingEquiv R RK hrow order T
  have hgK : Set.range g =
      (greedyPivots principalK (RK ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) :=
    hg.trans (congrArg (fun s : Finset ℕ => (s : Set ℕ))
      (hgreedyAll (weightedJetIndices H (N ^ 4 - 1)).card).symm)
  have htheta_bound (νK : principalK →+* ℂ) (j : Fin (N ^ 4)) :
      ‖νK (θK j)‖ ≤ 8 * N * Real.sqrt q := by
    rw [← hθe j]
    exact norm_embedding_basis_sum_le (νK.comp eB.toRingHom) ha' hb' hdreal hq
      (fun i => (n j i : ℕ)) (fun i => (n j i).isLt)
  have hrow_bound (νK : principalK →+* ℂ) (β : Fin 3 → ℕ) (j : Fin (N ^ 4)) :
      ‖νK (RK β j)‖ ≤ (8 * N * Real.sqrt q) ^ (β 0 + β 1 + β 2) := by
    rw [← hrow β j]
    exact norm_embedding_derivative_entry_le (νK.comp eB.toRingHom)
      σ.toRingHom τ.toRingHom ha' hb' hdreal hq
      (fun i => (n j i : ℕ)) (fun i => (n j i).isLt) β
  have harchK :
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (ΔK : principalK) : ℝ)| ≤
        (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
          ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
            (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
    rw [hnormQ]
    exact harch
  refine ⟨g, α, Δ, hg, hgK, hgreedyAll, hα, hΔ, hθe, hrow, rfl, hdetK, hneK, hnormQ,
    hnormZ, hprimepowers, ?_, htheta_bound, hrow_bound, harchK⟩
  intro p hp hHp hpq hχp
  exact (hprimepowers p (∑ i, α i 0 / p)).2.mpr (hdiv p hp hHp hpq hχp)

theorem source_principal_existing_data_completion (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ))
    (d : ℤ) (a : CyclotomicField (8 * q) ℚ)
    (hbound : d.natAbs ≤ q) (hns : ¬ IsSquare (d : ℚ))
    (hchar : IntermediateField.adjoin ℚ {a} = characterField (8 * q)
      (CyclotomicField (8 * q) ℚ) ℂ (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ))
    (hdisc : (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q)
    (hfund : Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})))
    (hformula : NumberField.discr (IntermediateField.adjoin ℚ {a}) =
      (if d % 4 = 1 then d else 4 * d))
    (B : IntermediateField ℚ (CyclotomicField (8 * q) ℚ))
    (principalK : IntermediateField ℚ ℂ) (a' b' : B)
    (hcoeA : (a' : CyclotomicField (8 * q) ℚ) = a)
    (ha' : a' ^ 2 = (d : B)) (hb' : b' ^ 2 = 2)
    (v : Module.Basis (Fin 4) ℚ B) (hv : ∀ i, v i = ![1, a', b', a' * b'] i)
    (hint : ∀ i, IsIntegral ℤ (v i)) (hdegree : Module.finrank ℚ B = 4)
    (σ τ : B ≃ₐ[ℚ] B) (hσa : σ a' = -a') (hσb : σ b' = b')
    (hτa : τ a' = a') (hτb : τ b' = -b') (hcard : Nat.card (B ≃ₐ[ℚ] B) = 4)
    (hall : ∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ)
    (hcomm : ∀ f g : B ≃ₐ[ℚ] B, Commute f g)
    (eB : B ≃ₐ[ℚ] principalK) (heBa : (eB a' : ℂ) = Complex.sqrt (d : ℂ))
    (heBb : (eB b' : ℂ) = (Real.sqrt 2 : ℂ)) (hPrincipal : NumberField principalK)
    (hfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
      ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
        (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)))
    (hunram : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q →
      Algebra.IsUnramifiedIn (𝓞 principalK) (Ideal.span {(p : ℤ)}))
    (hsource : ∀ N H : ℕ, 0 < H → H ≤ N →
            ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
              let θ : Fin (N ^ 4) → B := fun j =>
                ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
              let R : (Fin 3 → ℕ) → Fin (N ^ 4) → B := fun β j =>
                θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
              ∀ order : ℕ ≃ (Fin 3 → ℕ),
                Monotone (fun i => order i 0 + H * order i 1 + H * order i 2) →
                ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)),
                  Set.range g = (greedyPivots B (R ∘ order)
                    (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
                  (∀ i, α i = order (g i)) ∧
                  ∃ Δ : 𝓞 B, (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧ Δ ≠ 0 ∧
                    ((1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (Δ : B) : ℝ)| ≤
                      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                        ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                          (Real.log N + 1 / 2 * Real.log q + Real.log 8)) ∧
                    (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                      Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ (∑ i, α i 0 / p))) :
      letI := hPrincipal
        let A := eB a'
        let bK := eB b'
        let w := v.map eB.toLinearEquiv
        let φB := principalK.val.toRingHom.comp eB.toRingHom
        (∀ i, w i = ![1, A, bK, A * bK] i) ∧ (∀ i, IsIntegral ℤ (w i)) ∧
        Module.finrank ℚ principalK = 4 ∧ IsGalois ℚ principalK ∧
        (AlgEquiv.autCongr eB σ A = -A ∧ AlgEquiv.autCongr eB σ bK = bK ∧
          AlgEquiv.autCongr eB τ A = A ∧ AlgEquiv.autCongr eB τ bK = -bK) ∧
        Nat.card (principalK ≃ₐ[ℚ] principalK) = 4 ∧
        (∀ f : principalK ≃ₐ[ℚ] principalK, f = 1 ∨ f = AlgEquiv.autCongr eB σ ∨
          f = AlgEquiv.autCongr eB τ ∨ f = AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) ∧
        (∀ f g : principalK ≃ₐ[ℚ] principalK, Commute f g) ∧
      ∃ (Kχ : IntermediateField ℚ ℂ) (νL : CyclotomicField (8 * q) ℚ →ₐ[ℚ] ℂ),
        Kχ = IntermediateField.adjoin ℚ {Complex.sqrt (d : ℂ)} ∧
        (∀ x : B, νL x = (eB x : ℂ)) ∧
        (characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
          (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)).map νL = Kχ ∧
      ∃ eχ : IntermediateField.adjoin ℚ ({a} : Set (CyclotomicField (8 * q) ℚ)) ≃ₐ[ℚ] Kχ,
        (∀ x, (eχ x : ℂ) = νL x) ∧
      ∃ hKχ : NumberField Kχ, letI := hKχ
        NumberField.discr Kχ = (if d % 4 = 1 then d else 4 * d) ∧
        NumberField.discr Kχ =
          integerCharacter χ (real_character_isQuadratic χ hreal) (-1) * (q : ℤ) ∧
        Int.IsFundamentalDiscr (NumberField.discr Kχ) ∧
        (NumberField.discr Kχ).natAbs = q ∧
        Kχ ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} ∧
        biquadraticCoefficients (φB a') (φB b') =
          ![1, 1 / Complex.sqrt (d : ℂ), -(1 / (Real.sqrt 2 : ℂ)),
            -(1 / (Complex.sqrt (d : ℂ) * (Real.sqrt 2 : ℂ)))] ∧
        LinearIndependent ℚ
          (![1, 1 / Complex.sqrt (d : ℂ), -(1 / (Real.sqrt 2 : ℂ)),
            -(1 / (Complex.sqrt (d : ℂ) * (Real.sqrt 2 : ℂ)))] : Fin 4 → ℂ) ∧
      ∃ D : Module.Basis (Fin 3) ℂ
          (LinearMap.ker (biquadraticForm (Complex.sqrt (d : ℂ)) (Real.sqrt 2 : ℂ))),
        (∀ j i, (D j : Fin 4 → ℂ) i =
          φB ((![![1, a', b', a' * b'], (fun i => σ (![1, a', b', a' * b'] i)),
            (fun i => (σ * τ) (![1, a', b', a' * b'] i))] : Fin 3 → Fin 4 → B) j i)) ∧
        (∀ j, (D j : Fin 4 → ℂ) =
          biquadraticDirections (Complex.sqrt (d : ℂ)) (Real.sqrt 2 : ℂ) j) ∧
        (∀ (N : ℕ) (n : Fin (N ^ 4) ≃ (Fin 4 → Fin N)) (s : Set (Fin 3 → ℕ)),
          Module.finrank ℂ (Submodule.span ℂ
            ((fun β : Fin 3 → ℕ => fun j => MvPolynomial.eval (fun _ => 1)
              (Geometry.invariantJet (fun k i => (D k : Fin 4 → ℂ) i) β
                (MvPolynomial.monomial
                  (Finsupp.equivFunOnFinite.symm (fun i => (n j i : ℕ))) 1))) '' s)) =
          Module.finrank B (Submodule.span B
            ((fun β : Fin 3 → ℕ => fun j =>
              (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i) ^ β 0 *
              σ (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i) ^ β 1 *
              (σ * τ) (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i) ^
                β 2) '' s))) ∧
      ∃ (hA : A * A = algebraMap ℚ principalK (d : ℚ)) (hA0 : A ≠ 0),
        let ξ := quadraticEigencharacter A (d : ℚ) hA hA0
        (∀ f, f A = ξ f * A) ∧ (∀ f, ξ f = 1 ∨ ξ f = -1) ∧
        ξ (AlgEquiv.autCongr eB σ) = -1 ∧ ξ (AlgEquiv.autCongr eB τ) = 1 ∧
        ξ (AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) = -1 ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q →
          Algebra.IsUnramifiedIn (𝓞 principalK) (Ideal.span {(p : ℤ)})) ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
          ∃ φ : B ≃ₐ[ℚ] B, (φ = σ ∨ φ = σ * τ) ∧
            (∀ (P : Ideal (𝓞 principalK)) (_ : P.IsPrime), P.LiesOver (Ideal.span {(p : ℤ)}) →
              IsArithFrobAt ℤ (AlgEquiv.autCongr eB φ) P) ∧
            (ξ (AlgEquiv.autCongr eB φ) : ℂ) = χ p ∧
            ∀ x : 𝓞 principalK, (p : 𝓞 principalK) ∣ x ^ p - AlgEquiv.autCongr eB φ • x) ∧
        ∀ N H : ℕ, 0 < H → H ≤ N → ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
          let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i
          let θK := fun j => ∑ i : Fin 4, ((n j i : ℕ) : principalK) * ![1, A, bK, A * bK] i
          let R := fun β : Fin 3 → ℕ => fun j =>
            θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
          let RK := fun β : Fin 3 → ℕ => fun j =>
            θK j ^ β 0 * (AlgEquiv.autCongr eB σ) (θK j) ^ β 1 *
              (AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) (θK j) ^ β 2
          ∀ order : ℕ ≃ (Fin 3 → ℕ),
            Monotone (fun i => order i 0 + H * order i 1 + H * order i 2) →
            ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)) (Δ : 𝓞 B),
              Set.range g = (greedyPivots B (R ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
              Set.range g = (greedyPivots principalK (RK ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
              (∀ T : ℕ, greedyPivots principalK (RK ∘ order) T = greedyPivots B (R ∘ order) T) ∧
              (∀ i, α i = order (g i)) ∧
              (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
              let ΔK := NumberField.RingOfIntegers.mapRingEquiv eB.toRingEquiv Δ
              (∀ j, eB (θ j) = θK j) ∧ (∀ β j, eB (R β j) = RK β j) ∧
              (ΔK : principalK) = eB (Δ : B) ∧
              (ΔK : principalK) = Matrix.det (fun i j => RK (α i) j) ∧ ΔK ≠ 0 ∧
              Algebra.norm ℚ (ΔK : principalK) = Algebra.norm ℚ (Δ : B) ∧
              Algebra.norm ℤ ΔK = Algebra.norm ℤ Δ ∧
              (∀ p r : ℕ,
                ((p : 𝓞 principalK) ^ r ∣ ΔK ↔ (p : 𝓞 B) ^ r ∣ Δ) ∧
                (ΔK ∈ (Ideal.span {(p : 𝓞 principalK)}) ^ r ↔ Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ r)) ∧
              (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                ΔK ∈ (Ideal.span {(p : 𝓞 principalK)}) ^ (∑ i, α i 0 / p)) ∧
              (∀ νK : principalK →+* ℂ, ∀ j, ‖νK (θK j)‖ ≤ 8 * N * Real.sqrt q) ∧
              (∀ νK : principalK →+* ℂ, ∀ β j,
                ‖νK (RK β j)‖ ≤ (8 * N * Real.sqrt q) ^ (β 0 + β 1 + β 2)) ∧
              (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (ΔK : principalK) : ℝ)| ≤
                (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                  ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                    (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  classical
  let L := CyclotomicField (8 * q) ℚ
  let : NumberField principalK := hPrincipal
  let A : principalK := eB a'
  let bK : principalK := eB b'
  have heA : eB a' = A := rfl
  have heB : eB b' = bK := rfl
  let φB : B →+* ℂ := principalK.val.toRingHom.comp eB.toRingHom
  have hφa : φB a' = Complex.sqrt (d : ℂ) := heBa
  have hφb : φB b' = (Real.sqrt 2 : ℂ) := heBb
  let w := v.map eB.toLinearEquiv
  have hbasis :=
    biquadratic_basis_group_transport eB v a' b' hv hint hdegree
      σ τ hσa hσb hτa hτb hcard hall hcomm
  have hw := hbasis.1
  have hwIntegral := hbasis.2.1
  have hwDegree := hbasis.2.2.1
  have hGaloisK := hbasis.2.2.2.1
  have hsignK := hbasis.2.2.2.2.1
  have hcardK := hbasis.2.2.2.2.2.1
  have hallK := hbasis.2.2.2.2.2.2.1
  have hcommK := hbasis.2.2.2.2.2.2.2
  have hclassified :=
    source_principal_character_field_transport q χ hreal hprim hne hfield
      d a hchar hdisc hfund hformula B principalK a' hcoeA eB heBa
  let Kχ := hclassified.choose
  let νL := hclassified.choose_spec.choose
  have hfielddata := hclassified.choose_spec.choose_spec
  have hKχeq := hfielddata.1
  have hνB := hfielddata.2.1
  have hχmap := hfielddata.2.2.1
  let eχ := hfielddata.2.2.2.choose
  have heχ := hfielddata.2.2.2.choose_spec.1
  let hKχ := hfielddata.2.2.2.choose_spec.2.choose
  have hclass := hfielddata.2.2.2.choose_spec.2.choose_spec
  let : NumberField Kχ := hKχ
  have hdiscrKχ := hclass.1
  have hsignKχ := hclass.2.1
  have hfundKχ := hclass.2.2.1
  have habsKχ := hclass.2.2.2.1
  have hKχne := hclass.2.2.2.2
  have hcoeff : biquadraticCoefficients (φB a') (φB b') =
      ![1, 1 / Complex.sqrt (d : ℂ), -(1 / (Real.sqrt 2 : ℂ)),
        -(1 / (Complex.sqrt (d : ℂ) * (Real.sqrt 2 : ℂ)))] := by
    simp only [hφa, hφb, biquadraticCoefficients, one_div]
  have hsame := source_same_witness_hyperplane a' b' φB v hv σ τ hσa hσb hτa hτb
  rw [hφa, hφb] at hsame
  have hc := hsame.1
  let D := hsame.2.choose
  have hD := hsame.2.choose_spec
  have hprincipalCoefficients : LinearIndependent ℚ
      (![1, 1 / Complex.sqrt (d : ℂ), -(1 / (Real.sqrt 2 : ℂ)),
        -(1 / (Complex.sqrt (d : ℂ) * (Real.sqrt 2 : ℂ)))] : Fin 4 → ℂ) := by
    simpa only [biquadraticCoefficients, one_div] using hc
  have hprincipalDirections : ∀ j, (D j : Fin 4 → ℂ) =
      biquadraticDirections (Complex.sqrt (d : ℂ)) (Real.sqrt 2 : ℂ) j :=
    biquadratic_directions_eq_of_galois_coordinates a' b' φB σ τ
      hσa hσb hτa hτb hφa hφb (fun j => (D j : Fin 4 → ℂ)) hD
  have hdimension (N : ℕ) (n : Fin (N ^ 4) ≃ (Fin 4 → Fin N))
      (s : Set (Fin 3 → ℕ)) :
      Module.finrank ℂ (Submodule.span ℂ
        ((fun β : Fin 3 → ℕ => fun j => MvPolynomial.eval (fun _ => 1)
          (Geometry.invariantJet (fun k i => (D k : Fin 4 → ℂ) i) β
            (MvPolynomial.monomial
              (Finsupp.equivFunOnFinite.symm (fun i => (n j i : ℕ))) 1))) '' s)) =
      Module.finrank B (Submodule.span B
        ((fun β : Fin 3 → ℕ => fun j =>
          (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i) ^ β 0 *
          σ (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i) ^ β 1 *
          (σ * τ) (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, a', b', a' * b'] i) ^
            β 2) '' s)) := by
    have hD' := funext fun k => funext fun i => hD k i
    rw [hD']
    exact Geometry.finrank_span_source_jet_rows_eq φB ![1, a', b', a' * b']
      σ.toRingHom τ.toRingHom (fun j i => (n j i : ℕ)) s
  have haRat : a' ^ 2 = algebraMap ℚ B (d : ℚ) := by simpa using ha'
  have hA : A * A = algebraMap ℚ principalK (d : ℚ) := by
    calc
      A * A = eB (a' * a') := (map_mul eB a' a').symm
      _ = eB (algebraMap ℚ B (d : ℚ)) :=
        congrArg eB (by simpa [pow_two] using haRat)
      _ = algebraMap ℚ principalK (d : ℚ) := eB.commutes (d : ℚ)
  obtain ⟨hA0, heigen⟩ :=
    source_quadratic_group_character_principal_transport eB a' A (d : ℚ)
      haRat hA hns heA σ τ hσa hτa principalK.val q χ hfrob
  have hξ := heigen.1
  have hrange := heigen.2.1
  have hξσ := heigen.2.2.1
  have hξτ := heigen.2.2.2.1
  have hξστ := heigen.2.2.2.2.1
  have hprimes := heigen.2.2.2.2.2
  have hdreal : |(d : ℝ)| ≤ q := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (show (d.natAbs : ℝ) ≤ q from Nat.cast_le.mpr hbound)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hdeterminants := source_principal_determinant_suffix q χ d a' b' A bK σ τ
    eB heA heB ha' hb' hdreal hq hsource
  refine ⟨hw, hwIntegral, hwDegree, hGaloisK,
    hsignK, hcardK, hallK, hcommK, Kχ, νL, hKχeq, hνB, hχmap,
    eχ, heχ, hKχ, hdiscrKχ, hsignKχ, hfundKχ, habsKχ, hKχne,
    hcoeff, hprincipalCoefficients, D, hD, hprincipalDirections, hdimension,
    hA, hA0, hξ, hrange, hξσ, hξτ, hξστ, hunram, hprimes, hdeterminants⟩

theorem source_master_principal_same_data (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hfield : characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠
        sourceSqrtTwoField q (CyclotomicField (8 * q) ℚ)) :
    ∃ (d : ℤ) (a b : CyclotomicField (8 * q) ℚ),
      Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧ ¬ IsSquare (d : ℚ) ∧
      a ^ 2 = (d : CyclotomicField (8 * q) ℚ) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      ∃ (B : IntermediateField ℚ (CyclotomicField (8 * q) ℚ))
        (K : IntermediateField ℚ ℂ),
        B = IntermediateField.adjoin ℚ {a, b} ∧
        K = IntermediateField.adjoin ℚ {Complex.sqrt (d : ℂ), (Real.sqrt 2 : ℂ)} ∧
      ∃ aB bB : B, (aB : CyclotomicField (8 * q) ℚ) = a ∧
        (bB : CyclotomicField (8 * q) ℚ) = b ∧
      ∃ (v : Module.Basis (Fin 4) ℚ B) (σ τ : B ≃ₐ[ℚ] B),
        (∀ i, v i = ![1, aB, bB, aB * bB] i) ∧ (∀ i, IsIntegral ℤ (v i)) ∧
        Module.finrank ℚ B = 4 ∧
        σ aB = -aB ∧ σ bB = bB ∧ τ aB = aB ∧ τ bB = -bB ∧
        Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
        (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
        (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
      ∃ eB : B ≃ₐ[ℚ] K, (eB aB : ℂ) = Complex.sqrt (d : ℂ) ∧
        (eB bB : ℂ) = (Real.sqrt 2 : ℂ) ∧
      ∃ hK : NumberField K, letI := hK
        let A := eB aB
        let bK := eB bB
        let w := v.map eB.toLinearEquiv
        let φB := K.val.toRingHom.comp eB.toRingHom
        (∀ i, w i = ![1, A, bK, A * bK] i) ∧ (∀ i, IsIntegral ℤ (w i)) ∧
        Module.finrank ℚ K = 4 ∧ IsGalois ℚ K ∧
        (AlgEquiv.autCongr eB σ A = -A ∧ AlgEquiv.autCongr eB σ bK = bK ∧
          AlgEquiv.autCongr eB τ A = A ∧ AlgEquiv.autCongr eB τ bK = -bK) ∧
        Nat.card (K ≃ₐ[ℚ] K) = 4 ∧
        (∀ f : K ≃ₐ[ℚ] K, f = 1 ∨ f = AlgEquiv.autCongr eB σ ∨
          f = AlgEquiv.autCongr eB τ ∨ f = AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) ∧
        (∀ f g : K ≃ₐ[ℚ] K, Commute f g) ∧
      ∃ (Kχ : IntermediateField ℚ ℂ) (νL : CyclotomicField (8 * q) ℚ →ₐ[ℚ] ℂ),
        Kχ = IntermediateField.adjoin ℚ {Complex.sqrt (d : ℂ)} ∧
        (∀ x : B, νL x = (eB x : ℂ)) ∧
        (characterField (8 * q) (CyclotomicField (8 * q) ℚ) ℂ
          (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ)).map νL = Kχ ∧
      ∃ eχ : IntermediateField.adjoin ℚ ({a} : Set (CyclotomicField (8 * q) ℚ)) ≃ₐ[ℚ] Kχ,
        (∀ x, (eχ x : ℂ) = νL x) ∧
      ∃ hKχ : NumberField Kχ, letI := hKχ
        NumberField.discr Kχ = (if d % 4 = 1 then d else 4 * d) ∧
        NumberField.discr Kχ =
          integerCharacter χ (real_character_isQuadratic χ hreal) (-1) * (q : ℤ) ∧
        Int.IsFundamentalDiscr (NumberField.discr Kχ) ∧
        (NumberField.discr Kχ).natAbs = q ∧
        Kχ ≠ IntermediateField.adjoin ℚ {(Real.sqrt 2 : ℂ)} ∧
        biquadraticCoefficients (φB aB) (φB bB) =
          ![1, 1 / Complex.sqrt (d : ℂ), -(1 / (Real.sqrt 2 : ℂ)),
            -(1 / (Complex.sqrt (d : ℂ) * (Real.sqrt 2 : ℂ)))] ∧
        LinearIndependent ℚ
          (![1, 1 / Complex.sqrt (d : ℂ), -(1 / (Real.sqrt 2 : ℂ)),
            -(1 / (Complex.sqrt (d : ℂ) * (Real.sqrt 2 : ℂ)))] : Fin 4 → ℂ) ∧
      ∃ D : Module.Basis (Fin 3) ℂ
          (LinearMap.ker (biquadraticForm (Complex.sqrt (d : ℂ)) (Real.sqrt 2 : ℂ))),
        (∀ j i, (D j : Fin 4 → ℂ) i =
          φB ((![![1, aB, bB, aB * bB], (fun i => σ (![1, aB, bB, aB * bB] i)),
            (fun i => (σ * τ) (![1, aB, bB, aB * bB] i))] : Fin 3 → Fin 4 → B) j i)) ∧
        (∀ j, (D j : Fin 4 → ℂ) =
          biquadraticDirections (Complex.sqrt (d : ℂ)) (Real.sqrt 2 : ℂ) j) ∧
        (∀ (N : ℕ) (n : Fin (N ^ 4) ≃ (Fin 4 → Fin N)) (s : Set (Fin 3 → ℕ)),
          Module.finrank ℂ (Submodule.span ℂ
            ((fun β : Fin 3 → ℕ => fun j => MvPolynomial.eval (fun _ => 1)
              (Geometry.invariantJet (fun k i => (D k : Fin 4 → ℂ) i) β
                (MvPolynomial.monomial
                  (Finsupp.equivFunOnFinite.symm (fun i => (n j i : ℕ))) 1))) '' s)) =
          Module.finrank B (Submodule.span B
            ((fun β : Fin 3 → ℕ => fun j =>
              (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, aB, bB, aB * bB] i) ^ β 0 *
              σ (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, aB, bB, aB * bB] i) ^ β 1 *
              (σ * τ) (∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, aB, bB, aB * bB] i) ^
                β 2) '' s))) ∧
      ∃ (hA : A * A = algebraMap ℚ K (d : ℚ)) (hA0 : A ≠ 0),
        let ξ := quadraticEigencharacter A (d : ℚ) hA hA0
        (∀ f, f A = ξ f * A) ∧ (∀ f, ξ f = 1 ∨ ξ f = -1) ∧
        ξ (AlgEquiv.autCongr eB σ) = -1 ∧ ξ (AlgEquiv.autCongr eB τ) = 1 ∧
        ξ (AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) = -1 ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q →
          Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
          ∃ φ : B ≃ₐ[ℚ] B, (φ = σ ∨ φ = σ * τ) ∧
            (∀ (P : Ideal (𝓞 K)) (_ : P.IsPrime), P.LiesOver (Ideal.span {(p : ℤ)}) →
              IsArithFrobAt ℤ (AlgEquiv.autCongr eB φ) P) ∧
            (ξ (AlgEquiv.autCongr eB φ) : ℂ) = χ p ∧
            ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - AlgEquiv.autCongr eB φ • x) ∧
        ∀ N H : ℕ, 0 < H → H ≤ N → ∀ n : Fin (N ^ 4) ≃ (Fin 4 → Fin N),
          let θ := fun j => ∑ i : Fin 4, ((n j i : ℕ) : B) * ![1, aB, bB, aB * bB] i
          let θK := fun j => ∑ i : Fin 4, ((n j i : ℕ) : K) * ![1, A, bK, A * bK] i
          let R := fun β : Fin 3 → ℕ => fun j =>
            θ j ^ β 0 * σ (θ j) ^ β 1 * (σ * τ) (θ j) ^ β 2
          let RK := fun β : Fin 3 → ℕ => fun j =>
            θK j ^ β 0 * (AlgEquiv.autCongr eB σ) (θK j) ^ β 1 *
              (AlgEquiv.autCongr eB σ * AlgEquiv.autCongr eB τ) (θK j) ^ β 2
          ∀ order : ℕ ≃ (Fin 3 → ℕ),
            Monotone (fun i => order i 0 + H * order i 1 + H * order i 2) →
            ∃ (g : Fin (N ^ 4) ↪o ℕ) (α : Fin (N ^ 4) ↪ (Fin 3 → ℕ)) (Δ : 𝓞 B),
              Set.range g = (greedyPivots B (R ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
              Set.range g = (greedyPivots K (RK ∘ order) (weightedJetIndices H (N ^ 4 - 1)).card : Set ℕ) ∧
              (∀ T : ℕ, greedyPivots K (RK ∘ order) T = greedyPivots B (R ∘ order) T) ∧
              (∀ i, α i = order (g i)) ∧
              (Δ : B) = Matrix.det (fun i j => R (α i) j) ∧
              let ΔK := NumberField.RingOfIntegers.mapRingEquiv eB.toRingEquiv Δ
              (∀ j, eB (θ j) = θK j) ∧ (∀ β j, eB (R β j) = RK β j) ∧
              (ΔK : K) = eB (Δ : B) ∧
              (ΔK : K) = Matrix.det (fun i j => RK (α i) j) ∧ ΔK ≠ 0 ∧
              Algebra.norm ℚ (ΔK : K) = Algebra.norm ℚ (Δ : B) ∧
              Algebra.norm ℤ ΔK = Algebra.norm ℤ Δ ∧
              (∀ p r : ℕ,
                ((p : 𝓞 K) ^ r ∣ ΔK ↔ (p : 𝓞 B) ^ r ∣ Δ) ∧
                (ΔK ∈ (Ideal.span {(p : 𝓞 K)}) ^ r ↔ Δ ∈ (Ideal.span {(p : 𝓞 B)}) ^ r)) ∧
              (∀ p : ℕ, p.Prime → H < p → ¬ p ∣ 2 * q → χ p = -1 →
                ΔK ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p)) ∧
              (∀ νK : K →+* ℂ, ∀ j, ‖νK (θK j)‖ ≤ 8 * N * Real.sqrt q) ∧
              (∀ νK : K →+* ℂ, ∀ β j,
                ‖νK (RK β j)‖ ≤ (8 * N * Real.sqrt q) ^ (β 0 + β 1 + β 2)) ∧
              (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ (ΔK : K) : ℝ)| ≤
                (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
                  ((∑ i, (α i 0 : ℝ)) + (∑ i, ((α i 1 : ℝ) + α i 2))) *
                    (Real.log N + 1 / 2 * Real.log q + Real.log 8) := by
  classical
  obtain ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar, hdisc, hfund, hformula,
    B, principalK, hB, hK, a', b', hcoeA, hcoeB, ha', hb',
    v, hv, hint, hdegree, σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm,
    eB, heBa, heBb, hPrincipal, hfrob, hunram, hsource⟩ :=
    source_master_principal_opaque_prefix q χ hreal hprim hne hfield
  let : NumberField principalK := hPrincipal
  refine ⟨d, a, b, hd, hbound, hddiv, hns, ha, hb, hchar,
    B, principalK, hB, hK, a', b', hcoeA, hcoeB, v, σ, τ,
    hv, hint, hdegree, hσa, hσb, hτa, hτb, hcard, hall, hcomm,
    eB, heBa, heBb, hPrincipal, ?_⟩
  exact source_principal_existing_data_completion q χ hreal hprim hne hfield
    d a hbound hns hchar hdisc hfund hformula B principalK a' b' hcoeA ha' hb'
    v hv hint hdegree σ τ hσa hσb hτa hτb hcard hall hcomm
    eB heBa heBb hPrincipal hfrob hunram hsource

end WeightedTorusJets


end SiegelZeros

end OAI
