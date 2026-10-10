import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicContinuation
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkCharacters

namespace OAI

/-!
# Real characters at a simple real zero

The actual Frobenius ideal character commutes with complex conjugation.
Uniqueness of the entire nonprincipal Hecke continuation therefore makes
the cyclic zero orders conjugation invariant. At a simple real zero the
unique contributing character is real-valued.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open Module

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

@[simp] theorem conjugateLinearCharacter_conjugate {C : Type*} [Group C]
    (χ : C →* ℂˣ) :
    conjugateLinearCharacter (conjugateLinearCharacter χ) = χ := by
  ext g
  simp only [conjugateLinearCharacter_apply, starRingEnd_apply, star_star]

@[simp] theorem conjugateLinearCharacter_one {C : Type*} [Group C] :
    conjugateLinearCharacter (1 : C →* ℂˣ) = 1 := by
  ext g
  simp [conjugateLinearCharacter]

theorem conjugateLinearCharacter_ne_one {C : Type*} [Group C]
    {χ : C →* ℂˣ} (hχ : χ ≠ 1) : conjugateLinearCharacter χ ≠ 1 := by
  intro h
  have := congrArg conjugateLinearCharacter h
  exact hχ (by simpa using this)

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

theorem conjugate_artin_idealHom (χ : (E ≃ₐ[F] E) →* ℂˣ) :
    idealHom F E (conjugateLinearCharacter χ) =
      (Units.map (starRingEnd ℂ).toMonoidHom).comp (idealHom F E χ) := by
  apply MonoidHom.ext
  intro I
  change (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      conjugateLinearCharacter χ (primeFrobenius F E v) ^
        FractionalIdeal.count F v I.val) =
    Units.map (starRingEnd ℂ).toMonoidHom
      (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        χ (primeFrobenius F E v) ^ FractionalIdeal.count F v I.val)
  rw [MonoidHom.map_finprod _ (finite_factor_support F E χ I)]
  apply finprod_congr
  intro v
  rw [map_zpow]
  rfl

omit [NumberField E] [IsGalois F E] in
theorem nonprincipalContinued_eq_of_idealHom
    [NumberField.IsTotallyReal F] {d N : ℕ} [NeZero N]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (ψ φ : EvenRayCharacter F N) (hψ : ψ.IsNonprincipal)
    (hφ : φ.IsNonprincipal) (hid : ψ.idealHom = φ.idealHom) :
    ψ.nonprincipalContinued σ hn = φ.nonprincipalContinued σ hn := by
  apply entire_eq_of_real_eq (ψ.nonprincipalContinued_entire σ hn)
    (φ.nonprincipalContinued_entire σ hn)
  intro r hr
  rw [ψ.nonprincipalContinued_eq_dirichlet σ hn hψ hr,
    φ.nonprincipalContinued_eq_dirichlet σ hn hφ hr,
    ψ.dirichlet_eq_ideal_tsum hr, φ.dirichlet_eq_ideal_tsum hr]
  apply tsum_congr
  intro I
  simp only [EvenRayCharacter.idealTerm_apply, EvenRayCharacter.allCoefficient, hid]

theorem cyclicHeckeFactor_order_conjugation
    [NumberField.IsTotallyReal F] {d N : ℕ} [NeZero N]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) (β : ℝ) :
    meromorphicOrderAt (cyclicHeckeFactor σ hn ψ (conjugateLinearCharacter χ))
        (β : ℂ) =
      meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ) := by
  by_cases hχ : χ = 1
  · simp [hχ]
  have hc := conjugateLinearCharacter_ne_one hχ
  simp only [cyclicHeckeFactor, ite_eq_right hχ, ite_eq_right hc]
  have he : (ψ (conjugateLinearCharacter χ)).idealHom = (ψ χ).conjugate.idealHom := by
    rw [hid, conjugate_artin_idealHom]
    change _ = (Units.map (starRingEnd ℂ).toMonoidHom).comp (ψ χ).idealHom
    rw [hid]
  rw [nonprincipalContinued_eq_of_idealHom σ hn _ _ (hψ _ hc)
    ((ψ χ).conjugate_isNonprincipal (hψ χ hχ)) he]
  simpa only [Complex.conj_ofReal] using
    (ψ χ).nonprincipalContinued_order_conjugation σ hn (hψ χ hχ) (β : ℂ)

theorem real_character_of_simple_cyclic_zero
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
    [Fintype ((E ≃ₐ[F] E) →* ℂˣ)] {d N : ℕ} [NeZero N]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsum : (∑ χ, meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ)) = 1) :
    ∃ χ : (E ≃ₐ[F] E) →* ℂˣ,
      meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ) = 1 ∧
      (∀ φ, φ ≠ χ → meromorphicOrderAt (cyclicHeckeFactor σ hn ψ φ) (β : ℂ) = 0) ∧
      ∀ g, (χ g : ℂ).im = 0 := by
  choose m hm using fun χ =>
    cyclicHeckeFactor_finite_nonnegative_order σ hn ψ hψ χ hβ0 hβ1
  have hm1 : ∑ χ, m χ = 1 := by
    simp only [hm] at hsum
    exact_mod_cast hsum
  have hmc : ∀ χ, m (conjugateLinearCharacter χ) = m χ := by
    intro χ
    have H := cyclicHeckeFactor_order_conjugation σ hn ψ hid hψ χ β
    rw [hm, hm] at H
    exact_mod_cast H
  obtain ⟨χ, hχ, hrest, hreal⟩ :=
    real_character_of_simple_conjugate_orders m hm1 hmc
  refine ⟨χ, ?_, ?_, hreal⟩
  · rw [hm, hχ]
    rfl
  · intro φ hφ
    rw [hm, hrest φ hφ]
    rfl

end DukePrimeDegree

end

end OAI
