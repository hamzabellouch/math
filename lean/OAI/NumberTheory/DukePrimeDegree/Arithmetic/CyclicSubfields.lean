import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicRealCharacters
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.PermutationEuler

namespace OAI

/-!
# Cyclic subfield factors

For an intermediate field in a cyclic extension, the incomplete zeta
function is the product of exactly those Hecke factors whose characters
are trivial on the fixing subgroup. These subfield orders determine the
real character selected by a simple zero, without general Artin induction.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

section Quotient

variable {C : Type*} [CommGroup C] [Finite C]
local instance (D : Subgroup C) : Fintype (C ⧸ D →* ℂˣ) := Fintype.ofFinite _

theorem quotient_translation_euler (D : Subgroup C) (g : C) (z : ℂ) :
    (LinearMap.id - z •
      (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm (β := C ⧸ D) g⁻¹)).toLinearMap).det =
        ∏ η : C ⧸ D →* ℂˣ, (1 - z * (η (QuotientGroup.mk g) : ℂ)) := by
  let b := (complexMulBasis (C ⧸ D)).reindex (Equiv.inv (C ⧸ D →* ℂˣ))
  have hb (η : C ⧸ D →* ℂˣ) (q : C ⧸ D) : b η q = ((η⁻¹) q : ℂ) := by
    simp [b, complexMulBasis_apply]
  apply euler_det_eq_prod_of_eigenbasis b
  intro η
  funext q
  change b η (g⁻¹ • q) = (η (QuotientGroup.mk g) : ℂ) * b η q
  rw [hb, hb]
  change ((η⁻¹) ((QuotientGroup.mk g)⁻¹ * q) : ℂ) = _
  simp only [map_mul, map_inv, MonoidHom.inv_apply, inv_inv, Units.val_mul]

theorem sum_quotient_orders_of_unique_character
    (D : Subgroup C) (m : (C →* ℂˣ) → WithTop ℤ) (χ : C →* ℂˣ)
    (hχ : m χ = 1) (hrest : ∀ φ, φ ≠ χ → m φ = 0) :
    (∑ η : C ⧸ D →* ℂˣ, m (η.comp (QuotientGroup.mk' D))) =
      if D ≤ χ.ker then 1 else 0 := by
  by_cases hD : D ≤ χ.ker
  · rw [ite_eq_left hD]
    let η₀ := QuotientGroup.lift D χ hD
    have he : η₀.comp (QuotientGroup.mk' D) = χ := rfl
    rw [Finset.sum_eq_single η₀]
    · rw [he, hχ]
    · intro η _ hη
      apply hrest
      intro h
      apply hη
      apply MonoidHom.ext
      intro q
      induction q using Quotient.inductionOn
      rename_i c
      exact congrArg (fun φ : C →* ℂˣ => φ c) h
    · simp
  · rw [ite_eq_right hD]
    apply Finset.sum_eq_zero
    intro η _
    apply hrest
    intro h
    apply hD
    intro c hc
    change χ c = 1
    rw [← h]
    change η (QuotientGroup.mk c) = 1
    rw [(QuotientGroup.eq_one_iff c).mpr hc, map_one]

end Quotient

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance (L : IntermediateField F E) :
    Fintype ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ) := Fintype.ofFinite _

theorem cyclic_subfield_local_euler
    (L : IntermediateField F E) {N : ℕ}
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    cosetRationalEuler F E L N p s =
      ∏ η : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ,
        ∏ P : idealsOverPrime F p.val,
          (1 - ArtinSeries.idealTerm
            (η.comp (QuotientGroup.mk' L.fixingSubgroup)) N hs P.val)⁻¹ := by
  by_cases hp : p.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hp,
      ArtinSeries.local_euler_bad F E _ p hp hs, Finset.prod_const_one]
  rw [cosetRationalEuler, ite_eq_right hp, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro P _
  let PP := rationalPrimeSpectrum F p P
  have hP := (mem_idealsOverPrime_iff F p.property.ne_zero P.val).mp P.property
  have hc : IsCoprime P.val (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := by
    apply Ideal.isCoprime_iff_codisjoint.mpr
    apply Codisjoint.mono ((Ideal.span_singleton_le_iff_mem _).mpr hP.2) le_rfl
    exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr
      (p.property.coprime_iff_not_dvd.mpr hp).cast).codisjoint
  have he (η : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ) :
      ArtinSeries.idealTerm (η.comp (QuotientGroup.mk' L.fixingSubgroup)) N hs P.val =
        (η (QuotientGroup.mk (primeFrobenius F E PP)) : ℂ) *
          (Ideal.absNorm P.val : ℂ)^(-s) := by
    rw [ArtinSeries.idealTerm_apply]
    change artinCoefficient F E (η.comp (QuotientGroup.mk' L.fixingSubgroup)) N
      PP.asIdeal * _ = _
    have hc' : IsCoprime PP.asIdeal (ThetaConstruction.rationalModulusIdeal (𝓞 F) N) := hc
    rw [artinCoefficient, dite_eq_left PP.ne_bot, ite_eq_left hc', idealHom_prime]
    rfl
  rw [quotient_translation_euler, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro η _
  rw [he]
  congr 2
  ring

theorem cyclic_subfield_artin_product
    (L : IntermediateField F E) {N : ℕ} (hN : 0 < N)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s * removedEulerPolynomial L N s =
      ∏ η : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ,
        artinDirichlet F E (η.comp (QuotientGroup.mk' L.fixingSubgroup)) N s := by
  have hA := hasProd_prod
    (s := (Finset.univ : Finset ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ)))
    (fun η _ => ArtinSeries.dirichlet_hasProd (F := F) (E := E)
      (η.comp (QuotientGroup.mk' L.fixingSubgroup)) N hs)
  exact (cosetRationalEuler_hasProd F E L N hN hD hs).unique
    (hA.congr_fun (fun p => cyclic_subfield_local_euler L p hs))

variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
variable {d e N : ℕ} [NeZero N]

omit [NumberField.IsTotallyReal E] in
theorem cyclic_subfield_sum_orders
    (L : IntermediateField F E) [NumberField.IsTotallyReal L]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (τ : OrderedEmbeddings (e + 1) L) (he : finrank ℚ L = e + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ η : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ,
      meromorphicOrderAt (cyclicHeckeFactor σ hn ψ
        (η.comp (QuotientGroup.mk' L.fixingSubgroup))) (β : ℂ)) =
      meromorphicOrderAt (completedThetaXi τ he) (β : ℂ) := by
  let χ := fun η : (E ≃ₐ[F] E) ⧸ L.fixingSubgroup →* ℂˣ =>
    η.comp (QuotientGroup.mk' L.fixingSubgroup)
  have hp : AnalyticOnNhd ℂ (fun z => ∏ η, cyclicHeckeFactor σ hn ψ (χ η) z)
      ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    exact Finset.analyticAt_fun_prod Finset.univ
      (fun η _ => cyclicHeckeFactor_analytic σ hn ψ (χ η) z hz)
  have hq : AnalyticOnNhd ℂ (cosetMeromorphic τ he N) ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    rw [cosetMeromorphic_eq_factor]
    exact (cosetXiFactor_analyticAt N (by simpa using (not_or.mp hz).1)
      (by simpa using (not_or.mp hz).2)).mul
        ((completedThetaXi_entire τ he).analyticAt z)
  have heq := analytic_off_zero_one_eq_of_real_eq hp hq (fun s hs => by
    rw [cosetMeromorphic_eq_dedekindZeta τ he N hs,
      cyclic_subfield_artin_product L (NeZero.pos N) hD hs]
    exact Finset.prod_congr rfl (fun η _ =>
      cyclicHeckeFactor_eq_artinDirichlet σ hn ψ hid hψ (χ η) hs))
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hv : (fun z => ∏ η, cyclicHeckeFactor σ hn ψ (χ η) z) =ᶠ[𝓝[≠] (β : ℂ)]
      cosetMeromorphic τ he N := by
    have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
    exact heq hz
  have H := meromorphicOrderAt_congr hv
  rw [meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun η => cyclicHeckeFactor σ hn ψ (χ η))
    (fun η _ => (cyclicHeckeFactor_analytic σ hn ψ (χ η) (β : ℂ) hβ).meromorphicAt),
    cosetMeromorphic_order_eq τ he N hβ0 hβ1] at H
  exact H

omit [NumberField.IsTotallyReal E] in
theorem cyclic_subfield_order_of_unique_character
    (L : IntermediateField F E) [NumberField.IsTotallyReal L]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (τ : OrderedEmbeddings (e + 1) L) (he : finrank ℚ L = e + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (χ : (E ≃ₐ[F] E) →* ℂˣ)
    (hχ : meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ) = 1)
    (hrest : ∀ φ, φ ≠ χ →
      meromorphicOrderAt (cyclicHeckeFactor σ hn ψ φ) (β : ℂ) = 0) :
    meromorphicOrderAt (completedThetaXi τ he) (β : ℂ) =
      if L.fixingSubgroup ≤ χ.ker then 1 else 0 := by
  rw [← cyclic_subfield_sum_orders L σ hn τ he ψ hid hψ hD hβ0 hβ1]
  exact sum_quotient_orders_of_unique_character L.fixingSubgroup _ χ hχ hrest

end DukePrimeDegree

end

end OAI
