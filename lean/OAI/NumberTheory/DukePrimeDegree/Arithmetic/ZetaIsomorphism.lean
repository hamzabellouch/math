import OAI.NumberTheory.DukePrimeDegree.Arithmetic.SubfieldOrders
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.RationalZeroGap
import OAI.NumberTheory.PrimePackets.ZetaResidues

namespace OAI

/-!
# Continued zeta orders respect field isomorphisms

The Dirichlet coefficients are preserved by a number-field isomorphism.
Uniqueness of analytic continuation therefore preserves the zero order,
including for the bottom field in a normal closure.
-/

noncomputable section
open Filter Set
open scoped NumberField Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

lemma removedEulerPolynomial_one (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    removedEulerPolynomial K 1 s = 1 := by
  have hbad : badRationalPrimes 1 = ∅ := by
    ext p
    change (⟨p.val, p.property⟩ : Subtype Nat.Prime) ∈
      (1 : ℕ).primeFactors.subtype Nat.Prime ↔ p ∈ (∅ : Finset Nat.Primes)
    rw [Finset.mem_subtype]
    simp
  simp only [removedEulerPolynomial, hbad, Finset.prod_empty]

theorem zetaZeroOrder_algEquiv
    {K L : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (e : K ≃ₐ[ℚ] L) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = zetaZeroOrder L β := by
  let σ := canonicalRealEmbeddings K
  let τ := canonicalRealEmbeddings L
  have heq := analytic_off_zero_one_eq_of_real_eq
    (coset_analytic_off_zero_one σ (degreePred_spec K) 1)
    (coset_analytic_off_zero_one τ (degreePred_spec L) 1) (fun s hs => by
      rw [cosetMeromorphic_eq_dedekindZeta σ (degreePred_spec K) 1 hs,
        cosetMeromorphic_eq_dedekindZeta τ (degreePred_spec L) 1 hs,
        removedEulerPolynomial_one, removedEulerPolynomial_one,
        mul_one, mul_one]
      exact dedekindZeta_algEquiv e s)
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  apply meromorphicOrderAt_congr
  have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
  filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
  exact heq hz

theorem zetaMultiplicity_algEquiv
    {K L : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (e : K ≃ₐ[ℚ] L) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaMultiplicity K β = zetaMultiplicity L β := by
  unfold zetaMultiplicity
  rw [zetaZeroOrder_algEquiv e hβ0 hβ1]

theorem fixedFieldMultiplicity_top_eq
    {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
    [NumberField.IsTotallyReal E]
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    fixedFieldMultiplicity β (⊤ : Subgroup (E ≃ₐ[ℚ] E)) = zetaMultiplicity ℚ β := by
  unfold fixedFieldMultiplicity
  let e := (IntermediateField.equivOfEq (IsGalois.fixedField_top (F := ℚ) (E := E))).trans
    (IntermediateField.botEquiv ℚ E)
  exact zetaMultiplicity_algEquiv e hβ0 hβ1

theorem zetaMultiplicity_eq_zero_of_completed_ne_zero
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hzero : completedThetaXi σ hn (β : ℂ) ≠ 0) : zetaMultiplicity K β = 0 := by
  have hord : zetaZeroOrder K β = 0 := by
    rw [zetaZeroOrder_eq_completed_order σ hn hβ0 hβ1]
    exact ((completedThetaXi_entire σ hn).analyticAt _).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hzero
  simp [zetaMultiplicity, hord]

theorem rational_zetaMultiplicity_zero_scaled :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ, 4 ≤ L →
      ∀ β ∈ Icc (1 - a / L) 1, 0 < β → β < 1 → zetaMultiplicity ℚ β = 0 := by
  let σ := canonicalRealEmbeddings ℚ
  have hdeg : degreePred ℚ = 0 := by simp [degreePred]
  have hσ : OrderedEmbeddings 1 ℚ := by simpa only [hdeg, Nat.zero_add] using σ
  obtain ⟨a, ha, hz⟩ := rational_completedXi_nonzero_scaled hσ
  refine ⟨a, ha, fun L hL β hβ hβ0 hβ1 => ?_⟩
  exact zetaMultiplicity_eq_zero_of_completed_ne_zero hσ (by simp)
    hβ0 hβ1 (hz L hL β hβ)

end DukePrimeDegree

end

end OAI
