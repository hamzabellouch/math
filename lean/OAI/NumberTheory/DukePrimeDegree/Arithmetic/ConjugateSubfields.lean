import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ZetaOrder
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.PermutationEuler

namespace OAI

/-!
# Conjugate subfields have the same zeta zero order

Conjugate subgroups have the same permutation character. The
character-to-Euler identity identifies their actual incomplete Dedekind
zeta functions, and analytic continuation identifies their zero orders.
-/

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

theorem permutation_character_conjugate_subgroup
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (a g : G) :
    (Representation.ofMulAction ℂ G (G ⧸ H.map (MulAut.conj a).toMonoidHom)).character g =
      (Representation.ofMulAction ℂ G (G ⧸ H)).character g := by
  let H' := H.map (MulAut.conj a).toMonoidHom
  have hcard : Fintype.card H' = Fintype.card H := by
    exact Fintype.card_congr (H.equivMapOfInjective
      (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).toEquiv.symm
  have hsum : (∑ x : G, if x⁻¹ * g * x ∈ H' then (1 : ℂ) else 0) =
      ∑ x : G, if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0 := by
    apply Fintype.sum_equiv (Equiv.mulRight a)
    intro x
    have hmem : x⁻¹ * g * x ∈ H' ↔ (x * a)⁻¹ * g * (x * a) ∈ H := by
      rw [Subgroup.mem_map_equiv]
      simp only [MulAut.conj_symm_apply, mul_inv_rev, mul_assoc]
    change (if x⁻¹ * g * x ∈ H' then (1 : ℂ) else 0) =
      if (x * a)⁻¹ * g * (x * a) ∈ H then 1 else 0
    rw [hmem]
  rw [conjugacy_indicator_sum_eq_card_mul_character,
    conjugacy_indicator_sum_eq_card_mul_character, hcard] at hsum
  exact mul_left_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := H)) hsum

theorem permutation_euler_eq_of_character_eq
    {G : Type*} [Group G] [Fintype G] (H J : Subgroup G)
    (hχ : ∀ g, (Representation.ofMulAction ℂ G (G ⧸ H)).character g =
      (Representation.ofMulAction ℂ G (G ⧸ J)).character g)
    (g : G) (z : ℂ) :
    (LinearMap.id - z • Representation.ofMulAction ℂ G (G ⧸ H) g).det =
      (LinearMap.id - z • Representation.ofMulAction ℂ G (G ⧸ J) g).det := by
  let : Fintype (Subgroup G) := Fintype.ofFinite _
  let p : Subgroup G → ℕ := fun S => if S = H then 1 else 0
  let q : Subgroup G → ℕ := fun S => if S = J then 1 else 0
  have h := euler_det_products_eq_of_characters
    (V := fun S : Subgroup G => MonoidAlgebra ℂ (G ⧸ S))
    (fun S => Representation.ofMulAction ℂ G (G ⧸ S)) p q
    (fun g => by simpa [p, q] using hχ g) g z
  simpa [p, q] using h

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
local instance : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _

theorem cosetRationalEuler_eq_of_permutation_characters
    (L M : IntermediateField F E)
    (hχ : ∀ g,
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup)).character g =
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ M.fixingSubgroup)).character g)
    (N : ℕ) (p : Nat.Primes) (s : ℂ) :
    cosetRationalEuler F E L N p s = cosetRationalEuler F E M N p s := by
  by_cases hp : p.val ∣ N
  · simp only [cosetRationalEuler, ite_eq_left hp]
  simp only [cosetRationalEuler, ite_eq_right hp]
  apply Finset.prod_congr rfl
  intro P _
  congr 1
  rw [← permutation_euler_det_eq, ← permutation_euler_det_eq]
  exact permutation_euler_eq_of_character_eq L.fixingSubgroup M.fixingSubgroup hχ _ _

theorem coset_real_eq_of_permutation_characters
    (L M : IntermediateField F E)
    [NumberField.IsTotallyReal L] [NumberField.IsTotallyReal M]
    (hχ : ∀ g,
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup)).character g =
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ M.fixingSubgroup)).character g)
    {N : ℕ} (hN : 0 < N) (hD : (NumberField.discr E).natAbs ∣ N)
    (s : ℝ) (hs : 1 < s) :
    cosetMeromorphic (canonicalRealEmbeddings L) (degreePred_spec L) N s =
      cosetMeromorphic (canonicalRealEmbeddings M) (degreePred_spec M) N s := by
  have hs' : 1 < (s : ℂ).re := hs
  have hL := (actual_coset_meromorphic_pairing F E L (canonicalRealEmbeddings L)
    (degreePred_spec L) N hN hD).2.1 (s : ℂ) hs'
  have hM := (actual_coset_meromorphic_pairing F E M (canonicalRealEmbeddings M)
    (degreePred_spec M) N hN hD).2.1 (s : ℂ) hs'
  exact hL.unique (hM.congr_fun (fun p =>
    cosetRationalEuler_eq_of_permutation_characters L M hχ N p s))

theorem zetaZeroOrder_eq_of_permutation_characters
    (L M : IntermediateField F E)
    [NumberField.IsTotallyReal L] [NumberField.IsTotallyReal M]
    (hχ : ∀ g,
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ L.fixingSubgroup)).character g =
      (Representation.ofMulAction ℂ (E ≃ₐ[F] E) ((E ≃ₐ[F] E) ⧸ M.fixingSubgroup)).character g)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder L β = zetaZeroOrder M β := by
  let N := (NumberField.discr E).natAbs
  have hN : 0 < N := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  let σ := canonicalRealEmbeddings L
  let τ := canonicalRealEmbeddings M
  have heq := analytic_off_zero_one_eq_of_real_eq
    (coset_analytic_off_zero_one σ (degreePred_spec L) N)
    (coset_analytic_off_zero_one τ (degreePred_spec M) N)
    (coset_real_eq_of_permutation_characters L M hχ hN (dvd_refl _))
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  have hv : cosetMeromorphic σ (degreePred_spec L) N =ᶠ[𝓝[≠] (β : ℂ)]
      cosetMeromorphic τ (degreePred_spec M) N := by
    have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
    exact heq hz
  rw [zetaZeroOrder_eq_coset_order σ (degreePred_spec L) N hβ0 hβ1,
    zetaZeroOrder_eq_coset_order τ (degreePred_spec M) N hβ0 hβ1]
  exact meromorphicOrderAt_congr hv

theorem zetaZeroOrder_fixedField_conjugate
    [NumberField.IsTotallyReal E]
    (H : Subgroup (E ≃ₐ[F] E)) (a : E ≃ₐ[F] E)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    let : NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
      NumberField.IsTotallyReal.of_algebra _ E
    letI : NumberField.IsTotallyReal
        (IntermediateField.fixedField (H.map (MulAut.conj a).toMonoidHom)) :=
      NumberField.IsTotallyReal.of_algebra _ E
    zetaZeroOrder (IntermediateField.fixedField H) β =
      zetaZeroOrder (IntermediateField.fixedField (H.map (MulAut.conj a).toMonoidHom)) β := by
  let : NumberField.IsTotallyReal (IntermediateField.fixedField H) :=
    NumberField.IsTotallyReal.of_algebra _ E
  let : NumberField.IsTotallyReal
      (IntermediateField.fixedField (H.map (MulAut.conj a).toMonoidHom)) :=
    NumberField.IsTotallyReal.of_algebra _ E
  apply zetaZeroOrder_eq_of_permutation_characters _ _ _ hβ0 hβ1
  intro g
  rw [IntermediateField.fixingSubgroup_fixedField,
    IntermediateField.fixingSubgroup_fixedField]
  exact (permutation_character_conjugate_subgroup H a g).symm

end DukePrimeDegree

end

end OAI
