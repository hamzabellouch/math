import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkCharacters

namespace OAI

/-!
# Cyclic subgroup coefficients for Stark descent

Möbius inversion on the finite poset of cyclic subgroups expresses the
constant function as an integer combination of their indicators.
Averaging conjugates gives the denominator-cleared cyclic permutation
identity used to compare Dedekind zeta orders.
-/

open scoped BigOperators Classical

namespace DukePrimeDegree

private theorem finite_poset_upper_weights {α : Type*} [PartialOrder α]
    [Fintype α] : ∃ a : α → ℤ, ∀ C,
      (∑ D, if C ≤ D then a D else 0) = 1 := by
  classical
  let : LocallyFiniteOrder (WithTop α) := Fintype.toLocallyFiniteOrder
  let a : α → ℤ := fun C => -IncidenceAlgebra.mu ℤ (C : WithTop α) ⊤
  refine ⟨a, fun C => ?_⟩
  have h := IncidenceAlgebra.sum_Icc_mu_left (𝕜 := ℤ) (C : WithTop α) ⊤
  have hs : (∑ D : WithTop α,
      if (C : WithTop α) ≤ D then IncidenceAlgebra.mu ℤ D ⊤ else 0) = 0 := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun D : WithTop α => (C : WithTop α) ≤ D) =
        Finset.Icc (C : WithTop α) ⊤ := by
      ext D
      simp
    rw [he]
    simpa using h
  have hu : (Finset.univ : Finset (WithTop α)) =
      insert ⊤ (Finset.univ.image (fun D : α => (D : WithTop α))) := by
    ext D
    cases D using WithTop.recTopCoe <;> simp
  rw [hu, Finset.sum_insert (by simp),
    Finset.sum_image (fun _ _ _ _ h => WithTop.coe_injective h)] at hs
  simp only [show (C : WithTop α) ≤ ⊤ from le_top, ite_true,
    IncidenceAlgebra.mu_self, WithTop.coe_le_coe] at hs
  have he : (∑ D : α, if C ≤ D then a D else 0) =
      -(∑ D : α, if C ≤ D then IncidenceAlgebra.mu ℤ (D : WithTop α) ⊤ else 0) := by
    simp only [a, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D _
    split_ifs <;> simp
  rw [he]
  linarith

/-- The finite set of cyclic subgroups, retaining their actual subgroup
carrier. No choice of generators enters the coefficients. -/
abbrev CyclicSubgroups (G : Type*) [Group G] :=
  {H : Subgroup G // IsCyclic H}

noncomputable instance instFintypeCyclicSubgroups (G : Type*) [Group G] [Finite G] :
    Fintype (CyclicSubgroups G) := Fintype.ofFinite _

/-- Integer cyclic-subgroup indicator coefficients. -/
theorem exists_cyclic_indicator_coefficients
    (G : Type*) [Group G] [Finite G] :
    ∃ a : CyclicSubgroups G → ℤ, ∀ g : G,
      (∑ C, if g ∈ C.val then a C else 0) = 1 := by
  classical
  obtain ⟨a, ha⟩ := finite_poset_upper_weights (α := CyclicSubgroups G)
  refine ⟨a, fun g => ?_⟩
  let C : CyclicSubgroups G := ⟨Subgroup.zpowers g, inferInstance⟩
  convert ha C using 1
  apply Finset.sum_congr rfl
  intro D _
  have he : C ≤ D ↔ g ∈ D.val := by
    change Subgroup.zpowers g ≤ D.val ↔ g ∈ D.val
    exact Subgroup.zpowers_le
  simp only [he]

/-- Conjugacy averaging gives the denominator-cleared cyclic induction
identity, with coefficients independent of the group element. -/
theorem exists_cyclic_conjugacy_coefficients
    (G : Type*) [Group G] [Fintype G] :
    ∃ a : CyclicSubgroups G → ℤ, ∀ g : G,
      (∑ C, a C * ∑ x : G, if x⁻¹ * g * x ∈ C.val then (1 : ℤ) else 0) =
        Fintype.card G := by
  classical
  obtain ⟨a, ha⟩ := exists_cyclic_indicator_coefficients G
  refine ⟨a, fun g => ?_⟩
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (x : G) :
      (∑ C : CyclicSubgroups G, a C *
        (if x⁻¹ * g * x ∈ C.val then (1 : ℤ) else 0)) = 1 := by
    simpa only [mul_ite, mul_one, mul_zero] using ha (x⁻¹ * g * x)
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The permutation character counts fixed points in the actual coset
representation used by the Artin Euler factors. -/
theorem permutation_character_eq_fixed_sum
    {G Ω : Type*} [Monoid G] [Fintype Ω] [MulAction G Ω] (g : G) :
    (Representation.ofMulAction ℂ G Ω).character g =
      ∑ x : Ω, if g • x = x then (1 : ℂ) else 0 := by
  classical
  let b : Module.Basis Ω ℂ (MonoidAlgebra ℂ Ω) :=
    Finsupp.basisSingleOne.map (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [b, Finsupp.single_apply, eq_comm]

/-- Conjugacy counting and the coset permutation character differ by
exactly the subgroup order. -/
theorem conjugacy_indicator_sum_eq_card_mul_character
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (g : G) :
    (∑ x : G, if x⁻¹ * g * x ∈ H then (1 : ℂ) else 0) =
      Fintype.card H * (Representation.ofMulAction ℂ G (G ⧸ H)).character g := by
  classical
  let e := Subgroup.groupEquivQuotientProdSubgroup (s := H)
  have he (x : G) : (e x).1 = QuotientGroup.mk x := rfl
  have hf (x : G) : g • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x ↔
      x⁻¹ * g * x ∈ H := by
    change QuotientGroup.mk (g * x) = QuotientGroup.mk x ↔ _
    rw [eq_comm, QuotientGroup.eq]
    simp only [mul_assoc]
  calc
    _ = ∑ p : (G ⧸ H) × H, if g • p.1 = p.1 then (1 : ℂ) else 0 := by
      apply Fintype.sum_equiv e
      intro x
      simp only [he, hf]
    _ = Fintype.card H * ∑ q : G ⧸ H, if g • q = q then (1 : ℂ) else 0 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : g • q = q <;> simp [hq]
    _ = _ := by
      rw [permutation_character_eq_fixed_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : g • q = q <;> simp only [hq, ite_true, ite_false]

/-- Artin's cyclic permutation identity with integer coefficients after
clearing the single denominator `card G`. -/
theorem exists_cyclic_permutation_character_identity
    (G : Type*) [Group G] [Fintype G] :
    ∃ b : CyclicSubgroups G → ℤ, ∀ g : G,
      (∑ C, (b C : ℂ) *
        (Representation.ofMulAction ℂ G (G ⧸ C.val)).character g) =
          Fintype.card G := by
  classical
  obtain ⟨a, ha⟩ := exists_cyclic_conjugacy_coefficients G
  refine ⟨fun C => a C * Fintype.card C.val, fun g => ?_⟩
  have hcast : (∑ C, (a C : ℂ) *
      ∑ x : G, if x⁻¹ * g * x ∈ C.val then (1 : ℂ) else 0) = Fintype.card G := by
    exact_mod_cast ha g
  simp_rw [conjugacy_indicator_sum_eq_card_mul_character] at hcast
  simpa only [Int.cast_mul, Int.cast_natCast, mul_assoc] using hcast

end DukePrimeDegree

end OAI
