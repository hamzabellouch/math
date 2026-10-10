import OAI.AlgebraicGeometry.StableCoordinate.LaurentWeightObstruction

namespace OAI

/-!
# An integral weight coaction on a homogeneous principal quotient

This construction supplies the fiber-weight action for the actual
presentation `k[a,d,b,c,u]/(ac-bd-1)`.  It works for an arbitrary
weighted-homogeneous principal relation and uses genuine quotient algebra
homomorphisms.  Its hypotheses are construction data, not assumptions added
to the principal package.
-/

namespace StableCoordinate
namespace HomogeneousQuotientWeight

open MvPolynomial
open scoped LaurentPolynomial

noncomputable section

variable {k σ : Type*} [CommRing k]

/-- The principal quotient determined by a relation. -/
abbrev QuotientRing (H : MvPolynomial σ k) :=
  MvPolynomial σ k ⧸ Ideal.span ({H} : Set (MvPolynomial σ k))

/-- The coordinate images in a principal quotient. -/
def generator (H : MvPolynomial σ k) (i : σ) : QuotientRing H :=
  Ideal.Quotient.mk _ (X i)

@[simp]
theorem aeval_variable (H : MvPolynomial σ k) (p : MvPolynomial σ k) :
    aeval (generator H) p = (Ideal.Quotient.mkₐ k _ :
      MvPolynomial σ k →ₐ[k] QuotientRing H) p := by
  have h : aeval (generator H) = (Ideal.Quotient.mkₐ k _ :
      MvPolynomial σ k →ₐ[k] QuotientRing H) := by
    ext i
    simp [generator]
  exact congrArg (fun f => f p) h

@[simp]
theorem defining_relation_zero (H : MvPolynomial σ k) :
    (Ideal.Quotient.mkₐ k _ : MvPolynomial σ k →ₐ[k] QuotientRing H) H = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton H)

/-- Weighted evaluation annihilates a weighted-homogeneous defining relation. -/
theorem weightedEval_relation_zero (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) :
    LaurentWeightObstruction.weightedEval w (generator H) H = 0 := by
  rw [LaurentWeightObstruction.weightedEval_of_homogeneous w (generator H) hH]
  simp

/-- The Laurent weight coaction on the principal quotient by a homogeneous relation. -/
def coaction (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) :
    QuotientRing H →ₐ[k] LaurentPolynomial (QuotientRing H) :=
  Ideal.Quotient.liftₐ _ (LaurentWeightObstruction.weightedEval w (generator H))
    (by
      intro p hp
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
      rw [map_mul, weightedEval_relation_zero w H hH, zero_mul])

@[simp]
theorem coaction_mk (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (p : MvPolynomial σ k) :
    coaction w H hH ((Ideal.Quotient.mkₐ k _ :
      MvPolynomial σ k →ₐ[k] QuotientRing H) p) =
      LaurentWeightObstruction.weightedEval w (generator H) p := rfl

@[simp]
theorem coaction_variable (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (i : σ) :
    coaction w H hH (generator H i) =
      AddMonoidAlgebra.single (w i) (generator H i) := by
  change LaurentWeightObstruction.weightedEval w (generator H) (X i) = _
  simp [LaurentWeightObstruction.weightedEval]

/-- A homogeneous polynomial representative gives the expected weight
identity in the quotient algebra. -/
theorem coaction_mk_of_homogeneous (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) {p : MvPolynomial σ k} {m : ℤ}
    (hp : p.IsWeightedHomogeneous w m) :
    coaction w H hH ((Ideal.Quotient.mkₐ k _ :
      MvPolynomial σ k →ₐ[k] QuotientRing H) p) =
      AddMonoidAlgebra.single m ((Ideal.Quotient.mkₐ k _ :
        MvPolynomial σ k →ₐ[k] QuotientRing H) p) := by
  rw [coaction_mk, LaurentWeightObstruction.weightedEval_of_homogeneous w (generator H) hp]
  simp

/-- Coefficients of the quotient coaction are the images of polynomial
weighted components.  In particular, component projection is independent
of the chosen representative. -/
theorem coeff_coaction_mk (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (p : MvPolynomial σ k) (m : ℤ) :
    (coaction w H hH ((Ideal.Quotient.mkₐ k _ :
      MvPolynomial σ k →ₐ[k] QuotientRing H) p)).coeff m =
      (Ideal.Quotient.mkₐ k _ : MvPolynomial σ k →ₐ[k] QuotientRing H)
        (weightedHomogeneousComponent w m p) := by
  rw [coaction_mk, LaurentWeightObstruction.coeff_weightedEval, aeval_variable]

/-- A well-defined linear projection to an integral weight in the quotient. -/
def component (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (m : ℤ) :
    QuotientRing H →ₗ[k] QuotientRing H :=
  (Finsupp.lapply m).comp
    ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (coaction w H hH).toLinearMap)

@[simp]
theorem component_apply (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (m : ℤ) (q : QuotientRing H) :
    component w H hH m q = (coaction w H hH q).coeff m := rfl

@[simp]
theorem component_mk (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (p : MvPolynomial σ k) (m : ℤ) :
    component w H hH m ((Ideal.Quotient.mkₐ k _ :
      MvPolynomial σ k →ₐ[k] QuotientRing H) p) =
      (Ideal.Quotient.mkₐ k _ : MvPolynomial σ k →ₐ[k] QuotientRing H)
        (weightedHomogeneousComponent w m p) := coeff_coaction_mk w H hH p m

/-- The image definition of a weight piece in a homogeneous principal quotient. -/
def piece (w : σ → ℤ) (H : MvPolynomial σ k) (m : ℤ) :
    Submodule k (QuotientRing H) :=
  (weightedHomogeneousSubmodule k w m).map
    (Ideal.Quotient.mkₐ k (Ideal.span ({H} : Set (MvPolynomial σ k)))).toLinearMap

/-- A projected component belongs to the corresponding image piece. -/
theorem component_mem_piece (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (m : ℤ) (q : QuotientRing H) :
    component w H hH m q ∈ piece w H m := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (Ideal.span {H}) q
  rw [component_mk]
  exact ⟨weightedHomogeneousComponent w m p,
    weightedHomogeneousComponent_isWeightedHomogeneous m p, rfl⟩

/-- Elements of an image piece have the corresponding single-monomial
coaction, and conversely the coaction identity detects the image piece. -/
theorem mem_piece_iff_coaction (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) (m : ℤ) (q : QuotientRing H) :
    q ∈ piece w H m ↔ coaction w H hH q = AddMonoidAlgebra.single m q := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact coaction_mk_of_homogeneous w H hH hp
  · intro hq
    have heq : component w H hH m q = q := by
      rw [component_apply, hq]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [← heq]
    exact component_mem_piece w H hH m q

/-- The quotient projections are identity on their own piece and zero on
all other pieces. -/
theorem component_of_mem_piece (w : σ → ℤ) (H : MvPolynomial σ k) {n : ℤ}
    (hH : H.IsWeightedHomogeneous w n) {m : ℤ} {q : QuotientRing H}
    (hq : q ∈ piece w H m) (r : ℤ) :
    component w H hH r q = if r = m then q else 0 := by
  rw [component_apply, (mem_piece_iff_coaction w H hH m q).mp hq]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : r = m
  · simp [h]
  · simp [h, Ne.symm h]

/-- Any two polynomial weighted-component projections commute. -/
theorem polynomial_components_commute (w₁ w₂ : σ → ℤ) (m₁ m₂ : ℤ)
    (p : MvPolynomial σ k) :
    weightedHomogeneousComponent w₁ m₁ (weightedHomogeneousComponent w₂ m₂ p) =
      weightedHomogeneousComponent w₂ m₂ (weightedHomogeneousComponent w₁ m₁ p) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent]
  by_cases h₁ : Finsupp.weight w₁ d = m₁ <;>
    by_cases h₂ : Finsupp.weight w₂ d = m₂ <;> simp [h₁, h₂]

/-- Compatible integral gradings descend to compatible component projections
on the actual same quotient. -/
theorem components_commute (w₁ w₂ : σ → ℤ) (H : MvPolynomial σ k) {n₁ n₂ : ℤ}
    (hH₁ : H.IsWeightedHomogeneous w₁ n₁) (hH₂ : H.IsWeightedHomogeneous w₂ n₂)
    (m₁ m₂ : ℤ) (q : QuotientRing H) :
    component w₁ H hH₁ m₁ (component w₂ H hH₂ m₂ q) =
      component w₂ H hH₂ m₂ (component w₁ H hH₁ m₁ q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (Ideal.span {H}) q
  simp only [component_mk, polynomial_components_commute]

end
end HomogeneousQuotientWeight
end StableCoordinate

end OAI
