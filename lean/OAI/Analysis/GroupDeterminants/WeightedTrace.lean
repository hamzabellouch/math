import OAI.Analysis.GroupDeterminants.IndexedRepresentation

namespace OAI

universe uA

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section ClosedPair
variable {A : Type uA} [CStarAlgebra A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]

lemma trace_log_weightedPair_subalgebra (τ : A →L[ℝ] ℂ)
    (hτ : ∀ a ∈ D, ∀ b ∈ D, τ (a * b) = τ (b * a))
    (hstar : ∀ a, τ (star a) = star (τ a))
    (Q R : D) (hQ : Q * Q = Q) (hR : R * R = R)
    (hQR : Q * R = 0) (hRQ : R * Q = 0) (hQs : IsSelfAdjoint Q) (x : ℝ) :
    τ (CFC.log (star (weightedPair (Q : A) (R : A) (Real.exp x) (-Real.exp (-x)) (-1)) *
      weightedPair (Q : A) (R : A) (Real.exp x) (-Real.exp (-x)) (-1))) =
      (x * (2 * (τ ((Q : A) - (R : A))).re) : ℝ) := by
  cases subsingleton_or_nontrivial D with
  | inl h =>
    have hz : (0 : A) = 1 := congrArg (fun a : D => (a : A)) (Subsingleton.elim 0 1)
    let := subsingleton_of_zero_eq_one hz
    simp only [Subsingleton.elim (CFC.log _) (0 : A),
      Subsingleton.elim ((Q : A) - (R : A)) (0 : A), map_zero, Complex.zero_re,
      mul_zero, Complex.ofReal_zero]
  | inr h =>
    have H := trace_log_weightedPair (subTrace D τ) (subTrace_mul_comm D τ hτ)
      (subTrace_star D τ hstar) Q R hQ hR hQR hRQ hQs x
    let M := weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1)
    have hu : IsUnit M := weightedPair_unit Q R hQ hR hQR hRQ _ _ _
      (Real.exp_ne_zero x) (neg_ne_zero.mpr (Real.exp_ne_zero (-x))) (by norm_num)
    change τ ((CFC.log (star M * M) : D) : A) = _ at H
    rw [subalgebra_log_coe _ _ (IsSelfAdjoint.star_mul_self _) (hu.star.mul hu)] at H
    exact H

end ClosedPair

section IndexedTraceCalculus
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]

def indexedClosedRepresentation : Matrix I I (MonoidAlgebra ℂ G) →ₐ[ℂ]
    closedGroupAlgebra (G := G) (n := Fintype.card I) :=
  indexedComplexRepresentation.codRestrict closedGroupAlgebra.toSubalgebra indexedComplexRepresentation_mem

@[simp] lemma indexedClosedRepresentation_coe (A : Matrix I I (MonoidAlgebra ℂ G)) :
    (indexedClosedRepresentation A : Hilbert G (Fintype.card I) →L[ℂ] Hilbert G (Fintype.card I)) =
    indexedComplexRepresentation A := rfl

lemma indexedClosedRepresentation_star (A : Matrix I I (MonoidAlgebra ℂ G)) :
    indexedClosedRepresentation (star A) = star (indexedClosedRepresentation A) :=
  Subtype.ext (indexedComplexRepresentation_star A)

lemma indexed_trace_log_weightedPair (Q R : Matrix I I (MonoidAlgebra ℂ G))
    (hQ : Q * Q = Q) (hR : R * R = R) (hQR : Q * R = 0) (hRQ : R * Q = 0)
    (hQs : IsSelfAdjoint Q) (x : ℝ) :
    let M := indexedComplexRepresentation (weightedPair Q R (Real.exp x) (-Real.exp (-x)) (-1))
    groupTrace (CFC.log (star M * M)) =
      (x * (2 * (∑ i, ((Q - R) i i).coeff 1).re) : ℝ) := by
  let φ := indexedClosedRepresentation (G := G) (I := I)
  have hQ' : φ Q * φ Q = φ Q := by rw [← map_mul, hQ]
  have hR' : φ R * φ R = φ R := by rw [← map_mul, hR]
  have hQR' : φ Q * φ R = 0 := by rw [← map_mul, hQR, map_zero]
  have hRQ' : φ R * φ Q = 0 := by rw [← map_mul, hRQ, map_zero]
  have hQs' : IsSelfAdjoint (φ Q) := by
    change star (φ Q) = φ Q
    rw [← indexedClosedRepresentation_star, hQs.star_eq]
  have hcyc : ∀ a ∈ closedGroupAlgebra (G := G) (n := Fintype.card I),
      ∀ b ∈ closedGroupAlgebra, groupTraceCLM (a * b) = groupTraceCLM (b * a) := by
    intro a ha b hb
    simp only [groupTraceCLM_apply]
    exact groupTrace_closed_mul_comm ha hb
  have hstar : ∀ a : Hilbert G (Fintype.card I) →L[ℂ] Hilbert G (Fintype.card I),
      groupTraceCLM (star a) = star (groupTraceCLM a) := by
    simp only [groupTraceCLM_apply]
    exact groupTrace_star
  have H := trace_log_weightedPair_subalgebra closedGroupAlgebra
    (groupTraceCLM.restrictScalars ℝ) hcyc hstar (φ Q) (φ R) hQ' hR' hQR' hRQ' hQs' x
  change groupTraceCLM (G := G) (n := Fintype.card I) _ =
    ((x * (2 * (groupTraceCLM (G := G) (n := Fintype.card I) _).re) : ℝ) : ℂ) at H
  simp only [groupTraceCLM_apply, φ, indexedClosedRepresentation_coe] at H
  have hmap (a b c : ℝ) : indexedComplexRepresentation (weightedPair Q R a b c) =
      weightedPair (indexedComplexRepresentation Q) (indexedComplexRepresentation R) a b c := by
    simp only [weightedPair, map_add, map_sub, map_one, AlgHom.map_smul_of_tower]
  have ht : groupTrace (indexedComplexRepresentation Q - indexedComplexRepresentation R) =
      ∑ i, ((Q - R) i i).coeff 1 := by
    rw [← map_sub, indexedComplexRepresentation_trace]
  dsimp only
  rw [hmap]
  rw [ht] at H
  convert H using 1
  rfl

end IndexedTraceCalculus
end GroupRingDeterminant

end

end OAI
