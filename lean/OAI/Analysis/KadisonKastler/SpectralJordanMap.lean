import OAI.Analysis.KadisonKastler.ProjectionJordanMap
import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.KadisonKastler.Jordan
import OAI.Analysis.FactorGeneration.SpectralApproximation

namespace OAI

/-! # Jordan structure of a unitary-preserving map on a von Neumann algebra

Projection phases give exact algebraic identities on finite spectral
sums. Norm approximation by those sums then gives adjoint and square
preservation; complex polarization gives the Jordan identity.
-/

namespace KadisonKastler

open scoped BigOperators ComplexStarModule

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private theorem orthogonal_sum_square {I : Type*} [Fintype I]
    (p : I → A) (c : I → ℂ) (hp : ∀ i, p i * p i = p i)
    (hpq : ∀ i j, i ≠ j → p i * p j = 0) :
    (∑ i, c i • p i) * (∑ i, c i • p i) = ∑ i, (c i ^ 2) • p i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_eq_single i]
  · rw [hp i, pow_two]
  · intro j _ hji
    rw [hpq i j hji.symm, smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Finite spectral sums retain adjoints and squares under the map. -/
theorem map_star_square_projection_sum {I : Type*} [Fintype I]
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p : I → A) (c : I → ℂ) (hp : ∀ i, IsStarProjection (p i))
    (hpq : ∀ i j, i ≠ j → p i * p j = 0) :
    F (star (∑ i, c i • p i)) = star (F (∑ i, c i • p i)) ∧
      F ((∑ i, c i • p i) * (∑ i, c i • p i)) =
        F (∑ i, c i • p i) * F (∑ i, c i • p i) := by
  have hFp (i : I) := map_isStarProjection_of_map_unitary F hF1 hFu (p i) (hp i)
  constructor
  · simp only [star_sum, star_smul, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hp i).isSelfAdjoint.star_eq, (hFp i).isSelfAdjoint.star_eq]
  · calc
      _ = F (∑ i, (c i ^ 2) • p i) := congrArg F
        (orthogonal_sum_square p c (fun i => (hp i).isIdempotentElem.eq) hpq)
      _ = ∑ i, (c i ^ 2) • F (p i) := by simp only [map_sum, map_smul]
      _ = (∑ i, c i • F (p i)) * (∑ i, c i • F (p i)) :=
        (orthogonal_sum_square (fun i => F (p i)) c
          (fun i => (hFp i).isIdempotentElem.eq)
          (fun i j hij => map_projection_mul_eq_zero_of_map_unitary F hF1 hFu
            (p i) (p j) (hp i) (hp j) (hpq i j hij))).symm
      _ = _ := by simp only [map_sum, map_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Normal elements are norm limits of finite spectral sums, so both
identities extend by continuity. -/
theorem map_star_square_normal_of_map_unitary
    (F : Algebra M →L[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary (Algebra M), F u ∈ unitary B)
    (x : Algebra M) (hx : IsStarNormal x) :
    F (star x) = star (F x) ∧ F (x * x) = F x * F x := by
  let S : Set (Algebra M) := {x | F (star x) = star (F x) ∧ F (x * x) = F x * F x}
  have hclosed : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  have hxcl : x ∈ closure S := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let : IsStarNormal x := hx
    obtain ⟨Q, c, hc⟩ := Generator.Tracial.exists_normal_spectral_approximation x ε hε
    refine ⟨∑ i, c i • (Q.piece i).val, ?_, ?_⟩
    · exact map_star_square_projection_sum F.toLinearMap hF1 hFu
        (fun i => (Q.piece i).val) c (fun i => (Q.piece i).property) Q.orthogonal
    · simpa only [dist_eq_norm] using hc
  rwa [hclosed.closure_eq] at hxcl

private theorem complex_square_expansion (a b : A) :
    (a + Complex.I • b) * (a + Complex.I • b) =
      a * a + Complex.I • (a * b + b * a) - b * b := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, neg_one_smul, smul_add]
  abel

private theorem map_jordan_of_three_squares (F : A →ₗ[ℂ] B) (a b : A)
    (ha : F (a * a) = F a * F a) (hb : F (b * b) = F b * F b)
    (hab : F ((a + b) * (a + b)) = F (a + b) * F (a + b)) :
    F (a * b + b * a) = F a * F b + F b * F a := by
  have he : (F a * F a + F (a * b + b * a)) + F b * F b =
      (F a * F a + (F a * F b + F b * F a)) + F b * F b := by
    calc
      _ = F ((a + b) * (a + b)) := by
        rw [show (a + b) * (a + b) = a * a + (a * b + b * a) + b * b by noncomm_ring]
        simp only [map_add, ha, hb]
      _ = F (a + b) * F (a + b) := hab
      _ = _ := by rw [map_add]; noncomm_ring
  exact add_left_cancel (add_right_cancel he)

/-- A continuous unital linear map preserving unitaries preserves all
adjoints and all squares on a von Neumann algebra. -/
theorem map_star_square_of_map_unitary
    (F : Algebra M →L[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary (Algebra M), F u ∈ unitary B) (x : Algebra M) :
    F (star x) = star (F x) ∧ F (x * x) = F x * F x := by
  let a : Algebra M := ℜ x
  let b : Algebra M := ℑ x
  have ha : IsSelfAdjoint a := (ℜ x).property
  have hb : IsSelfAdjoint b := (ℑ x).property
  have he : x = a + Complex.I • b := (realPart_add_I_smul_imaginaryPart x).symm
  have hfa := map_star_square_normal_of_map_unitary F hF1 hFu a ha.isStarNormal
  have hfb := map_star_square_normal_of_map_unitary F hF1 hFu b hb.isStarNormal
  have hfab := map_star_square_normal_of_map_unitary F hF1 hFu (a + b)
    (ha.add hb).isStarNormal
  have hcross : F (a * b + b * a) = F a * F b + F b * F a :=
    map_jordan_of_three_squares F.toLinearMap a b hfa.2 hfb.2 hfab.2
  constructor
  · rw [he]
    simp only [star_add, star_smul, map_add, map_smul, hfa.1, hfb.1]
  · rw [he, complex_square_expansion, map_sub, map_add, map_smul,
      hfa.2, hfb.2, hcross,
      map_add, map_smul, complex_square_expansion]

/-- The same map is a star-preserving Jordan map, ready for the
surjective orientation theorem. -/
theorem preservesJordan_of_map_unitary
    (F : Algebra M →L[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary (Algebra M), F u ∈ unitary B) :
    PreservesJordan F.toLinearMap := by
  intro x y
  exact map_jordan_of_three_squares F.toLinearMap x y
    (map_star_square_of_map_unitary F hF1 hFu x).2
    (map_star_square_of_map_unitary F hF1 hFu y).2
    (map_star_square_of_map_unitary F hF1 hFu (x + y)).2

end

end KadisonKastler

end OAI
