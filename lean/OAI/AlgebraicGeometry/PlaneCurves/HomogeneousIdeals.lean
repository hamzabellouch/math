import OAI.AlgebraicGeometry.PlaneCurves.RelationIdeals

namespace OAI

/-!
# Homogeneous relation components and principal cubic ideals
-/

section

/-! A polynomial vanishing on infinitely many scalar multiples of a fixed vector
has every homogeneous component vanishing there. This is finite polynomial algebra;
its application to automorphic section orbits is proved separately. -/
noncomputable section
namespace Nagata.Workers.W25
open scoped BigOperators

/-- Polynomial obtained by evaluating a multivariate polynomial on a scalar line. -/
def scalarLinePolynomial {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (P.totalDegree + 1),
    Polynomial.monomial n (MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P))

theorem eval_scalarLinePolynomial {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (t : ℂ) :
    (scalarLinePolynomial P x).eval t = MvPolynomial.eval (fun i => t * x i) P := by
  classical
  unfold scalarLinePolynomial
  rw [Polynomial.eval_finsetSum]
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval_monomial,
    Nagata.W16.homogeneous_eval_scale (MvPolynomial.homogeneousComponent_isHomogeneous n P)]
  exact mul_comm _ _

theorem coeff_scalarLinePolynomial {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (n : ℕ) :
    (scalarLinePolynomial P x).coeff n =
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P) := by
  classical
  by_cases hn : n < P.totalDegree + 1
  · simp [scalarLinePolynomial, Polynomial.coeff_monomial, hn]
  · have hdeg : P.totalDegree < n := by omega
    simp [scalarLinePolynomial, Polynomial.coeff_monomial, hn,
      MvPolynomial.homogeneousComponent_eq_zero n P hdeg]

theorem homogeneousComponent_eval_zero_of_infinite_scalars {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (hP : ∀ t ∈ S, MvPolynomial.eval (fun i => t * x i) P = 0) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P) = 0 := by
  have hzero : scalarLinePolynomial P x = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono (fun t ht => by
      change (scalarLinePolynomial P x).eval t = 0
      rw [eval_scalarLinePolynomial]
      exact hP t ht))
  rw [← coeff_scalarLinePolynomial, hzero, Polynomial.coeff_zero]

end Nagata.Workers.W25

end
end

section

/-! Common automorphy produces infinitely many scalar multiples at each nonzero
cover point. The argument uses finite sets, not an assumed density theorem. -/
noncomputable section
namespace Nagata.Workers.W25

/-- An everywhere nonzero recurrence with injective successive multipliers
cannot take only finitely many values. -/
theorem infinite_range_of_injective_multipliers (a b : ℕ → ℂ)
    (ha : ∀ n, a n ≠ 0) (hb : Function.Injective b)
    (hab : ∀ n, a (n + 1) = b n * a n) : (Set.range a).Infinite := by
  intro hfinite
  have hinj : Function.Injective (fun n => (a n, a (n + 1))) := by
    intro n m h
    have h0 : a n = a m := congrArg Prod.fst h
    have h1 : a (n + 1) = a (m + 1) := congrArg Prod.snd h
    apply hb
    apply mul_right_cancel₀ (ha n)
    rw [← hab n, h0, ← hab m]
    exact h1
  have hpair : (Set.range (fun n => (a n, a (n + 1)))).Finite :=
    (hfinite.prod hfinite).subset (by rintro _ ⟨n, rfl⟩; exact ⟨⟨n, rfl⟩, ⟨n+1, rfl⟩⟩)
  exact (Set.infinite_range_of_injective hinj) hpair

/-- The scalar accumulated along nonnegative iterates of the period. -/
def cubicOrbitScale (τ γ z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => γ * (τ ^ n * z) ^ (-3 : ℤ) * cubicOrbitScale τ γ z n

theorem cubicOrbitScale_ne_zero {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    cubicOrbitScale τ γ z n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ n ih => exact mul_ne_zero (mul_ne_zero hγ (zpow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hτ) hz))) ih

theorem cubic_section_eval_period_iterate {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hz : z ≠ 0) (s : Nagata.W08.automorphicSections τ 3 γ) (n : ℕ) :
    s.val (τ ^ n * z) = cubicOrbitScale τ γ z n * s.val z := by
  induction n with
  | zero => simp [cubicOrbitScale]
  | succ n ih =>
    rw [pow_succ, mul_comm (τ ^ n) τ, mul_assoc,
      s.property.2.2 _ (mul_ne_zero (pow_ne_zero _ hτ) hz), ih]
    simp only [cubicOrbitScale, mul_assoc]

/-- Distinct period powers give distinct cubic automorphy multipliers. -/
theorem cubic_period_multiplier_injective {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0) (hz : z ≠ 0) :
    Function.Injective (fun n : ℕ => γ * (τ ^ n * z) ^ (-3 : ℤ)) := by
  intro n m h
  have hnorm := congrArg norm h
  simp only [norm_mul, norm_zpow, norm_pow] at hnorm
  have hp := mul_left_cancel₀ (norm_ne_zero_iff.mpr hγ) hnorm
  have hb := (zpow_left_inj₀
    (mul_nonneg (pow_nonneg (norm_nonneg τ) n) (norm_nonneg z))
    (mul_nonneg (pow_nonneg (norm_nonneg τ) m) (norm_nonneg z))
    (by decide : (-3 : ℤ) ≠ 0)).mp hp
  have he := mul_right_cancel₀ (norm_ne_zero_iff.mpr hz) hb
  exact (pow_right_injective₀ (norm_pos_iff.mpr hτ) (ne_of_lt hτnorm)) he

/-- At every nonzero point, the common cubic period scalars have infinite range. -/
theorem cubicOrbitScale_infinite {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0) (hz : z ≠ 0) :
    (Set.range (cubicOrbitScale τ γ z)).Infinite :=
  infinite_range_of_injective_multipliers _ _
    (cubicOrbitScale_ne_zero hτ hγ hz)
    (cubic_period_multiplier_injective hτ hτnorm hγ hz) (fun _ => rfl)

end Nagata.Workers.W25

end
end

section

/-! Homogeneous-component closure of the actual relation ideal follows from
common automorphy, not from an assumption on the algebraic image. -/
namespace Nagata.Workers.W25

/-- Every homogeneous component of an actual section relation is again a relation.
The common degree-three automorphy supplies infinitely many scalar zeros at each
nonzero cover point. No injectivity or base-point-free hypothesis is needed. -/
theorem homogeneousComponent_mem_cubicSectionRelationIdeal {τ γ : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.automorphicSections τ 3 γ)
    (P : MvPolynomial (Fin 3) ℂ)
    (hP : P ∈ polynomialRelationIdeal (fun i => (b i).val)) (n : ℕ) :
    MvPolynomial.homogeneousComponent n P ∈
      polynomialRelationIdeal (fun i => (b i).val) := by
  apply (mem_polynomialRelationIdeal _ _).mpr
  intro z hz
  apply homogeneousComponent_eval_zero_of_infinite_scalars P (fun i => (b i).val z)
    (Set.range (cubicOrbitScale τ γ z)) (cubicOrbitScale_infinite hτ hτnorm hγ hz)
  rintro t ⟨k, rfl⟩
  have heval := (mem_polynomialRelationIdeal _ P).mp hP
    (τ ^ k * z) (mul_ne_zero (pow_ne_zero _ hτ) hz)
  have hfun : (fun i => cubicOrbitScale τ γ z k * (b i).val z) =
      (fun i => (b i).val (τ ^ k * z)) :=
    funext (fun i => (cubic_section_eval_period_iterate hτ hz (b i) k).symm)
  rw [hfun]
  exact heval

end Nagata.Workers.W25

end

section

/-! The actual section relation ideal is homogeneous in mathlib's ordinary
polynomial grading; its component-closure proof is supplied by period orbits. -/
namespace Nagata.Workers.W25
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicSectionRelationIdeal_isHomogeneous {τ γ : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.automorphicSections τ 3 γ) :
    (polynomialRelationIdeal (fun i => (b i).val)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) := by
  intro n P hP
  have hcomp (D : DirectSum.Decomposition
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) :
      (D.decompose' P n : MvPolynomial (Fin 3) ℂ) = MvPolynomial.homogeneousComponent n P := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  rw [← DirectSum.Decomposition.decompose'_eq, hcomp]
  exact homogeneousComponent_mem_cubicSectionRelationIdeal hτ hτnorm hγ b P hP n

end Nagata.Workers.W25

end

section

namespace Nagata.Workers.W25

theorem exists_actual_cubic_mem_relationIdeal {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.automorphicSections (τ : ℂ) 3 γ) :
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ P.IsHomogeneous 3 ∧
      P ∈ polynomialRelationIdeal (fun i => (b i).val) := by
  let := Nagata.Workers.W10.automorphicSection_finite hτ hτone
    (show (0 : ℤ) < 9 by decide) (pow_ne_zero 3 hγ)
  apply exists_cubic_mem_relationIdeal b
  rw [Nagata.Workers.W10.automorphicSection_finrank hτ hτone
    (show (0 : ℤ) < 9 by decide) (pow_ne_zero 3 hγ)]
  decide

theorem actualCubicSectionRelationIdeal_ne_bot {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.automorphicSections (τ : ℂ) 3 γ) :
    polynomialRelationIdeal (fun i => (b i).val) ≠ ⊥ := by
  obtain ⟨P, hP, _, hmem⟩ := exists_actual_cubic_mem_relationIdeal hτ hτone hγ b
  intro hzero
  rw [hzero, Ideal.mem_bot] at hmem
  exact hP hmem

end Nagata.Workers.W25

end

section

/-! Algebraic composition from two independent quotient coordinates to a
principal relation ideal. The independence input is explicit at this intermediate
interface and is to be discharged using the actual section basis. -/
namespace Nagata.Workers.W25
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_relation_generator_of_independent_quotient {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.automorphicSections (τ : ℂ) 3 γ)
    (hind : AlgebraicIndependent ℂ (fun i : Fin 2 =>
      Ideal.Quotient.mk (polynomialRelationIdeal (fun j => (b j).val))
        (MvPolynomial.X i.castSucc))) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous G.totalDegree ∧
      0 < G.totalDegree ∧ G.totalDegree ≤ 3 ∧
      polynomialRelationIdeal (fun i => (b i).val) = Ideal.span {G} := by
  let I := polynomialRelationIdeal (fun i => (b i).val)
  let : I.IsPrime := cubicSectionRelationIdeal_isPrime b
  have hheight : I.height ≤ 1 :=
    Nagata.W04.Dimension.height_le_one_of_independent_quotient I hind
  have hτne : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)
  have hτnorm : ‖(τ : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
  obtain ⟨G, hprime, hhom, hpos, hI⟩ :=
    Nagata.Workers.W30.homogeneous_height_one_prime_generator I
      (actualCubicSectionRelationIdeal_ne_bot hτ hτone hγ b) hheight
      (cubicSectionRelationIdeal_isHomogeneous hτne hτnorm hγ b)
  obtain ⟨P, hP, hPdegree, hPmem⟩ := exists_actual_cubic_mem_relationIdeal hτ hτone hγ b
  have hdvd : G ∣ P := Ideal.mem_span_singleton.mp (hI ▸ hPmem)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hP
  rw [hPdegree.totalDegree hP] at hle
  exact ⟨G, hprime, hhom, hpos, hle, hI⟩

end Nagata.Workers.W25

end

section

/-! Actual principal relation ideal of a basis of three automorphic sections.
Binary factorization, analytic primeness, automorphic homogeneity, and quotient
localization discharge every algebraic independence/height assumption. Exact
cubic degree and smoothness remain separate geometric steps. -/
namespace Nagata.Workers.W25
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualBasis_binaryCoordinates_algebraicIndependent {τ γ : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.automorphicSections τ 3 γ)) :
    AlgebraicIndependent ℂ (fun i : Fin 2 =>
      Ideal.Quotient.mk (polynomialRelationIdeal (fun j => (b j).val))
        (MvPolynomial.X i.castSucc)) := by
  apply Nagata.W02.algebraicIndependent_quotient_of_no_linear_relation Fin.castSucc
    (cubicSectionRelationIdeal_isPrime b)
    (cubicSectionRelationIdeal_isHomogeneous hτ hτnorm hγ b)
  intro a c hrel
  exact basis_pair_linear_relation_trivial b 0 1 (by decide) a c hrel

theorem exists_actual_relation_generator {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.automorphicSections (τ : ℂ) 3 γ)) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous G.totalDegree ∧
      0 < G.totalDegree ∧ G.totalDegree ≤ 3 ∧
      polynomialRelationIdeal (fun i => (b i).val) = Ideal.span {G} := by
  apply exists_relation_generator_of_independent_quotient hτ hτone hγ b
  apply actualBasis_binaryCoordinates_algebraicIndependent
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) _ hγ b
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone

/-- Exact pointwise kernel description for a proved prime homogeneous generator. -/
theorem exists_actual_relation_generator_with_noncancellation {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.automorphicSections (τ : ℂ) 3 γ)) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous G.totalDegree ∧
      0 < G.totalDegree ∧ G.totalDegree ≤ 3 ∧
      polynomialRelationIdeal (fun i => (b i).val) = Ideal.span {G} ∧
      ∀ P : MvPolynomial (Fin 3) ℂ, ¬ G ∣ P →
        ∃ z : ℂ, z ≠ 0 ∧ MvPolynomial.eval (fun i => (b i).val z) P ≠ 0 := by
  obtain ⟨G, hG, hhom, hpos, hle, hI⟩ := exists_actual_relation_generator hτ hτone hγ b
  exact ⟨G, hG, hhom, hpos, hle, hI,
    fun P hP => exists_eval_ne_zero_of_not_dvd_relation_generator _ G hI P hP⟩

end Nagata.Workers.W25

end

end OAI
