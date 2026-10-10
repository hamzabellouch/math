import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import OAI.Computability.PerfectCompleteness.Algebra.AffineFunctionalDependence
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Machines.BinaryRankOneCount
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.LowerCrossRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section Evaluation

variable {K I N : Type*} [Field K] [Fintype I]
  [AddCommGroup N] [Module K N]

theorem evaluation_surjective (forms : I → Module.Dual K N)
    (hforms : LinearIndependent K forms) : Function.Surjective (LinearMap.pi forms) := by
  have hfun : LinearIndependent K (fun i => (forms i : N → K)) := by
    exact hforms.map' (LinearMap.ltoFun K N K K)
      (LinearMap.ker_eq_bot.mpr DFunLike.coe_injective)
  have hspan : Submodule.span K
      (Set.range (fun n : N => fun i : I => forms i n)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hfun
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

variable {J : Type*} [Fintype J]

def crossLinear (forms : I → Module.Dual K N) :
    (J → N) →ₗ[K] Matrix I J K where
  toFun y i j := forms i (y j)
  map_add' y z := by ext i j; exact map_add (forms i) (y j) (z j)
  map_smul' a y := by ext i j; exact map_smul (forms i) a (y j)

omit [Fintype J] in
theorem crossLinear_surjective (forms : I → Module.Dual K N)
    (hforms : LinearIndependent K forms) :
    Function.Surjective (crossLinear (J := J) forms) := by
  intro M
  have h := evaluation_surjective forms hforms
  choose y hy using (fun j : J => h (fun i => M i j))
  refine ⟨y, ?_⟩
  ext i j
  exact congrFun (hy j) i

end Evaluation

private theorem uniform_pushforward_perm {A : Type*} [Fintype A] [Nonempty A]
    (e : A ≃ A) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform A := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∑ x : A, if e x = y then (1 / (Fintype.card A : ℝ)) else 0) =
    1 / (Fintype.card A : ℝ)
  simp_rw [← e.eq_symm_apply]
  simp

section UniformCross

variable {I J N : Type*} [Fintype I] [Fintype J]
  [AddCommGroup N] [Module F2 N] [Fintype N]
  [Fintype (J → N)] [Fintype (Matrix I J F2)]

omit [Fintype N] [Fintype J] in
theorem affine_cross_uniform (forms : I → Module.Dual F2 N)
    (hforms : LinearIndependent F2 forms) (offset : Matrix I J F2) :
    (FiniteDistribution.uniform (J → N)).pushforward (Γ := Matrix I J F2)
        (fun y i j => offset i j + forms i (y j)) =
      FiniteDistribution.uniform (Matrix I J F2) := by
  calc
    _ = ((FiniteDistribution.uniform (J → N)).pushforward (Γ := Matrix I J F2)
        (crossLinear forms)).pushforward (Γ := Matrix I J F2)
        (fun M => offset + M) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (FiniteDistribution.uniform (Matrix I J F2)).pushforward (Γ := Matrix I J F2)
        (fun M => offset + M) := by
      rw [UniformLinearImage.uniform_pushforward_linearMap
        (crossLinear forms) (crossLinear_surjective forms hforms)]
    _ = _ := uniform_pushforward_perm (Equiv.addLeft offset)

end UniformCross


variable {H : Type*} [AddCommGroup H] [Module F2 H]
  [Fintype H] [FiniteDimensional F2 H]
  (F : H →ₗ[F2] Module.Dual F2 H) (N : Submodule F2 H)
  {m : Nat} (u v : Fin m → H)

def firstFunctionals (x : Fin m → N) (i : Fin m) : Module.Dual F2 N :=
  N.dualRestrict (F (u i + (x i : H)))

def crossMatrix (x y : Fin m → N) : Matrix (Fin m) (Fin m) F2 :=
  fun i j => F (u i + (x i : H)) (v j + (y j : H))

omit [FiniteDimensional F2 H] in
theorem crossMatrix_uniform_of_independent (x : Fin m → N)
    (hx : LinearIndependent F2 (firstFunctionals F N u x)) :
    (FiniteDistribution.uniform (Fin m → N)).pushforward
        (crossMatrix F N u v x) =
      FiniteDistribution.uniform (Matrix (Fin m) (Fin m) F2) := by
  have h := affine_cross_uniform (firstFunctionals F N u x) hx
    (fun i j => F (u i + (x i : H)) (v j))
  have heq : crossMatrix F N u v x =
      fun y i j => F (u i + (x i : H)) (v j) +
        firstFunctionals F N u x i (y j) := by
    funext y i j
    exact map_add (F (u i + (x i : H))) (v j) (y j : H)
  rw [heq]
  exact h

omit [FiniteDimensional F2 H] in
theorem conditional_rank_probability_le (x : Fin m → N)
    (hx : LinearIndependent F2 (firstFunctionals F N u x)) :
    (FiniteDistribution.uniform (Fin m → N)).probability
        (fun y => decide ((crossMatrix F N u v x y).rank ≤ 1)) ≤
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have h := congrArg (fun μ : FiniteDistribution (Matrix (Fin m) (Fin m) F2) =>
    μ.probability (fun M => decide (M.rank ≤ 1)))
    (crossMatrix_uniform_of_independent F N u v x hx)
  rw [FiniteDistribution.probability_pushforward] at h
  rw [h]
  exact BinaryRankOneCount.uniform_rank_le_one_probability_le m

private theorem probability_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A × B → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun a => ν.probability (fun b => event (a, b))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

omit [FiniteDimensional F2 H] in
theorem cross_rank_probability_le :
    ((FiniteDistribution.uniform (Fin m → N)).product
        (FiniteDistribution.uniform (Fin m → N))).probability
        (fun p => decide ((crossMatrix F N u v p.1 p.2).rank ≤ 1)) ≤
      (2 : ℝ) ^ m /
        (2 : ℝ) ^ Module.finrank F2
          (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  let : Fintype (Module.Dual F2 N) :=
    Fintype.ofInjective (fun f : Module.Dual F2 N => (f : N → F2))
      DFunLike.coe_injective
  let q : ℝ := (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m)
  have hq : 0 ≤ q := by positivity
  have hdep := AffineFunctionalDependence.dependence_probability_le
    (BilinearRestrictionRank.restrictForm F N)
    (fun i => N.dualRestrict (F (u i)))
  have hforms (x : Fin m → N) : firstFunctionals F N u x =
      fun i => N.dualRestrict (F (u i)) +
        BilinearRestrictionRank.restrictForm F N (x i) := by
    funext i
    simp [firstFunctionals, BilinearRestrictionRank.restrictForm, map_add]
  have hdep' : (FiniteDistribution.uniform (Fin m → N)).probability
      (fun x => decide (¬ LinearIndependent F2 (firstFunctionals F N u x))) ≤
        (2 : ℝ) ^ m /
          (2 : ℝ) ^ Module.finrank F2
            (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) := by
    simpa only [hforms] using hdep
  rw [probability_product]
  calc
    _ ≤ (FiniteDistribution.uniform (Fin m → N)).expectation
        (fun x => (if ¬ LinearIndependent F2 (firstFunctionals F N u x)
          then (1 : ℝ) else 0) + q) := by
      apply SmallBias.expectation_mono
      intro x
      by_cases hx : LinearIndependent F2 (firstFunctionals F N u x)
      · simpa only [hx, not_true_eq_false, ite_false, zero_add] using
          conditional_rank_probability_le F N u v x hx
      · simpa only [hx, not_false_eq_true, ite_true] using
          ((FiniteDistribution.uniform (Fin m → N)).probability_le_one
            (fun y => decide ((crossMatrix F N u v x y).rank ≤ 1))).trans
            (le_add_of_nonneg_right hq)
    _ = (FiniteDistribution.uniform (Fin m → N)).probability
        (fun x => decide (¬ LinearIndependent F2 (firstFunctionals F N u x))) + q := by
      simp [FiniteDistribution.expectation, FiniteDistribution.probability,
        mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
        ← Finset.sum_mul, FiniteDistribution.normalized, one_mul]
    _ ≤ _ := add_le_add hdep' (le_refl q)

def gramMatrix (x y : Fin m → N) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F2 :=
  let rows : Fin m ⊕ Fin m → H :=
    Sum.elim (fun i => u i + (x i : H)) (fun j => v j + (y j : H))
  fun i j => F (rows i) (rows j)

omit [Fintype H] [FiniteDimensional F2 H] in
theorem cross_rank_le_gram_rank (x y : Fin m → N) :
    (crossMatrix F N u v x y).rank ≤ (gramMatrix F N u v x y).rank :=
  Matrix.rank_submatrix_le (gramMatrix F N u v x y) Sum.inl Sum.inr

omit [FiniteDimensional F2 H] in
theorem gram_rank_probability_le :
    ((FiniteDistribution.uniform (Fin m → N)).product
        (FiniteDistribution.uniform (Fin m → N))).probability
        (fun p => decide ((gramMatrix F N u v p.1 p.2).rank ≤ 1)) ≤
      (2 : ℝ) ^ m /
        (2 : ℝ) ^ Module.finrank F2
          (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  apply le_trans _ (cross_rank_probability_le F N u v)
  apply FiniteDistribution.probability_mono
  intro p hp
  apply decide_eq_true
  exact (cross_rank_le_gram_rank F N u v p.1 p.2).trans (of_decide_eq_true hp)

theorem cross_rank_probability_le_of_rank_gt (r s : Nat)
    (hcodim : Module.finrank F2 (H ⧸ N) ≤ r)
    (hrank : s < Module.finrank F2 (LinearMap.range F)) :
    ((FiniteDistribution.uniform (Fin m → N)).product
        (FiniteDistribution.uniform (Fin m → N))).probability
        (fun p => decide ((crossMatrix F N u v p.1 p.2).rank ≤ 1)) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have hloss := BilinearRestrictionRank.rank_restrict_add_codim F N
  have hexp : s - 2 * r ≤ Module.finrank F2
      (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) := by omega
  apply (cross_rank_probability_le F N u v).trans
  apply add_le_add _ (le_refl _)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num) hexp)

theorem rank_le_of_cross_probability (r s : Nat) (α : ℝ)
    (hcodim : Module.finrank F2 (H ⧸ N) ≤ r)
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) < α)
    (hdensity : α ≤
      ((FiniteDistribution.uniform (Fin m → N)).product
          (FiniteDistribution.uniform (Fin m → N))).probability
          (fun p => decide ((crossMatrix F N u v p.1 p.2).rank ≤ 1))) :
    Module.finrank F2 (LinearMap.range F) ≤ s := by
  by_contra h
  have hbound := cross_rank_probability_le_of_rank_gt F N u v r s hcodim
    (Nat.lt_of_not_ge h)
  exact (not_le_of_gt herror) (hdensity.trans hbound)

end
end PerfectCompleteness.LowerCrossRank

end OAI
