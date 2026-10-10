import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.Positivity
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatent
import OAI.Computability.UniqueGames.Reduction.BinaryLinear

namespace OAI

section

namespace PerfectCompleteness.AffineFunctionalDependence

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

noncomputable section

private theorem probability_cover_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (cover : I → Ω → Bool)
    (hcover : ∀ x, event x = true → ∃ i, cover i x = true) :
    μ.probability event ≤ ∑ i, μ.probability (cover i) := by
  unfold FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · obtain ⟨i, hi⟩ := hcover x hx
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if cover j x then μ.weight x else 0) (a := i)
      (fun j _ => by split <;> first | exact μ.nonnegative x | exact le_rfl)
      (Finset.mem_univ i)
    simpa only [hx, hi, ite_true] using h
  · simp only [hx]
    apply Finset.sum_nonneg
    intro i _
    split
    · exact μ.nonnegative x
    · exact le_rfl

variable {N V : Type*} [AddCommGroup N] [Module F2 N]
  [AddCommGroup V] [Module F2 V] [Fintype N] [Fintype V]

theorem affine_zero_probability_le (f : N →ₗ[F2] V) (b : V) :
    (FiniteDistribution.uniform N).probability (fun x => decide (b + f x = 0)) ≤
      1 / (Fintype.card (LinearMap.range f) : ℝ) := by
  have hlaw := UniformLinearImage.uniform_pushforward_linearMap
    f.rangeRestrict f.surjective_rangeRestrict
  have hp := congrArg (fun μ : FiniteDistribution (LinearMap.range f) =>
    μ.probability (fun y => decide (b + (y : V) = 0))) hlaw
  rw [FiniteDistribution.probability_pushforward] at hp
  change (FiniteDistribution.uniform N).probability
    (fun x => decide (b + f x = 0)) = _ at hp
  rw [hp]
  by_cases hzero : ∃ y : LinearMap.range f, b + (y : V) = 0
  · obtain ⟨z, hz⟩ := hzero
    have hevent : (fun y : LinearMap.range f => decide (b + (y : V) = 0)) =
        (fun y => decide (y = z)) := by
      funext y
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro hy
        apply Subtype.ext
        exact add_left_cancel (hy.trans hz.symm)
      · rintro rfl
        exact hz
    rw [hevent, UniformLatent.probability_uniform_singleton]
  · have hz : ∀ y : LinearMap.range f, b + (y : V) ≠ 0 := by
      simpa only [not_exists] using hzero
    simp [FiniteDistribution.probability, hz]

variable {m : Nat}

def coefficientSum (c : Fin m → F2) : (Fin m → N) →ₗ[F2] N where
  toFun x := ∑ i, c i • x i
  map_add' x y := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, mul_comm, RingHom.id_apply]

@[simp] theorem coefficientSum_apply (c : Fin m → F2) (x : Fin m → N) :
    coefficientSum c x = ∑ i, c i • x i := rfl

theorem coefficientSum_surjective (c : Fin m → F2) (hc : c ≠ 0) :
    Function.Surjective (coefficientSum (N := N) c) := by
  have hcoord : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨i, hi⟩ := hcoord
  have hi1 : c i = 1 :=
    (UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (c i)).resolve_left hi
  intro n
  refine ⟨Function.update 0 i n, ?_⟩
  rw [coefficientSum_apply, Finset.sum_eq_single i]
  · simp [hi1]
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem relation_probability_le (f : N →ₗ[F2] V) (offsets : Fin m → V)
    (c : Fin m → F2) (hc : c ≠ 0) :
    (FiniteDistribution.uniform (Fin m → N)).probability
        (fun x => decide ((∑ i, c i • (offsets i + f (x i))) = 0)) ≤
      1 / (Fintype.card (LinearMap.range f) : ℝ) := by
  have hlaw := UniformLinearImage.uniform_pushforward_linearMap
    (coefficientSum (N := N) c) (coefficientSum_surjective c hc)
  have hp := congrArg (fun μ : FiniteDistribution N =>
    μ.probability (fun n => decide ((∑ i, c i • offsets i) + f n = 0))) hlaw
  rw [FiniteDistribution.probability_pushforward] at hp
  have hevent :
      (fun x : Fin m → N => decide ((∑ i, c i • (offsets i + f (x i))) = 0)) =
      (fun x => decide ((∑ i, c i • offsets i) + f (coefficientSum c x) = 0)) := by
    funext x
    simp only [coefficientSum_apply, smul_add, Finset.sum_add_distrib,
      map_sum, map_smul]
  rw [hevent, hp]
  exact affine_zero_probability_le f (∑ i, c i • offsets i)

theorem dependence_probability_le (f : N →ₗ[F2] V) (offsets : Fin m → V) :
    (FiniteDistribution.uniform (Fin m → N)).probability
        (fun x => decide (¬ LinearIndependent F2 (fun i => offsets i + f (x i)))) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ Module.finrank F2 (LinearMap.range f) := by
  let μ := FiniteDistribution.uniform (Fin m → N)
  let event := fun x : Fin m → N =>
    decide (¬ LinearIndependent F2 (fun i => offsets i + f (x i)))
  let cover := fun (c : Fin m → F2) (x : Fin m → N) =>
    decide (c ≠ 0 ∧ (∑ i, c i • (offsets i + f (x i))) = 0)
  have hcover : ∀ x, event x = true → ∃ c, cover c x = true := by
    intro x hx
    have hdep : ¬ LinearIndependent F2 (fun i => offsets i + f (x i)) :=
      of_decide_eq_true hx
    obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
    have hc0 : c ≠ 0 := by
      intro hz
      exact hi (congrFun hz i)
    refine ⟨c, ?_⟩
    exact decide_eq_true_eq.mpr ⟨hc0, hc⟩
  have hbound (c : Fin m → F2) :
      μ.probability (cover c) ≤ 1 / (Fintype.card (LinearMap.range f) : ℝ) := by
    by_cases hc : c = 0
    · subst c
      simp [cover, FiniteDistribution.probability]
    · simpa [μ, cover, hc] using relation_probability_le f offsets c hc
  calc
    μ.probability event ≤ ∑ c, μ.probability (cover c) :=
      probability_cover_le_sum μ event cover hcover
    _ ≤ ∑ _c : Fin m → F2, 1 / (Fintype.card (LinearMap.range f) : ℝ) :=
      Finset.sum_le_sum (fun c _ => hbound c)
    _ = (2 : ℝ) ^ m / (2 : ℝ) ^ Module.finrank F2 (LinearMap.range f) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin,
        Module.card_eq_pow_finrank (K := F2) (V := LinearMap.range f),
        show Fintype.card F2 = 2 by decide, Nat.cast_pow, Nat.cast_ofNat,
        mul_one_div]

end
end PerfectCompleteness.AffineFunctionalDependence

end

end OAI
