import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Foundations.LinearEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BucketSampler
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.UniformDifference

namespace OAI

section

namespace PerfectCompleteness.LowerDirectionFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {ℓ : Nat}

private theorem exists_pivot (a : Direction ℓ) : ∃ i : Fin ℓ, a.val i = 1 := by
  by_contra h
  apply a.property
  funext i
  rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (a.val i) with hz | ho
  · exact hz
  · exact False.elim (h ⟨i, ho⟩)

def pivot (a : Direction ℓ) : Fin ℓ := Classical.choose (exists_pivot a)

@[simp] theorem pivot_value (a : Direction ℓ) : a.val (pivot a) = 1 :=
  Classical.choose_spec (exists_pivot a)

abbrev Other (a : Direction ℓ) := {i : Fin ℓ // i ≠ pivot a}
abbrev Rows (H : Type*) (ℓ : Nat) := Fin ℓ → H
abbrev Complement (a : Direction ℓ) (H : Type*) := Other a → H

theorem scalar_count (a : Direction ℓ) : Fintype.card (Other a ⊕ Fin 2) = ℓ + 1 := by
  have h : ℓ = 1 + Fintype.card (Other a) := by
    simpa [Other] using
      (Fintype.sum_eq_add_sum_subtype_ne (fun _ : Fin ℓ => (1 : Nat)) (pivot a))
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

variable {H : Type*} [AddCommGroup H] [Module F2 H]

def complement (a : Direction ℓ) (S : Rows H ℓ) : Complement a H :=
  fun j => S j.val - a.val j.val • S (pivot a)

def restore (a : Direction ℓ) (c : Complement a H) (h : H) : Rows H ℓ :=
  fun i => if hi : i = pivot a then h else c ⟨i, hi⟩ + a.val i • h

@[simp] theorem restore_pivot (a : Direction ℓ) (c : Complement a H) (h : H) :
    restore a c h (pivot a) = h := by simp [restore]

@[simp] theorem restore_other (a : Direction ℓ) (c : Complement a H) (h : H)
    (j : Other a) : restore a c h j.val = c j + a.val j.val • h := by
  simp only [restore, dite_eq_right j.property]

@[simp] theorem complement_restore (a : Direction ℓ) (c : Complement a H) (h : H) :
    complement a (restore a c h) = c := by
  funext j
  simp only [complement, restore_other, restore_pivot, add_sub_cancel_right]

@[simp] theorem restore_complement (a : Direction ℓ) (S : Rows H ℓ) :
    restore a (complement a S) (S (pivot a)) = S := by
  funext i
  by_cases hi : i = pivot a
  · subst i
    exact restore_pivot a (complement a S) (S (pivot a))
  · simp only [restore, dite_eq_right hi, complement, sub_add_cancel]

def split (a : Direction ℓ) : Rows H ℓ ≃ Complement a H × H where
  toFun S := (complement a S, S (pivot a))
  invFun z := restore a z.1 z.2
  left_inv := restore_complement a
  right_inv z := Prod.ext (complement_restore a z.1 z.2) (restore_pivot a z.1 z.2)

@[simp] theorem split_apply (a : Direction ℓ) (S : Rows H ℓ) :
    split a S = (complement a S, S (pivot a)) := rfl

def replace (a : Direction ℓ) (S : Rows H ℓ) (fresh : H) : Rows H ℓ :=
  restore a (complement a S) fresh

@[simp] theorem complement_replace (a : Direction ℓ) (S : Rows H ℓ) (fresh : H) :
    complement a (replace a S fresh) = complement a S :=
  complement_restore a _ _

theorem replace_eq (a : Direction ℓ) (S : Rows H ℓ) (fresh : H) :
    replace a S fresh = S + BucketSampler.rankOne a.val (fresh - S (pivot a)) := by
  funext i
  by_cases hi : i = pivot a
  · subst i
    simp only [replace, restore_pivot, Pi.add_apply, BucketSampler.rankOne,
      pivot_value, one_smul]
    abel
  · simp only [replace, restore, dite_eq_right hi, complement, Pi.add_apply,
      BucketSampler.rankOne, smul_sub]
    abel

def fiberEquiv (a : Direction ℓ) (c : Complement a H) :
    H ≃ {S : Rows H ℓ // complement a S = c} where
  toFun h := ⟨restore a c h, complement_restore a c h⟩
  invFun S := S.val (pivot a)
  left_inv := restore_pivot a c
  right_inv S := by
    apply Subtype.ext
    change restore a c (S.val (pivot a)) = S.val
    exact (congrArg (fun c' => restore a c' (S.val (pivot a))) S.property.symm).trans
      (restore_complement a S.val)

instance fiberNonempty (a : Direction ℓ) (c : Complement a H) :
    Nonempty {S : Rows H ℓ // complement a S = c} := ⟨(fiberEquiv a c) 0⟩

theorem quotient_replace (a : Direction ℓ) (S : Rows H ℓ) (fresh : H)
    (eval : H →ₗ[F2] F2) :
    DirectionQuotient.proj a.val (fun i => eval (replace a S fresh i)) =
      DirectionQuotient.proj a.val (fun i => eval (S i)) := by
  have heq : (fun i => eval (replace a S fresh i)) =
      (fun i => eval (S i)) + eval (fresh - S (pivot a)) • a.val := by
    rw [replace_eq]
    funext i
    simp only [Pi.add_apply, BucketSampler.rankOne, map_add, map_smul,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [heq, map_add, map_smul]
  have hz : DirectionQuotient.proj a.val a.val = 0 :=
    (DirectionQuotient.proj_eq_zero_iff a.val a.val).mpr (Or.inr rfl)
  rw [hz, smul_zero, add_zero]

private theorem scalar_complement_eq (a : Direction ℓ) (x y : Fin ℓ → F2)
    (h : DirectionQuotient.proj a.val x = DirectionQuotient.proj a.val y)
    (i : Fin ℓ) :
    x i - a.val i * x (pivot a) = y i - a.val i * y (pivot a) := by
  rcases (DirectionQuotient.proj_eq_iff a.val x y).mp h with hz | ha
  · have hxy : x = y := sub_eq_zero.mp hz
    rw [hxy]
  · have hi : x i = y i + a.val i := by
      have h' := congrFun ha i
      change x i - y i = a.val i at h'
      exact ((sub_eq_iff_eq_add).mp h').trans (add_comm _ _)
    have hp : x (pivot a) = y (pivot a) + 1 := by
      have h' := congrFun ha (pivot a)
      change x (pivot a) - y (pivot a) = a.val (pivot a) at h'
      rw [pivot_value] at h'
      exact ((sub_eq_iff_eq_add).mp h').trans (add_comm _ _)
    rw [hi, hp]
    ring

section ActualFunctions

variable {X : Type*} (V : Submodule F2 (X → F2))

def quotientQuery (a : Direction ℓ) (S : Rows V ℓ) : X → DirectionQuotient.Space a.val :=
  fun x => DirectionQuotient.proj a.val (fun i => (S i).val x)

@[simp] theorem quotientQuery_replace (a : Direction ℓ) (S : Rows V ℓ) (fresh : V) :
    quotientQuery V a (replace a S fresh) = quotientQuery V a S := by
  funext x
  exact quotient_replace a S fresh (EvaluationMatrix.evaluation V x)

theorem quotientQuery_eq_iff (a : Direction ℓ) (S T : Rows V ℓ) :
    quotientQuery V a S = quotientQuery V a T ↔ complement a S = complement a T := by
  constructor
  · intro h
    funext j
    apply Subtype.ext
    funext x
    exact scalar_complement_eq a (fun i => (S i).val x) (fun i => (T i).val x)
      (congrFun h x) j.val
  · intro h
    have hT : replace a S (T (pivot a)) = T := by
      unfold replace
      rw [h, restore_complement]
    rw [← hT]
    exact (quotientQuery_replace V a S (T (pivot a))).symm

theorem response_replace {Y : Type*} (a : Direction ℓ)
    (read : (X → DirectionQuotient.Space a.val) → Y)
    (S : Rows V ℓ) (fresh : V) :
    read (quotientQuery V a (replace a S fresh)) = read (quotientQuery V a S) := by
  rw [quotientQuery_replace]

theorem ofRows_add_rankOne (a : Direction ℓ) (S : Rows V ℓ) (h : V) :
    EvaluationMatrix.ofRows V (S + BucketSampler.rankOne a.val h) =
      EvaluationMatrix.shift V (EvaluationMatrix.ofRows V S) a.val h := by
  apply LinearMap.ext
  intro q
  funext i
  change q (S i + a.val i • h) = q (S i) + q h * a.val i
  simp only [map_add, map_smul, smul_eq_mul, mul_comm]

theorem ofRows_replace (a : Direction ℓ) (S : Rows V ℓ) (fresh : V) :
    EvaluationMatrix.ofRows V (replace a S fresh) =
      EvaluationMatrix.shift V (EvaluationMatrix.ofRows V S) a.val
        (fresh - S (pivot a)) := by
  rw [replace_eq]
  exact ofRows_add_rankOne V a S _

end ActualFunctions

section Laws

variable [Fintype H]

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ)) =
    1 / (Fintype.card (A × B) : ℝ)
  simp only [Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]

theorem split_uniform (a : Direction ℓ) :
    (FiniteDistribution.uniform (Rows H ℓ)).pushforward (split a) =
      (FiniteDistribution.uniform (Complement a H)).product (FiniteDistribution.uniform H) := by
  rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  exact uniform_product.symm

theorem uniform_fiber (a : Direction ℓ) (c : Complement a H) :
    (FiniteDistribution.uniform H).pushforward (restore a c) =
      (FiniteDistribution.uniform {S : Rows H ℓ // complement a S = c}).pushforward
        Subtype.val := by
  have h := UniformConditioning.uniform_transport (fiberEquiv (H := H) a c)
  rw [FiniteDistribution.transport_eq_pushforward] at h
  have h' := congrArg
    (fun μ : FiniteDistribution {S : Rows H ℓ // complement a S = c} =>
      μ.pushforward (Subtype.val : {S : Rows H ℓ // complement a S = c} → Rows H ℓ)) h
  rw [FiniteDistribution.pushforward_comp] at h'
  exact h'

def pairCoordinates (a : Direction ℓ) :
    (Rows H ℓ × H) ≃ Complement a H × (H × H) where
  toFun z := (complement a z.1, (z.1 (pivot a), z.2))
  invFun z := (restore a z.1 z.2.1, z.2.2)
  left_inv z := Prod.ext (restore_complement a z.1) rfl
  right_inv z := Prod.ext (complement_restore a z.1 z.2.1)
    (Prod.ext (restore_pivot a z.1 z.2.1) rfl)

omit [Fintype H] in
@[simp] theorem pairCoordinates_apply (a : Direction ℓ) (z : Rows H ℓ × H) :
    pairCoordinates a z = (complement a z.1, (z.1 (pivot a), z.2)) := rfl

def fiberPairLaw (a : Direction ℓ) : FiniteDistribution (Rows H ℓ × Rows H ℓ) :=
  ((FiniteDistribution.uniform (Complement a H)).product
    ((FiniteDistribution.uniform H).product (FiniteDistribution.uniform H))).pushforward
      (fun z => (restore a z.1 z.2.1, restore a z.1 z.2.2))

theorem two_copy_law (a : Direction ℓ) :
    ((FiniteDistribution.uniform (Rows H ℓ)).product (FiniteDistribution.uniform H)).pushforward
      (fun z => (z.1, replace a z.1 z.2)) = fiberPairLaw (H := H) a := by
  have h :
      ((FiniteDistribution.uniform (Rows H ℓ)).product (FiniteDistribution.uniform H)).pushforward
        (pairCoordinates a) =
      (FiniteDistribution.uniform (Complement a H)).product
        ((FiniteDistribution.uniform H).product (FiniteDistribution.uniform H)) := by
    rw [uniform_product, uniform_product, uniform_product,
      ← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  have h' := congrArg
    (fun μ : FiniteDistribution (Complement a H × (H × H)) => μ.pushforward
      (fun z => (restore a z.1 z.2.1, restore a z.1 z.2.2))) h
  rw [FiniteDistribution.pushforward_comp] at h'
  simpa only [pairCoordinates_apply, restore_complement, replace, fiberPairLaw] using h'

theorem resampled_pair_law (μ : FiniteDistribution (Rows H ℓ)) (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform H)).pushforward
      (fun z => (z.1, replace a z.1 z.2)) =
    (μ.product (FiniteDistribution.uniform H)).pushforward
      (fun z => (z.1, z.1 + BucketSampler.rankOne a.val z.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution (Rows H ℓ × H) => ν.pushforward
      (fun z => (z.1, z.1 + BucketSampler.rankOne a.val z.2)))
    (UniformDifference.difference_law μ (fun S => S (pivot a)))
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [UniformDifference.difference, replace_eq] using h

theorem fiberPairLaw_eq_rankOne (a : Direction ℓ) :
    fiberPairLaw (H := H) a =
      ((FiniteDistribution.uniform (Rows H ℓ)).product (FiniteDistribution.uniform H)).pushforward
        (fun z => (z.1, z.1 + BucketSampler.rankOne a.val z.2)) := by
  rw [← two_copy_law]
  exact resampled_pair_law (FiniteDistribution.uniform (Rows H ℓ)) a

end Laws

section MatrixLaws

variable {X : Type*} (V : Submodule F2 (X → F2))
  [FiniteDimensional F2 V] [Fintype V]
  [Fintype (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))]

theorem matrix_pair_law (a : Direction ℓ) :
    (fiberPairLaw (H := V) a).pushforward
        (fun z => (EvaluationMatrix.ofRows V z.1, EvaluationMatrix.ofRows V z.2)) =
      ((FiniteDistribution.uniform (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))).product
        (FiniteDistribution.uniform V)).pushforward
          (fun z => (z.1, EvaluationMatrix.shift V z.1 a.val z.2)) := by
  have hprod :
      ((FiniteDistribution.uniform (Rows V ℓ)).product (FiniteDistribution.uniform V)).pushforward
          (fun z => (EvaluationMatrix.ofRows V z.1, z.2)) =
        (FiniteDistribution.uniform (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))).product
          (FiniteDistribution.uniform V) := by
    rw [uniform_product, uniform_product]
    change (FiniteDistribution.uniform (Rows V ℓ × V)).pushforward
      (Equiv.prodCongr (EvaluationMatrix.rowsEquiv V).symm (Equiv.refl V)) = _
    rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  have h := congrArg
    (fun μ : FiniteDistribution ((Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)) × V) =>
      μ.pushforward (fun z => (z.1, EvaluationMatrix.shift V z.1 a.val z.2))) hprod
  rw [FiniteDistribution.pushforward_comp] at h
  rw [fiberPairLaw_eq_rankOne, FiniteDistribution.pushforward_comp]
  simpa only [ofRows_add_rankOne] using h

end MatrixLaws
end
end PerfectCompleteness.LowerDirectionFiber

end

end OAI
