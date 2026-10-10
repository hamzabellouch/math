import OAI.Analysis.FreeEntropy.WickSeries

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]
def reverseEquiv : List α ≃ List α where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

def residual (R : Series α) (v : α → ℝ) (i : α) : Series α :=
  FreeSeries.deriv i R - (v i : ℂ) • letter i
 theorem residual_heat (R : Series α) (v : α → ℝ) (u : ℝ) (i : α) :
    residual (R + (u : ℂ) • quadratic) (fun i => v i + u) i = residual R v i := by
  funext w
  simp only [residual, Pi.sub_apply, FreeSeries.deriv_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Complex.ofReal_add]
  have hq := congrFun (deriv_quadratic (α := α) i) w
  change quadratic (i::w) = letter i w at hq
  rw [hq]
  ring
 theorem cumulant_residual_identity (M : Series α) (hM : M [] = 1) (v : α → ℝ) (i : α) :
    conv M (subst M (residual (cumulants M) v i)) =
      FreeSeries.deriv i M - (v i : ℂ) • conv M (subst M (letter i)) := by
  rw [residual, subst_sub, subst_smul, conv_sub_right, conv_smul_right]
  congr 1
  have he := congrArg (FreeSeries.deriv i) (cumulants_equation hM)
  have he' : FreeSeries.deriv i M = FreeSeries.deriv i (subst M (cumulants M)) := by
    funext w
    simpa only [FreeSeries.deriv_apply, Pi.add_apply, unit_cons, zero_add] using congrFun he w
  rw [he', deriv_subst]
end FreeSeries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem series_reverseDerivative_hasSum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (f : Series (Fin n)) (w : List (Fin n)) :
    HasSum (fun js => f js.reverse * reverseDerivativeMoment τ X js w)
      (conv (wordMoment τ X) (subst (wordMoment τ X) f) w) := by
  let F : List (Fin n) → ℂ := fun js => f js *
    conv (wordMoment τ X) (subst (wordMoment τ X) (monomial js)) w
  have hs : HasSum (F ∘ (reverseEquiv (α := Fin n)))
      (conv (wordMoment τ X) (subst (wordMoment τ X) f) w) :=
    (reverseEquiv (α := Fin n)).hasSum_iff.mpr (conv_subst_hasSum (wordMoment τ X) f w)
  apply hs.congr_fun
  intro js
  change f js.reverse * reverseDerivativeMoment τ X js w =
    f js.reverse * conv (wordMoment τ X)
      (subst (wordMoment τ X) (monomial js.reverse)) w
  rw [reverseDerivativeMoment_monomial]
 theorem inner_selfAdjoint_word {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) = wordMoment τ X (i::w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hX i).star_eq]
  rfl
 theorem cumulant_residual_hasSum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i))
    (v : Fin n → ℝ) (i : Fin n) (w : List (Fin n)) :
    HasSum (fun js => residual (cumulants (wordMoment τ X)) v i js.reverse *
      reverseDerivativeMoment τ X js w)
      (inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) -
        (v i : ℂ) * derivativeMoment τ X i w) := by
  have hs := series_reverseDerivative_hasSum τ X (residual (cumulants (wordMoment τ X)) v i) w
  rw [cumulant_residual_identity _ (by simp), Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, FreeSeries.deriv_apply, ← derivativeMoment_series, ← inner_selfAdjoint_word τ X hX] at hs
  exact hs

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}

 theorem heat_cumulant_residual_hasSum (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (hsa : ∀ i, IsSelfAdjoint (X i))
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) (v : Fin n → ℝ) (i : Fin n) (w : List (Fin n)) :
    HasSum (fun js => residual (cumulants (wordMoment (tracialVector B N G) X)) v i js.reverse *
      reverseDerivativeMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) js w)
      (inner ℂ (heatTuple X (fun i => semicircularN (σ i)) u i (tracialVector B N G).vacuum)
        (wordEval (heatTuple X (fun i => semicircularN (σ i)) u) w (tracialVector B N G).vacuum) -
        ((v i + u : ℝ) : ℂ) * derivativeMoment (tracialVector B N G)
          (heatTuple X (fun i => semicircularN (σ i)) u) i w) := by
  have he := cumulant_residual_hasSum (tracialVector B N G)
    (heatTuple X (fun i => semicircularN (σ i)) u)
    (heatTuple_selfAdjoint X _ hsa (fun i => semicircularN_selfAdjoint _) u)
    (fun i => v i + u) i w
  rw [heat_cumulants J X hX σ hσ hs u hu] at he
  simp only [residual_heat] at he
  exact he
end FreeTensor
end FiniteEntropySeparation

end

end OAI
