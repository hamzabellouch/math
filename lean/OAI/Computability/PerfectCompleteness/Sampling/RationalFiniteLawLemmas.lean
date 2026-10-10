import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.RationalFiniteLaw

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

structure RationalLaw {E : Type*} [Fintype E] (μ : FiniteDistribution E) where
  weights : E → ℚ
  positive : ∀ e, 0 < weights e
  total : ∑ e, weights e = 1
  cast_weight : ∀ e, μ.weight e = (weights e : ℝ)

def uniform (E : Type*) [Fintype E] [Nonempty E] :
    RationalLaw (FiniteDistribution.uniform E) where
  weights _ := 1 / (Fintype.card E : ℚ)
  positive _ := div_pos zero_lt_one (Nat.cast_pos.mpr Fintype.card_pos)
  total := by
    have hn : (Fintype.card E : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn
  cast_weight _ := by
    change (1 / (Fintype.card E : ℝ)) = ((1 / (Fintype.card E : ℚ) : ℚ) : ℝ)
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

def pi {I : Type*} [Fintype I] [DecidableEq I]
    {E : I → Type*} [∀ i, Fintype (E i)]
    (P : (i : I) → FiniteDistribution (E i)) (r : ∀ i, RationalLaw (P i)) :
    RationalLaw (FiniteProduct.law P) where
  weights x := ∏ i, (r i).weights (x i)
  positive x := Finset.prod_pos (fun i _ => (r i).positive (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [RationalLaw.total, Finset.prod_const_one]
  cast_weight x := by
    change (∏ i, (P i).weight (x i)) = ((∏ i, (r i).weights (x i) : ℚ) : ℝ)
    rw [Rat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => (r i).cast_weight (x i))

def product {E F : Type*} [Fintype E] [Fintype F]
    {μ : FiniteDistribution E} {ν : FiniteDistribution F}
    (r : RationalLaw μ) (s : RationalLaw ν) : RationalLaw (μ.product ν) where
  weights x := r.weights x.1 * s.weights x.2
  positive x := mul_pos (r.positive x.1) (s.positive x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, s.total, mul_one]
    exact r.total
  cast_weight x := by
    change μ.weight x.1 * ν.weight x.2 = ((r.weights x.1 * s.weights x.2 : ℚ) : ℝ)
    rw [Rat.cast_mul, r.cast_weight, s.cast_weight]

def sigma {E : Type*} {F : E → Type*} [Fintype E] [∀ e, Fintype (F e)]
    {μ : FiniteDistribution E} {ν : ∀ e, FiniteDistribution (F e)}
    (r : RationalLaw μ) (s : ∀ e, RationalLaw (ν e)) :
    RationalLaw (CompletionSoundness.sigmaLaw μ ν) where
  weights x := r.weights x.1 * (s x.1).weights x.2
  positive x := mul_pos (r.positive x.1) ((s x.1).positive x.2)
  total := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ e, r.weights e := by
        apply Finset.sum_congr rfl
        intro e _
        change (∑ f : F e, r.weights e * (s e).weights f) = r.weights e
        rw [← Finset.mul_sum, (s e).total, mul_one]
      _ = 1 := r.total
  cast_weight x := by
    change μ.weight x.1 * (ν x.1).weight x.2 =
      ((r.weights x.1 * (s x.1).weights x.2 : ℚ) : ℝ)
    rw [Rat.cast_mul, r.cast_weight, (s x.1).cast_weight]

def transport {E F : Type*} [Fintype E] [Fintype F]
    {μ : FiniteDistribution E} (r : RationalLaw μ) (e : E ≃ F) :
    RationalLaw (μ.transport e) where
  weights f := r.weights (e.symm f)
  positive f := r.positive (e.symm f)
  total := (e.symm.sum_comp r.weights).trans r.total
  cast_weight f := r.cast_weight (e.symm f)

theorem real_positive {E : Type*} [Fintype E] {μ : FiniteDistribution E}
    (r : RationalLaw μ) (e : E) : 0 < μ.weight e := by
  rw [r.cast_weight]
  exact Rat.cast_pos.mpr (r.positive e)

end
end PerfectCompleteness.RationalFiniteLaw



namespace PerfectCompleteness.RecursiveSamplerBiasProducts

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

def pairTapeEquiv (R : Nat) (V : Type*) :
    ((Fin R × Bool) → V) ≃ (Fin R → V × V) where
  toFun x h := (x (h, false), x (h, true))
  invFun y hb := if hb.2 then (y hb.1).2 else (y hb.1).1
  left_inv x := by
    funext hb
    rcases hb with ⟨h, b⟩
    cases b <;> rfl
  right_inv y := by
    funext h
    rfl

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]

theorem pairTape_law (R : Nat) (μ : FiniteDistribution V) :
    (FiniteProduct.law (fun _ : Fin R × Bool => μ)).pushforward (pairTapeEquiv R V) =
      FiniteProduct.law (fun _ : Fin R => μ.product μ) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ hb : Fin R × Bool,
      μ.weight (if hb.2 then (y hb.1).2 else (y hb.1).1)) =
    ∏ h : Fin R, μ.weight (y h).1 * μ.weight (y h).2
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  simp [mul_comm]

theorem expectation_pairs (R : Nat) (μ : FiniteDistribution V) (φ : V × V → ℝ) :
    (FiniteProduct.law (fun _ : Fin R × Bool => μ)).expectation
        (fun x => ∏ h : Fin R, φ (x (h, false), x (h, true))) =
      ((μ.product μ).expectation φ) ^ R := by
  calc
    _ = ((FiniteProduct.law (fun _ : Fin R × Bool => μ)).pushforward
        (pairTapeEquiv R V)).expectation (fun y => ∏ h : Fin R, φ (y h)) :=
      (FiniteDistribution.expectation_pushforward _ _ _).symm
    _ = (FiniteProduct.law (fun _ : Fin R => μ.product μ)).expectation
        (fun y => ∏ h : Fin R, φ (y h)) := by rw [pairTape_law]
    _ = ∏ _h : Fin R, (μ.product μ).expectation φ :=
      FiniteProduct.expectation_product _ (fun _ => φ)
    _ = _ := by simp

theorem expectation_product_mul (μ : FiniteDistribution V) (ν : FiniteDistribution W)
    (f : V → ℝ) (g : W → ℝ) :
    (μ.product ν).expectation (fun z => f z.1 * g z.2) =
      μ.expectation f * ν.expectation g := by
  change (∑ z : V × W, (μ.weight z.1 * ν.weight z.2) * (f z.1 * g z.2)) =
    (∑ v : V, μ.weight v * f v) * (∑ w : W, ν.weight w * g w)
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact mul_mul_mul_comm _ _ _ _

end
end PerfectCompleteness.RecursiveSamplerBiasProducts



noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

namespace PerfectCompleteness.FiniteProduct

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω Γ : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Γ i)]

theorem pushforward_map (P : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → Γ i) :
    (law P).pushforward (fun x i => f i (x i)) =
      law (fun i => (P i).pushforward (f i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  simp only [FiniteDistribution.pushforward, law]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

end PerfectCompleteness.FiniteProduct

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

@[simp] theorem pushforward_id {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) : μ.pushforward id = μ := by
  classical
  apply eq_of_weight_eq
  intro a
  simp [pushforward]

theorem product_pushforward_snd {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward Prod.snd = ν := by
  classical
  apply eq_of_weight_eq
  intro b
  change (∑ z : A × B,
    if z.2 = b then μ.weight z.1 * ν.weight z.2 else 0) = ν.weight b
  calc
    _ = ∑ a : A, μ.weight a * ν.weight b := by
      rw [Fintype.sum_prod_type]
      simp
    _ = (∑ a : A, μ.weight a) * ν.weight b := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [μ.normalized, one_mul]

end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
