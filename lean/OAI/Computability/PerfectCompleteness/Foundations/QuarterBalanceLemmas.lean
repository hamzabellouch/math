import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.QuarterBalance

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias

noncomputable section

abbrev F2 := ZMod 2

def sign (b : F2) : ℝ := if b = 0 then 1 else -1

theorem scalar_cases : ∀ b : F2, b = 0 ∨ b = 1 := by decide

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]
@[simp] theorem abs_sign (b : F2) : |sign b| = 1 := by unfold sign; split <;> norm_num

theorem sign_add (a b : F2) : sign (a + b) = sign a * sign b := by
  have htwo : (1 : F2) + 1 = 0 := by decide
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl <;> simp [htwo]

theorem sign_sum {J : Type*} (s : Finset J) (f : J → F2) :
    sign (∑ j ∈ s, f j) = ∏ j ∈ s, sign (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sum_insert, Finset.prod_insert, hj, sign_add, ih]

variable {Ω : Type*} [Fintype Ω]

theorem bit_probabilities (μ : FiniteDistribution Ω) (f : Ω → F2) :
    μ.probability (fun x => decide (f x = 0)) +
      μ.probability (fun x => decide (f x = 1)) = 1 := by
  rw [← μ.normalized]
  simp only [FiniteDistribution.probability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hb : f x = 0 ∨ f x = 1 := scalar_cases (f x)
  rcases hb with h | h <;> simp [h]

theorem expectation_sign (μ : FiniteDistribution Ω) (f : Ω → F2) :
    μ.expectation (fun x => sign (f x)) =
      2 * μ.probability (fun x => decide (f x = 0)) - 1 := by
  rw [← μ.normalized]
  simp only [FiniteDistribution.expectation, FiniteDistribution.probability,
    Finset.mul_sum, ← Finset.sum_sub_distrib, sign]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = 0 <;> simp [h]
  ring

theorem bias_of_balanced_bits (μ : FiniteDistribution Ω) (f : Ω → F2)
    (c : ℝ) (lower : ∀ b : F2, c ≤ μ.probability (fun x => decide (f x = b))) :
    |μ.expectation (fun x => sign (f x))| ≤ 1 - 2 * c := by
  rw [expectation_sign]
  have h0 := lower 0
  have h1 := lower 1
  have ht := bit_probabilities μ f
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {V W : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup W] [Module F2 W] [Fintype W]

def Balanced (μ : FiniteDistribution V) : Prop :=
  ∀ (f : V →ₗ[F2] F2), f ≠ 0 → ∀ b : F2,
    (1 / 4 : ℝ) ≤ μ.probability (fun x => decide (f x = b))

theorem balanced_of_bias_le_half (μ : FiniteDistribution V)
    (bias : ∀ f : V →ₗ[F2] F2, f ≠ 0 →
      |μ.expectation (fun x => sign (f x))| ≤ (1 / 2 : ℝ)) : Balanced μ := by
  intro f hf b
  have h := abs_le.mp (bias f hf)
  rw [expectation_sign] at h
  have ht := bit_probabilities μ f
  rcases scalar_cases b with rfl | rfl <;> linarith

theorem bilinear_bit_lower (μ : FiniteDistribution V) (ν : FiniteDistribution W)
    (hμ : Balanced μ) (hν : Balanced ν)
    (B : V →ₗ[F2] W →ₗ[F2] F2) (nonzero : B ≠ 0) (b : F2) :
    (1 / 16 : ℝ) ≤ (μ.product ν).probability (fun z => decide (B z.1 z.2 = b)) := by
  classical
  have hw : ∃ w : W, (B.flip w) ≠ 0 := by
    by_contra h
    push Not at h
    apply nonzero
    ext v w
    have he := congrArg (fun f : V →ₗ[F2] F2 => f v) (h w)
    simpa using he
  obtain ⟨w, hw⟩ := hw
  have lower (v : V) :
      (if B.flip w v = 1 then (1 / 4 : ℝ) else 0) ≤
        ν.probability (fun x => decide (B v x = b)) := by
    by_cases h : B.flip w v = 1
    · rw [ite_eq_left h]
      apply hν (B v)
      intro hz
      have he := congrArg (fun f : W →ₗ[F2] F2 => f w) hz
      have hh : B v w = 1 := h
      simp only [LinearMap.zero_apply] at he
      exact zero_ne_one (he.symm.trans hh)
    · rw [ite_eq_right h]
      exact ν.probability_nonnegative _
  have hfirst := hμ (B.flip w) hw 1
  calc
    (1 / 16 : ℝ) ≤ (1 / 4 : ℝ) * μ.probability (fun v => decide (B.flip w v = 1)) := by
      nlinarith
    _ = ∑ v, μ.weight v * (if B.flip w v = 1 then (1 / 4 : ℝ) else 0) := by
      simp only [FiniteDistribution.probability, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : B v w = 1 <;> simp [h, LinearMap.flip_apply]
      ring
    _ ≤ ∑ v, μ.weight v * ν.probability (fun x => decide (B v x = b)) :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (lower v) (μ.nonnegative v)
    _ = _ := by
      simp only [FiniteDistribution.probability, FiniteDistribution.product,
        Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : B v x = b <;> simp [h]

theorem bilinear_bias (μ : FiniteDistribution V) (ν : FiniteDistribution W)
    (hμ : Balanced μ) (hν : Balanced ν)
    (B : V →ₗ[F2] W →ₗ[F2] F2) (nonzero : B ≠ 0) :
    |(μ.product ν).expectation (fun z => sign (B z.1 z.2))| ≤ (7 / 8 : ℝ) := by
  have h := bias_of_balanced_bits (μ.product ν) (fun z => B z.1 z.2) (1 / 16)
    (bilinear_bit_lower μ ν hμ hν B nonzero)
  norm_num at h ⊢
  exact h

end
end PerfectCompleteness.QuarterBalance



namespace PerfectCompleteness.SelectedSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem expectation_product_selected (P : (i : I) → FiniteDistribution (Ω i))
    (selected : I → Prop) [DecidablePred selected]
    (f : (i : Subtype selected) → Ω i → ℝ) :
    (law P).expectation (fun x => ∏ i : Subtype selected, f i (x i)) =
      ∏ i : Subtype selected, (P i).expectation (f i) := by
  let g : (i : I) → Ω i → ℝ := fun i a =>
    if h : selected i then f ⟨i, h⟩ a else 1
  have hprod (x : (i : I) → Ω i) :
      (∏ i, g i (x i)) = ∏ i : Subtype selected, f i (x i) := by
    simp only [g, Fintype.prod_dite, Finset.prod_const_one, mul_one]
  have hexp (i : I) : (P i).expectation (g i) =
      if h : selected i then (P i).expectation (f ⟨i, h⟩) else 1 := by
    by_cases hi : selected i <;> simp [g, hi, SmallBias.expectation_const]
  calc
    _ = (law P).expectation (fun x => ∏ i, g i (x i)) :=
      FiniteDistribution.expectation_congr _ (fun x => (hprod x).symm)
    _ = ∏ i, (P i).expectation (g i) := expectation_product P g
    _ = ∏ i, if h : selected i then (P i).expectation (f ⟨i, h⟩) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact hexp i
    _ = _ := by simp only [Fintype.prod_dite, Finset.prod_const_one, mul_one]

theorem pushforward_law_selected (P : (i : I) → FiniteDistribution (Ω i))
    (selected : I → Prop) [DecidablePred selected]
    {Γ : Subtype selected → Type*} [∀ i, Fintype (Γ i)]
    (source : (i : Subtype selected) → Ω i → Γ i) :
    (law P).pushforward (fun x (i : Subtype selected) => source i (x i)) =
      law (fun i : Subtype selected => (P i).pushforward (source i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  calc
    _ = (law P).expectation
        (fun x => if (fun i : Subtype selected => source i (x i)) = y then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : (fun i : Subtype selected => source i (x i)) = y <;> simp [h]
    _ = (law P).expectation
        (fun x => ∏ i : Subtype selected, if source i (x i) = y i then 1 else 0) := by
      apply FiniteDistribution.expectation_congr
      intro x
      simp only [Fintype.prod_boole, funext_iff]
    _ = ∏ i : Subtype selected, (P i).expectation
        (fun a => if source i a = y i then 1 else 0) :=
      expectation_product_selected (I := I) (Ω := Ω) P selected
        (fun (i : Subtype selected) (a : Ω i) => if source i a = y i then (1 : ℝ) else 0)
    _ = _ := by
      simp [law, FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]

theorem selected_sources_conditioned (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool)
    (positive : 0 < (law P).probability (allEvent event))
    (selected : I → Prop) [DecidablePred selected]
    {Γ : Subtype selected → Type*} [∀ i, Fintype (Γ i)]
    (source : (i : Subtype selected) → Ω i → Γ i)
    (μ : (i : Subtype selected) → FiniteDistribution (Γ i))
    (row : ∀ i : Subtype selected,
      ((P i).condition (event i) (coordinate_probability_positive P event positive i)).pushforward
        (source i) = μ i) :
    ((law P).condition (allEvent event) positive).pushforward
      (fun x (i : Subtype selected) => source i (x i)) = law μ := by
  rw [condition_law_all, pushforward_law_selected]
  congr 1
  funext i
  exact row i

end Product

section Records

variable {E R T : Type*}

def childObservation (clean : E → R → T → Bool) (x : E × (R × T)) :
    Sum (E × (R × T)) R :=
  if clean x.1 x.2.1 x.2.2 then Sum.inr x.2.1 else Sum.inl x

theorem clean_observation_event [DecidableEq E] [DecidableEq R] [DecidableEq T]
    (clean : E → R → T → Bool) (record : R) :
    (fun x => decide (childObservation clean x = Sum.inr record)) =
      (fun x => decide (x.2.1 = record) && clean x.1 x.2.1 x.2.2) := by
  funext x
  cases h : clean x.1 x.2.1 x.2.2 <;> simp [childObservation, h]

end Records


variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R T : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (T i)]

theorem clean_record_sources
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (kernel : (i : I) → E i → R i → FiniteDistribution (T i))
    (clean : (i : I) → E i → R i → T i → Bool)
    (p : I → ℝ)
    (constant : ∀ i e r, (kernel i e r).probability (clean i e r) = p i)
    (record : (i : I) → Sum (E i × (R i × T i)) (R i))
    (positive : 0 <
      (law (fun i => kernelJoint (μ i) (fun e => kernelJoint (ν i) (kernel i e)))).probability
        (allEvent (fun i x => decide (childObservation (clean i) x = record i)))) :
    ((law (fun i => kernelJoint (μ i) (fun e => kernelJoint (ν i) (kernel i e)))).condition
      (allEvent (fun i x => decide (childObservation (clean i) x = record i)))
        positive).pushforward
          (fun x (i : {i : I // ∃ r, record i = Sum.inr r}) => (x i).1) =
      law (fun i : {i : I // ∃ r, record i = Sum.inr r} => μ i) := by
  classical
  let P := fun i => kernelJoint (μ i) (fun e => kernelJoint (ν i) (kernel i e))
  let event := fun i x => decide (childObservation (clean i) x = record i)
  apply selected_sources_conditioned P event positive
    (fun i => ∃ r, record i = Sum.inr r) (fun _ x => x.1) (fun i => μ i)
  intro i
  obtain ⟨r, hr⟩ := i.property
  have hevent : event i =
      (fun x => decide (x.2.1 = r) && clean i x.1 x.2.1 x.2.2) := by
    dsimp [event]
    rw [hr]
    exact clean_observation_event (clean i) r
  have hpositive := coordinate_probability_positive P event positive i
  have hp : 0 < (P i).probability
      (fun x => decide (x.2.1 = r) && clean i x.1 x.2.1 x.2.2) := by
    rwa [hevent] at hpositive
  simpa only [hevent] using
    designated_source_condition (μ i) (ν i) (kernel i) (clean i) (p i) (constant i) r hp


end
end PerfectCompleteness.SelectedSources



namespace PerfectCompleteness.SourceCoordinateSplit

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem coordinate_split (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (law P).transport (Equiv.piSplitAt i Ω) =
      (P i).product (law (fun j : {j : I // j ≠ i} => P j)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ j, (P j).weight ((Equiv.piSplitAt i Ω).symm y j)) =
    (P i).weight y.1 * ∏ j : {j : I // j ≠ i}, (P j).weight (y.2 j)
  calc
    _ = ∏ j, if h : j = i then (P i).weight y.1 else (P j).weight (y.2 ⟨j, h⟩) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt, hj]
    _ = _ := by
      rw [Fintype.prod_dite]
      simp

theorem coordinate_split_pushforward (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) :
    (law P).pushforward (fun x => (x i, fun j : {j : I // j ≠ i} => x j)) =
      (P i).product (law (fun j : {j : I // j ≠ i} => P j)) := by
  change (law P).pushforward (Equiv.piSplitAt i Ω) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact coordinate_split P i

theorem iid_coordinate_split {E : Type*} [Fintype E] {n : Nat}
    (μ : FiniteDistribution E) (i : Fin n) :
    (μ.iid n).pushforward (fun x => (x i, fun j : {j : Fin n // j ≠ i} => x j)) =
      μ.product (FiniteDistribution.table (fun _ : {j : Fin n // j ≠ i} => μ)) := by
  change (law (fun _ : Fin n => μ)).pushforward
      (fun x => (x i, fun j : {j : Fin n // j ≠ i} => x j)) =
    μ.product (law (fun _ : {j : Fin n // j ≠ i} => μ))
  exact coordinate_split_pushforward (fun _ : Fin n => μ) i

end
end PerfectCompleteness.SourceCoordinateSplit



namespace PerfectCompleteness.FiniteProductSplit

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

abbrev Others (i : I) := (j : {j : I // j ≠ i}) → Ω j.val

def others (i : I) (x : (j : I) → Ω j) : Others (Ω := Ω) i := fun j => x j.val

def otherLaw (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    FiniteDistribution (Others (Ω := Ω) i) :=
  FiniteProduct.law (fun j : {j : I // j ≠ i} => P j.val)

theorem split_law (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (FiniteProduct.law P).pushforward (Equiv.piSplitAt i Ω) =
      (P i).product (otherLaw P i) :=
  SourceCoordinateSplit.coordinate_split_pushforward P i

theorem expectation_split (P : (i : I) → FiniteDistribution (Ω i)) (i : I)
    (f : Ω i → Others (Ω := Ω) i → ℝ) :
    (FiniteProduct.law P).expectation (fun x => f (x i) (others i x)) =
      (P i).expectation (fun a => (otherLaw P i).expectation (fun b => f a b)) := by
  have h := congrArg (fun μ : FiniteDistribution (Ω i × Others (Ω := Ω) i) =>
    μ.expectation (fun z => f z.1 z.2)) (split_law P i)
  rw [FiniteDistribution.expectation_pushforward, FiniteDistribution.expectation_product] at h
  exact h

theorem expectation_background_first (P : (i : I) → FiniteDistribution (Ω i)) (i : I)
    (f : Ω i → Others (Ω := Ω) i → ℝ) :
    (FiniteProduct.law P).expectation (fun x => f (x i) (others i x)) =
      (otherLaw P i).expectation (fun b => (P i).expectation (fun a => f a b)) := by
  rw [expectation_split]
  exact FiniteDistribution.expectation_comm (P i) (otherLaw P i) f

theorem resampling_expectation (P : (i : I) → FiniteDistribution (Ω i)) (i : I)
    (f : Others (Ω := Ω) i → Ω i → Ω i → ℝ) :
    ((FiniteProduct.law P).product (P i)).expectation
        (fun z => f (others i z.1) (z.1 i) z.2) =
      (otherLaw P i).expectation
        (fun b => ((P i).product (P i)).expectation (fun z => f b z.1 z.2)) := by
  rw [FiniteDistribution.expectation_product]
  rw [expectation_background_first P i
    (fun a b => (P i).expectation (fun a' => f b a a'))]
  apply FiniteDistribution.expectation_congr
  intro b
  exact (FiniteDistribution.expectation_product (P i) (P i) (fun z => f b z.1 z.2)).symm

end
end PerfectCompleteness.FiniteProductSplit

end OAI
