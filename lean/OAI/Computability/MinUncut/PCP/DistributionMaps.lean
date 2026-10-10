import Mathlib
import OAI.Computability.MinUncut.PCP.SelectedMarginal
import OAI.Computability.MinUncut.Games.KernelSampling

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem pushforward_mixture (μ : FiniteDistribution A) (ν : A → FiniteDistribution B)
    (f : B → C) :
    (μ.mixture ν).pushforward f = μ.mixture (fun a => (ν a).pushforward f) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward, probability_mixture]

end
end MinUncutGames.Foundations.Games.FiniteDistribution

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem isProbability_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (hp : IsProbability p) :
    IsProbability (fun a => p (e a)) := by
  constructor
  · intro a
    exact hp.1 _
  · rw [e.sum_comp]
    exact hp.2

theorem partialRevealMarginal_isProbability
    {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ)
    (hp : IsProbability (fullRevealMarginal μ j likelihood)) :
    IsProbability (partialRevealMarginal μ j likelihood) := by
  apply (maskedJoint_isProbability_iff _).mp
  have h := isProbability_comp_equiv (revealSplitEquiv (T := T) j).symm _ hp
  have he : (fun z => fullRevealMarginal μ j likelihood
      ((revealSplitEquiv (T := T) j).symm z)) =
      maskedJoint (partialRevealMarginal μ j likelihood) := by
    funext z
    exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
  rw [he] at h
  exact h

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

abbrev SelectedCommonData (selected : Finset (Fin n))
    (j : {i : Fin n // i ∉ selected}) :=
  ((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
    ({i : {i : Fin n // i ∉ selected} // i ≠ j} → Q₁ ⊕ Q₂)

theorem selected_fullReveal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) := by
  have h := isProbability_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm
    _ (selectedRawMarginal_isProbability G strategy selected positive j)
  have he : (fun z => selectedRawMarginal G strategy selected j
      ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z)) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) := by
    funext z
    exact selectedRawMarginal_fullReveal G strategy selected j z
  rw [he] at h
  exact h

def selectedCommonLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j × (Q₁ × Q₂)) :=
  toGameLaw (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
    (partialRevealMarginal_isProbability G.questions j _
      (selected_fullReveal_isProbability G strategy selected positive j))

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem firstMarginal_totalVariation_le (r t : X × Y → ℝ) :
    totalVariation (firstMarginal r) (firstMarginal t) ≤ totalVariation r t := by
  unfold totalVariation firstMarginal
  simp_rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => Finset.abs_sum_le_sum_abs (fun y : Y => r (x,y)-t (x,y)) Finset.univ)
  rw [Fintype.sum_prod_type]
  linarith

def leftCommonMarginal (p : S × (X × Y) → ℝ) : X × S → ℝ :=
  fun z => ∑ y, p (z.2,(z.1,y))

def leftCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : X → S → ℝ :=
  conditionalKernel (leftCommonMarginal p) fallback

def swapSeedLeft : (X × (S × Y)) ≃ (S × (X × Y)) where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

theorem leftCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (x : X) :
    IsProbability (leftCommonProfile p fallback x) :=
  conditionalKernel_isProbability _ _ (leftCommonMarginal_isProbability p hp) hf x

theorem leftCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1) ≤
      totalVariation p (leftRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapSeedLeft (S := S) (X := X) (Y := Y)
  let p' : X × (S × Y) → ℝ := fun z => p (e z)
  have h := ProfileCorrection.left_profile_correction p' μ.weight fallback
    (μ.pushforward Prod.snd).weight
    (isProbability_comp_equiv e p hp) (gameLaw_isProbability μ) hf
    (gameLaw_isProbability (μ.pushforward Prod.snd))
  have hs : ProfileCorrection.seedQuestionMarginal p' = leftCommonMarginal p := rfl
  have hc : (fun z : X × (S × Y) => ProfileCorrection.seedQuestionMarginal p' (z.1,z.2.1) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2) =
      fun z => leftRevealModel μ p (e z) := by
    funext z
    change (∑ y, p (z.2.1,(z.1,y))) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2 =
      (∑ y, p (z.2.1,(z.1,y))) *
        (revealProfile μ (Sum.inl z.1)).weight (z.1,z.2.2)
    rw [revealProfile_inl_diagonal]
  have hd : (fun z : X × (S × Y) => μ.weight (z.1,z.2.2) *
      conditionalKernel (ProfileCorrection.seedQuestionMarginal p') fallback z.1 z.2.1) =
      fun z => μ.weight (e z).2 * leftCommonProfile p fallback (e z).2.1 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (leftRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1)] at h
  have hm : firstMarginal p' = firstMarginal (secondMarginal p) := by
    funext x
    simp only [firstMarginal, secondMarginal, Fintype.sum_prod_type, p', e, swapSeedLeft]
    exact Finset.sum_comm
  rw [hm] at h
  exact h.trans (add_le_add le_rfl (firstMarginal_totalVariation_le (secondMarginal p) μ.weight))

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

theorem rightCommonProfile_isProbability (p : S × (X × Y) → ℝ) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (y : Y) :
    IsProbability (rightCommonProfile p fallback y) :=
  leftCommonProfile_isProbability (fun z => p (swapQuestionEndpoints z)) fallback
    (isProbability_comp_equiv swapQuestionEndpoints p hp) hf y

theorem swap_question_pushforward_snd (μ : FiniteDistribution (X × Y)) :
    ((μ.transport (Equiv.prodComm X Y)).pushforward Prod.snd) = μ.pushforward Prod.fst := by
  rw [FiniteDistribution.transport_eq_pushforward, FiniteDistribution.pushforward_comp]
  rfl

omit [Fintype S] in
theorem leftRevealModel_swap [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (z : S × (Y × X)) :
    leftRevealModel (μ.transport (Equiv.prodComm X Y))
      (fun z => p (swapQuestionEndpoints z)) z = rightRevealModel μ p (swapQuestionEndpoints z) := by
  rcases z with ⟨s,y,x⟩
  change (∑ x', p (s,(x',y))) *
      (revealProfile (μ.transport (Equiv.prodComm X Y)) (Sum.inl y)).weight (y,x) =
    (∑ x', p (s,(x',y))) * (revealProfile μ (Sum.inr y)).weight (x,y)
  rw [revealProfile_inl_diagonal, revealProfile_inr_diagonal, swap_question_pushforward_snd]

theorem rightCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1) ≤
      totalVariation p (rightRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapQuestionEndpoints (S := S) (X := X) (Y := Y)
  let p' : S × (Y × X) → ℝ := fun z => p (e z)
  let μ' := μ.transport (Equiv.prodComm X Y)
  have h := leftCommonProfile_error p' μ' fallback (isProbability_comp_equiv e p hp) hf
  have hc : leftRevealModel μ' p' = fun z => rightRevealModel μ p (e z) := by
    funext z
    exact leftRevealModel_swap p μ z
  have hd : (fun z : S × (Y × X) => μ'.weight z.2 * leftCommonProfile p' fallback z.2.1 z.1) =
      fun z => μ.weight (e z).2 * rightCommonProfile p fallback (e z).2.2 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (rightRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1)] at h
  have hm : totalVariation (secondMarginal p') μ'.weight =
      totalVariation (secondMarginal p) μ.weight := by
    change totalVariation (fun yx => secondMarginal p ((Equiv.prodComm Y X) yx))
      (fun yx => μ.weight ((Equiv.prodComm Y X) yx)) = _
    exact totalVariation_comp_equiv (Equiv.prodComm Y X) _ _
  rw [hm] at h
  exact h

end
end MinUncutGames.Foundations.Repetition

end OAI
