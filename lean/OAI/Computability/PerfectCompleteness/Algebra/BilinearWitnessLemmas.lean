import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Pi
import OAI.Computability.PerfectCompleteness.Decoding.CollisionAveragingLemmas
import OAI.Computability.PerfectCompleteness.Sampling.DensityVariation

namespace OAI


namespace PerfectCompleteness.BilinearWitness

open scoped BigOperators

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

def assemble (f : (i : I) → V i →ₗ[𝕜] H) (x : (i : I) → V i) : H :=
  ∑ i, f i (x i)

omit [DecidableEq I] in
theorem exists_child_pair (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜)
    (nonzero : B ≠ 0) : ∃ i j, ∃ (x : V i) (y : V j), B (f i x) (f j y) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply nonzero
  ext u v
  obtain ⟨x, rfl⟩ := spans u
  obtain ⟨y, rfl⟩ := spans v
  simp only [assemble, map_sum, LinearMap.sum_apply]
  simp only [h, Finset.sum_const_zero, LinearMap.zero_apply]

def Witness (f : (i : I) → V i →ₗ[𝕜] H) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜) :=
  { w : (Σ i : I, Σ j : I, V i × V j) // B (f w.1 w.2.2.1) (f w.2.1 w.2.2.2) ≠ 0 }

def chooseWitness (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜)
    (nonzero : B ≠ 0) : Witness f B := by
  classical
  apply Classical.choice
  obtain ⟨i, j, x, y, h⟩ := exists_child_pair f spans B nonzero
  exact ⟨⟨⟨i, j, x, y⟩, h⟩⟩

def selected (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜) : Finset I := by
  classical
  exact if h : B = 0 then ∅ else
    { (chooseWitness f spans B h).val.1, (chooseWitness f spans B h).val.2.1 }

theorem selected_card_le (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜) :
    (selected f spans B).card ≤ 2 := by
  classical
  unfold selected
  split
  · simp
  · exact (Finset.card_insert_le _ _).trans (by simp)

theorem marked_of_restriction_zero (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜)
    (nonzero : B ≠ 0) (mask : I → Bool) (U : Submodule 𝕜 H)
    (unchanged : ∀ i, mask i = false → ∀ x, f i x ∈ U)
    (vanishes : ∀ x ∈ U, ∀ y ∈ U, B x y = 0) :
    ∃ i ∈ selected f spans B, mask i = true := by
  classical
  let w := chooseWitness f spans B nonzero
  have hselect : selected f spans B = {w.val.1, w.val.2.1} := by
    simp only [selected, dite_eq_right nonzero, w]
  rw [hselect]
  by_cases hi : mask w.val.1 = true
  · exact ⟨w.val.1, by simp, hi⟩
  by_cases hj : mask w.val.2.1 = true
  · exact ⟨w.val.2.1, by simp, hj⟩
  have hif : mask w.val.1 = false := Bool.eq_false_of_not_eq_true hi
  have hjf : mask w.val.2.1 = false := Bool.eq_false_of_not_eq_true hj
  exact False.elim (w.property (vanishes _ (unchanged _ hif _) _ (unchanged _ hjf _)))

end
end PerfectCompleteness.BilinearWitness


namespace PerfectCompleteness.BilinearProjection

open scoped BigOperators
open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness ProjectionPosterior AdaptiveProjection BilinearWitness

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem disagreement_probability (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → (H →ₗ[𝕜] H →ₗ[𝕜] 𝕜))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L) :
    (forward P q nonnegative mean β hβ hβ').probability
      (fun z => decide (F₀ z.2 ≠ F₁ z.2 ∧
        ∀ v ∈ U z.2 z.1, ∀ w ∈ U z.2 z.1, F₀ z.2 v w = F₁ z.2 v w)) ≤
      2 * (β * L / (1 - β)) := by
  classical
  let select := fun x => selected f spans (F₀ x - F₁ x)
  have inclusion : ∀ z : (I → Bool) × ((i : I) → Ω i),
      decide (F₀ z.2 ≠ F₁ z.2 ∧
        ∀ v ∈ U z.2 z.1, ∀ w ∈ U z.2 z.1, F₀ z.2 v w = F₁ z.2 v w) = true →
      decide (∃ i ∈ select z.2, z.1 i = true) = true := by
    intro z hz
    have h := of_decide_eq_true hz
    apply decide_eq_true
    apply marked_of_restriction_zero f spans (F₀ z.2 - F₁ z.2)
      (sub_ne_zero.mpr h.1) z.1 (U z.2 z.1) (unchanged z.2 z.1)
    intro v hv w hw
    simpa only [LinearMap.sub_apply, sub_eq_zero] using h.2 v hv w hw
  exact ((forward P q nonnegative mean β hβ hβ').probability_mono inclusion).trans
    (by simpa only [Nat.cast_ofNat] using
      (adaptive_selection P q nonnegative mean β hβ hβ' L hL bound select 2
        (fun x => selected_card_le f spans (F₀ x - F₁ x))))

end
end PerfectCompleteness.BilinearProjection


namespace PerfectCompleteness.BilinearCollisionTransfer

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness ProjectionPosterior BilinearWitness

noncomputable section

theorem probability_le_add_of_imp {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (p q r : X → Bool)
    (h : ∀ x, p x = true → q x = true ∨ r x = true) :
    μ.probability p ≤ μ.probability q + μ.probability r := by
  simp only [FiniteDistribution.probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  cases hp : p x <;> cases hq : q x <;> cases hr : r x <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, zero_add, add_zero]
  all_goals first | exact μ.nonnegative x | linarith [μ.nonnegative x] |
    exact False.elim (by simpa [hq, hr] using h x hp)

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

abbrev Form := H →ₗ[𝕜] H →ₗ[𝕜] 𝕜

def fullCollision (a b : Option (Form (𝕜 := 𝕜) (H := H))) : Bool :=
  decide (∃ F, a = some F ∧ b = some F)

def restrictedCollision (a b : Option (Form (𝕜 := 𝕜) (H := H)))
    (U : Submodule 𝕜 H) : Bool :=
  decide (∃ F G, a = some F ∧ b = some G ∧
    ∀ v ∈ U, ∀ w ∈ U, F v w = G v w)

theorem collision_split (a b : Option (Form (𝕜 := 𝕜) (H := H)))
    (U : Submodule 𝕜 H) (h : restrictedCollision a b U = true) :
    fullCollision a b = true ∨
      decide (a.getD 0 ≠ b.getD 0 ∧
        ∀ v ∈ U, ∀ w ∈ U, a.getD 0 v w = b.getD 0 v w) = true := by
  obtain ⟨F, G, ha, hb, heq⟩ := of_decide_eq_true h
  subst a b
  by_cases hFG : F = G
  · left
    apply decide_eq_true
    exact ⟨F, rfl, congrArg some hFG.symm⟩
  · right
    simpa only [Option.getD_some, decide_eq_true_eq] using And.intro hFG heq

theorem restricted_le_full_add (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → Option (Form (𝕜 := 𝕜) (H := H)))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L) :
    (forward P q nonnegative mean β hβ hβ').probability
        (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1)) ≤
      ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd).probability
        (fun x => fullCollision (F₀ x) (F₁ x)) + 2 * (β * L / (1 - β)) := by
  have hsplit := probability_le_add_of_imp (forward P q nonnegative mean β hβ hβ')
    (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1))
    (fun z => fullCollision (F₀ z.2) (F₁ z.2))
    (fun z => decide ((F₀ z.2).getD 0 ≠ (F₁ z.2).getD 0 ∧
      ∀ v ∈ U z.2 z.1, ∀ w ∈ U z.2 z.1,
        (F₀ z.2).getD 0 v w = (F₁ z.2).getD 0 v w))
    (fun z => collision_split (F₀ z.2) (F₁ z.2) (U z.2 z.1))
  have hbad := BilinearProjection.disagreement_probability f spans
    (fun x => (F₀ x).getD 0) (fun x => (F₁ x).getD 0) U unchanged
    P q nonnegative mean β hβ hβ' L hL bound
  rw [FiniteDistribution.probability_pushforward]
  exact hsplit.trans (add_le_add (le_refl _) hbad)

theorem full_collision_transfer (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → Option (Form (𝕜 := 𝕜) (H := H)))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L)
    (ν : FiniteDistribution ((i : I) → Ω i)) :
    (forward P q nonnegative mean β hβ hβ').probability
        (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1)) -
      2 * (β * L / (1 - β)) -
      ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd).totalVariation ν ≤
      ν.probability (fun x => fullCollision (F₀ x) (F₁ x)) := by
  have h := restricted_le_full_add f spans F₀ F₁ U unchanged
    P q nonnegative mean β hβ hβ' L hL bound
  have htv := FiniteDistribution.probability_le_add_totalVariation
    ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd) ν
    (fun x => fullCollision (F₀ x) (F₁ x))
  linarith

end
end PerfectCompleteness.BilinearCollisionTransfer

end OAI
