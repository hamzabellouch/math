import OAI.LinearAlgebra.MatrixMultiplication.Tensor.LeafVolumes
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMasks

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.ExactStatisticWords

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A U : Type*} [Fintype A] [DecidableEq A]

abbrev Words (statistic : U → A) (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → U //
    ∀ a, wordPopulation (statistic ∘ w) a = counts a}

def statisticWord (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) : ExactWords counts :=
  ⟨statistic ∘ w.val, w.property⟩

theorem empiricalLaw_eq (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) :
    InheritedMasks.empiricalLaw (statistic ∘ w.val) =
      fun a => (counts a : ℝ) / (∑ a, counts a : ℕ) := by
  funext a
  simp only [InheritedMasks.empiricalLaw, w.property, Fintype.card_fin]

theorem typeWindow_of_counts (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) (ν : A → ℝ) (η : ℝ)
    (happrox : ∀ a, |(counts a : ℝ) / (∑ a, counts a : ℕ) - ν a| ≤ η) :
    InheritedMasks.typeWindow ν η (statistic ∘ w.val) := by
  intro a
  rw [empiricalLaw_eq]
  exact happrox a

theorem sum_statistic_weight (statistic : U → A) (counts q : A → ℕ)
    (w : Words statistic counts) :
    (∑ i, q (statistic (w.val i))) = ∑ a, counts a * q a := by
  let e := Equiv.sigmaFiberEquiv (statistic ∘ w.val)
  calc
    (∑ i, q (statistic (w.val i))) =
        ∑ p : (Σ a, {i // (statistic ∘ w.val) i = a}), q p.1 := by
      rw [← Equiv.sum_comp e (fun i => q (statistic (w.val i)))]
      apply Finset.sum_congr rfl
      intro p _
      exact congrArg q p.2.property
    _ = ∑ a, counts a * q a := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      change wordPopulation (statistic ∘ w.val) a * q a = counts a * q a
      rw [w.property]

def fiberEquiv (statistic : U → A) (counts : A → ℕ) (w : ExactWords counts) :
    {v : Words statistic counts // statisticWord statistic counts v = w} ≃
      {v : Fin (∑ a, counts a) → U // ∀ i, statistic (v i) = w.val i} where
  toFun v := ⟨v.val.val, fun i => congrFun (congrArg Subtype.val v.property) i⟩
  invFun v := by
    have heq : statistic ∘ v.val = w.val := funext v.property
    let v' : Words statistic counts := ⟨v.val, fun a => by
      rw [heq]
      exact w.property a⟩
    exact ⟨v', Subtype.ext heq⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    rfl

variable [Fintype U]

theorem card (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, Fintype.card {u : U // statistic u = a} = b a) :
    Fintype.card (Words statistic counts) =
      Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
  classical
  have hfiber (w : ExactWords counts) :
      Fintype.card {v : Words statistic counts // statisticWord statistic counts v = w} =
        ∏ a, b a ^ counts a := by
    let e : {v : Fin (∑ a, counts a) → U // ∀ i, statistic (v i) = w.val i} ≃
        (∀ i : Fin (∑ a, counts a), {u : U // statistic u = w.val i}) :=
      { toFun := fun v i => ⟨v.val i, v.property i⟩
        invFun := fun v => ⟨fun i => (v i).val, fun i => (v i).property⟩
        left_inv := by intro v; rfl
        right_inv := by intro v; rfl }
    rw [Fintype.card_congr (fiberEquiv statistic counts w),
      Fintype.card_congr e, Fintype.card_pi]
    simp only [hb]
    have h := LeafVolumes.labelings_card w.val b
    simpa only [Fintype.card_pi, Fintype.card_fin, w.property] using h
  calc
    Fintype.card (Words statistic counts) =
        Fintype.card (Σ w : ExactWords counts,
          {v : Words statistic counts // statisticWord statistic counts v = w}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (statisticWord statistic counts))).symm
    _ = Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
      simp only [Fintype.card_sigma, hfiber, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, exactWords_card]

theorem card_of_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a) :
    Fintype.card (Words statistic counts) =
      Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
  rw [card statistic counts (fun a => Fintype.card {u : U // statistic u = a})
    (fun _ => rfl)]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : counts a = 0
  · simp [ha]
  · rw [hb a (Nat.pos_of_ne_zero ha)]

omit [Fintype A] in
theorem card_fixedWeight_fiber (statistic : U → A) (weight : U → ℕ)
    (statisticWeight : A → ℕ) (hweight : ∀ u, weight u = statisticWeight (statistic u))
    (a : ℕ) (s : A) (hs : statisticWeight s = a) :
    Fintype.card {u : {u : U // weight u = a} // statistic u.val = s} =
      Fintype.card {u : U // statistic u = s} := by
  apply Fintype.card_congr
  exact
    { toFun := fun u => ⟨u.val.val, u.property⟩
      invFun := fun u => ⟨⟨u.val, by rw [hweight, u.property, hs]⟩, u.property⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }

theorem card_pos_of_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hpos : ∀ a, 0 < counts a → 0 < b a) :
    0 < Fintype.card (Words statistic counts) := by
  rw [card_of_supported statistic counts b hb]
  apply Nat.mul_pos (Nat.multinomial_pos Finset.univ counts)
  apply Finset.prod_pos
  intro a _
  by_cases ha : counts a = 0
  · simp [ha]
  · exact pow_pos (hpos a (Nat.pos_of_ne_zero ha)) _

end MatrixMultiplication.ExactStatisticWords

end

end OAI
