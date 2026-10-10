import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.InheritedMaskMargins
import OAI.LinearAlgebra.MatrixFields.Tensors.TerminalRelabel

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.LeafVolumes

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F U : Type*} [CommSemiring F] [DecidableEq U]

def zeroXMatching : Tensor F Unit U U := fun _ y z => if y = z then 1 else 0
def zeroYMatching : Tensor F U Unit U := fun x _ z => if x = z then 1 else 0
def zeroZMatching : Tensor F U U Unit := fun x y _ => if x = y then 1 else 0

theorem zeroXMatching_matrixCoefficients :
    Tensor.pullback (fun _ : Unit × Unit => ())
      (fun y : Unit × U => y.2) (fun z : U × Unit => z.1)
      (zeroXMatching (F := F) (U := U)) =
    Tensor.matrixCoefficients Unit Unit U := by
  funext x y z
  simp [Tensor.pullback, zeroXMatching, Tensor.matrixCoefficients]

theorem zeroYMatching_matrixCoefficients :
    Tensor.pullback (fun x : U × Unit => x.1)
      (fun _ : Unit × Unit => ()) (fun z : Unit × U => z.2)
      (zeroYMatching (F := F) (U := U)) =
    Tensor.matrixCoefficients U Unit Unit := by
  funext x y z
  simp [Tensor.pullback, zeroYMatching, Tensor.matrixCoefficients, eq_comm]

theorem zeroZMatching_matrixCoefficients :
    Tensor.pullback (fun x : Unit × U => x.2)
      (fun y : U × Unit => y.1) (fun _ : Unit × Unit => ())
      (zeroZMatching (F := F) (U := U)) =
    Tensor.matrixCoefficients Unit U Unit := by
  funext x y z
  simp [Tensor.pullback, zeroZMatching, Tensor.matrixCoefficients]

def complementaryMatching {V : Type*} [DecidableEq V] (e : U ≃ V) :
    Tensor F Unit U V := fun _ y z => if e y = z then 1 else 0

theorem complementaryMatching_pullback {V : Type*} [DecidableEq V] (e : U ≃ V) :
    Tensor.pullback id id e (complementaryMatching (F := F) e) =
      zeroXMatching (F := F) (U := U) := by
  funext x y z
  simp [Tensor.pullback, complementaryMatching, zeroXMatching]

theorem zeroXMatching_subtype (p : U → Prop) [DecidablePred p] :
    Tensor.pullback id (Subtype.val : {u // p u} → U) Subtype.val
      (zeroXMatching (F := F) (U := U)) =
      zeroXMatching (F := F) (U := {u // p u}) := by
  funext x y z
  simp [Tensor.pullback, zeroXMatching, Subtype.ext_iff]

theorem matchingPower_leaf {X Y Z : Type*} [DecidableEq Y]
    (T : Tensor F X Y Z) (x₀ : X) (e : Y ≃ Z)
    (hmatch : ∀ y z, T x₀ y (e z) = if y = z then 1 else 0)
    (n : ℕ) (p : (Fin n → Y) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit => fun _ : Fin n => x₀)
      (Subtype.val : {w // p w} → (Fin n → Y))
      (fun w : {w // p w} => fun i => e (w.val i)) (Tensor.power T n) =
      zeroXMatching (F := F) (U := {w // p w}) := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, hmatch, zeroXMatching,
    Fintype.prod_boole, ← funext_iff, Subtype.ext_iff]

theorem matchingPower_matrixCoefficients {X Y Z : Type*} [DecidableEq Y]
    (T : Tensor F X Y Z) (x₀ : X) (e : Y ≃ Z)
    (hmatch : ∀ y z, T x₀ y (e z) = if y = z then 1 else 0)
    (n : ℕ) (p : (Fin n → Y) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => x₀)
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => e (z.1.val i))
      (Tensor.power T n) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  have h := matchingPower_leaf T x₀ e hmatch n p
  have hp := congrArg (Tensor.pullback (fun _ : Unit × Unit => ())
    (fun y : Unit × {w // p w} => y.2)
    (fun z : {w // p w} × Unit => z.1)) h
  rw [zeroXMatching_matrixCoefficients] at hp
  exact hp

theorem rankAtMost_matchingPower_leaf {X Y Z : Type*} [DecidableEq Y]
    (T : Tensor F X Y Z) (x₀ : X) (e : Y ≃ Z)
    (hmatch : ∀ y z, T x₀ y (e z) = if y = z then 1 else 0)
    (n : ℕ) (p : (Fin n → Y) → Prop) [DecidablePred p]
    {r : ℕ} (hT : Tensor.RankAtMost (Tensor.power T n) r) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) Unit Unit {w // p w}) r := by
  rw [← matchingPower_matrixCoefficients T x₀ e hmatch n p]
  exact hT.pullback _ _ _

section ExactLabeledWords

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev LabeledExactWords (counts b : A → ℕ) :=
  Σ w : ExactWords counts, ∀ i : Fin (∑ a, counts a), Fin (b (w.val i))

theorem labelings_card {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → A) (b : A → ℕ) :
    Fintype.card (∀ i, Fin (b (w i))) =
      ∏ a, b a ^ wordPopulation w a := by
  classical
  simp only [Fintype.card_pi, Fintype.card_fin]
  calc
    (∏ i, b (w i)) = ∏ s : Σ a, {i // w i = a}, b s.1 := by
      rw [← (Equiv.sigmaFiberEquiv w).prod_comp (fun i => b (w i))]
      apply Finset.prod_congr rfl
      intro s _
      exact congrArg b s.2.property
    _ = ∏ a, b a ^ wordPopulation w a := by
      simp [Fintype.prod_sigma, wordPopulation]

theorem labeledExactWords_card (counts b : A → ℕ) :
    Fintype.card (LabeledExactWords counts b) =
      Nat.multinomial Finset.univ counts * ∏ a, b a ^ counts a := by
  classical
  rw [Fintype.card_sigma]
  have hcard : ∀ w : ExactWords counts,
      Fintype.card (∀ i : Fin (∑ a, counts a), Fin (b (w.val i))) =
        ∏ a, b a ^ counts a := by
    intro w
    rw [labelings_card]
    simp only [w.property]
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    exactWords_card]

theorem labeledExactWords_card_pos (counts b : A → ℕ)
    (hb : ∀ a, counts a ≠ 0 → 0 < b a) :
    0 < Fintype.card (LabeledExactWords counts b) := by
  classical
  rw [labeledExactWords_card]
  apply Nat.mul_pos (Nat.multinomial_pos Finset.univ counts)
  apply Finset.prod_pos
  intro a _
  by_cases h : counts a = 0
  · simp [h]
  · exact pow_pos (hb a h) _

end ExactLabeledWords

structure Dimensions where
  rows : ℕ
  inner : ℕ
  cols : ℕ
  deriving DecidableEq

def Dimensions.volume (d : Dimensions) : ℕ := d.rows * d.inner * d.cols

def Dimensions.product (d e : Dimensions) : Dimensions :=
  ⟨d.rows * e.rows, d.inner * e.inner, d.cols * e.cols⟩

theorem Dimensions.volume_product (d e : Dimensions) :
    (d.product e).volume = d.volume * e.volume := by
  simp only [Dimensions.product, Dimensions.volume]
  ring

def historyDimensions {C : Type*} [Fintype C] (d : C → Dimensions) : Dimensions :=
  ⟨∏ c, (d c).rows, ∏ c, (d c).inner, ∏ c, (d c).cols⟩

theorem historyDimensions_volume {C : Type*} [Fintype C] (d : C → Dimensions) :
    (historyDimensions d).volume = ∏ c, (d c).volume := by
  simp [historyDimensions, Dimensions.volume, Finset.prod_mul_distrib]

end MatrixMultiplication.LeafVolumes





noncomputable section

namespace MatrixMultiplication.ExactStatisticWords

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]

abbrev Words (statistic : U → A) (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → U //
    ∀ a, wordPopulation (statistic ∘ w) a = counts a}

def statisticWord (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) : ExactWords counts :=
  ⟨statistic ∘ w.val, w.property⟩

omit [Fintype U] [DecidableEq U] in
theorem empiricalLaw_eq (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) :
    InheritedMasks.empiricalLaw (statistic ∘ w.val) =
      fun a => (counts a : ℝ) / (∑ a, counts a : ℕ) := by
  funext a
  simp only [InheritedMasks.empiricalLaw, w.property, Fintype.card_fin]

omit [Fintype U] [DecidableEq U] in
theorem typeWindow_of_counts (statistic : U → A) (counts : A → ℕ)
    (w : Words statistic counts) (ν : A → ℝ) (η : ℝ)
    (happrox : ∀ a, |(counts a : ℝ) / (∑ a, counts a : ℕ) - ν a| ≤ η) :
    InheritedMasks.typeWindow ν η (statistic ∘ w.val) := by
  intro a
  rw [empiricalLaw_eq]
  exact happrox a

omit [Fintype U] [DecidableEq U] in
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

omit [DecidableEq U] in
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

omit [DecidableEq U] in
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

omit [Fintype A] [DecidableEq U] in
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

omit [DecidableEq U] in
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
end

end MatrixAllFields

end OAI
