import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

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
  unfold Tensor.pullback at hp ⊢
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

end OAI
