import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrands

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWShapeLeaves

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions
open scoped BigOperators

theorem complement_word_weight {P : Type*} [Fintype P] (w : P → Fin 7) :
    weight (fun i => complement 5 (w i)) + weight w = 2 * Fintype.card P := by
  calc
    weight (fun i => complement 5 (w i)) + weight w =
        ∑ i, (CWLeafStatistics.weight (complement 5 (w i)) + CWLeafStatistics.weight (w i)) := by
      simp [weight, Finset.sum_add_distrib]
    _ = ∑ _i : P, 2 := Finset.sum_congr rfl (fun i _ => CWLeafStatistics.complement_weight (w i))
    _ = 2 * Fintype.card P := by simp [Nat.mul_comm]

theorem zeroX_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => complement 5 (z.1.val i))
      (shapeTensor (F := F) (Fin n) ![0, a, b]) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  funext x y z
  have hy : weight y.2.val = a := hp _ y.2.property
  have hz : weight (fun i => complement 5 (z.1.val i)) = b := by
    have hw := complement_word_weight z.1.val
    have hzw : weight z.1.val = a := hp _ z.1.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroX_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hy, hz, strand, Tensor.power] using hleaf

theorem zeroY_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun x : {w // p w} × Unit => x.1.val)
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (fun z : Unit × {w // p w} => fun i => complement 5 (z.2.val i))
      (shapeTensor (F := F) (Fin n) ![a, 0, b]) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  have hx : weight x.1.val = a := hp _ x.1.property
  have hz : weight (fun i => complement 5 (z.2.val i)) = b := by
    have hw := complement_word_weight z.2.val
    have hzw : weight z.2.val = a := hp _ z.2.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroY_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hx, hz, strand, Tensor.power] using hleaf

theorem zeroZ_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun x : Unit × {w // p w} => x.2.val)
      (fun y : {w // p w} × Unit => fun i => complement 5 (y.1.val i))
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (shapeTensor (F := F) (Fin n) ![a, b, 0]) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  have hx : weight x.2.val = a := hp _ x.2.property
  have hy : weight (fun i => complement 5 (y.1.val i)) = b := by
    have hw := complement_word_weight y.1.val
    have hyw : weight y.1.val = a := hp _ y.1.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroZ_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hx, hy, strand, Tensor.power] using hleaf

end MatrixMultiplication.CWShapeLeaves

end

end OAI
