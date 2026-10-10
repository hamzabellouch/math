import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWShapeLeaves
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ExactStatisticWords
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.ExactRecovery

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWWindowedLeaves

open MatrixMultiplication.Foundation CWStrands CWShapeLeaves CWLeafRestrictions InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Raw (n : ℕ) := Fin n → Fin 7
abbrev Alphabet (n a : ℕ) := {w : Raw n // weight w = a}

def complementWord {n : ℕ} (w : Raw n) : Raw n := fun i => complement 5 (w i)
def zeroWord (n : ℕ) : Raw n := fun _ => 0

variable (F : Type*) [CommRing F]

theorem zeroX_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) ![0, a, b] (zeroWord n) u.val (complementWord v.val) =
      if u = v then 1 else 0 := by
  have h := zeroX_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h ((), ())) ((), u)) (v, ())
  change shapeTensor (F := F) (Fin n) ![0, a, b] (fun _ => 0) u.val
    (fun i => complement 5 (v.val i)) = if u = v then 1 else 0
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true] using hh

theorem zeroY_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) ![a, 0, b] u.val (zeroWord n) (complementWord v.val) =
      if u = v then 1 else 0 := by
  have h := zeroY_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h (u, ())) ((), ())) ((), v)
  have huv : (v = u) ↔ (u = v) := eq_comm
  change shapeTensor (F := F) (Fin n) ![a, 0, b] u.val (fun _ => 0)
    (fun i => complement 5 (v.val i)) = if u = v then 1 else 0
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true, huv] using hh

theorem zeroZ_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) ![a, b, 0] u.val (complementWord v.val) (zeroWord n) =
      if u = v then 1 else 0 := by
  have h := zeroZ_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h ((), u)) (v, ())) ((), ())
  change shapeTensor (F := F) (Fin n) ![a, b, 0] u.val
    (fun i => complement 5 (v.val i)) (fun _ => 0) = if u = v then 1 else 0
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true] using hh

section Classes

variable (n a b m : ℕ) (hab : a + b = 2 * n)
    (p : (Fin m → Alphabet n a) → Prop)

def rawSelected (w : {w : Fin m → Alphabet n a // p w}) : Fin m → Raw n :=
  fun i => (w.val i).val

def complementarySelected (w : {w : Fin m → Alphabet n a // p w}) : Fin m → Raw n :=
  fun i => complementWord (w.val i).val

include hab

theorem zeroX_class :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun y : Unit × {w // p w} => rawSelected n a m p y.2)
      (fun z : {w // p w} × Unit => complementarySelected n a m p z.1)
      (Tensor.power (shapeTensor (F := F) (Fin n) ![0, a, b]) m) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, rawSelected, complementarySelected,
    zeroX_local F n a b hab, Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

theorem zeroY_class :
    Tensor.pullback (fun x : {w // p w} × Unit => rawSelected n a m p x.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun z : Unit × {w // p w} => complementarySelected n a m p z.2)
      (Tensor.power (shapeTensor (F := F) (Fin n) ![a, 0, b]) m) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, rawSelected, complementarySelected,
    zeroY_local F n a b hab, Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff, eq_comm]

theorem zeroZ_class :
    Tensor.pullback (fun x : Unit × {w // p w} => rawSelected n a m p x.2)
      (fun y : {w // p w} × Unit => complementarySelected n a m p y.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (Tensor.power (shapeTensor (F := F) (Fin n) ![a, b, 0]) m) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, rawSelected, complementarySelected,
    zeroZ_local F n a b hab, Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

theorem zeroX_masked
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : keepX (fun _ => zeroWord n))
    (hy : ∀ w, keepY (rawSelected n a m p w))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun y : Unit × {w // p w} => rawSelected n a m p y.2)
      (fun z : {w // p w} × Unit => complementarySelected n a m p z.1)
      (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) ![0, a, b]) m)
        keepX keepY keepZ) = Tensor.matrixCoefficients Unit Unit {w // p w} := by
  have h := zeroX_class F n a b m hab p
  funext x y z
  simpa only [Tensor.pullback, ExactRecovery.delete, hx, hy, hz, and_self, ite_true] using
    congrFun (congrFun (congrFun h x) y) z

theorem zeroY_masked
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : keepY (fun _ => zeroWord n))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    Tensor.pullback (fun x : {w // p w} × Unit => rawSelected n a m p x.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun z : Unit × {w // p w} => complementarySelected n a m p z.2)
      (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) ![a, 0, b]) m)
        keepX keepY keepZ) = Tensor.matrixCoefficients {w // p w} Unit Unit := by
  have h := zeroY_class F n a b m hab p
  funext x y z
  simpa only [Tensor.pullback, ExactRecovery.delete, hx, hy, hz, and_self, ite_true] using
    congrFun (congrFun (congrFun h x) y) z

theorem zeroZ_masked
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : ∀ w, keepY (complementarySelected n a m p w))
    (hz : keepZ (fun _ => zeroWord n)) :
    Tensor.pullback (fun x : Unit × {w // p w} => rawSelected n a m p x.2)
      (fun y : {w // p w} × Unit => complementarySelected n a m p y.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) ![a, b, 0]) m)
        keepX keepY keepZ) = Tensor.matrixCoefficients Unit {w // p w} Unit := by
  have h := zeroZ_class F n a b m hab p
  funext x y z
  simpa only [Tensor.pullback, ExactRecovery.delete, hx, hy, hz, and_self, ite_true] using
    congrFun (congrFun (congrFun h x) y) z

theorem zeroX_restriction
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : keepX (fun _ => zeroWord n))
    (hy : ∀ w, keepY (rawSelected n a m p w))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    ∃ (A : (Unit × Unit) → (Fin m → Raw n) → F)
      (B : (Unit × {w // p w}) → (Fin m → Raw n) → F)
      (C : ({w // p w} × Unit) → (Fin m → Raw n) → F),
      Tensor.restrict A B C
        (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) ![0, a, b]) m)
          keepX keepY keepZ) = Tensor.matrixCoefficients Unit Unit {w // p w} := by
  refine ⟨(fun _ v => if v = (fun _ => zeroWord n) then 1 else 0),
    (fun y v => if v = rawSelected n a m p y.2 then 1 else 0),
    (fun z v => if v = complementarySelected n a m p z.1 then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact zeroX_masked F n a b m hab p keepX keepY keepZ hx hy hz

theorem zeroY_restriction
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : keepY (fun _ => zeroWord n))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    ∃ (A : ({w // p w} × Unit) → (Fin m → Raw n) → F)
      (B : (Unit × Unit) → (Fin m → Raw n) → F)
      (C : (Unit × {w // p w}) → (Fin m → Raw n) → F),
      Tensor.restrict A B C
        (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) ![a, 0, b]) m)
          keepX keepY keepZ) = Tensor.matrixCoefficients {w // p w} Unit Unit := by
  refine ⟨(fun x v => if v = rawSelected n a m p x.1 then 1 else 0),
    (fun _ v => if v = (fun _ => zeroWord n) then 1 else 0),
    (fun z v => if v = complementarySelected n a m p z.2 then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact zeroY_masked F n a b m hab p keepX keepY keepZ hx hy hz

theorem zeroZ_restriction
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : ∀ w, keepY (complementarySelected n a m p w))
    (hz : keepZ (fun _ => zeroWord n)) :
    ∃ (A : (Unit × {w // p w}) → (Fin m → Raw n) → F)
      (B : ({w // p w} × Unit) → (Fin m → Raw n) → F)
      (C : (Unit × Unit) → (Fin m → Raw n) → F),
      Tensor.restrict A B C
        (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) ![a, b, 0]) m)
          keepX keepY keepZ) = Tensor.matrixCoefficients Unit {w // p w} Unit := by
  refine ⟨(fun x v => if v = rawSelected n a m p x.2 then 1 else 0),
    (fun y v => if v = complementarySelected n a m p y.1 then 1 else 0),
    (fun _ v => if v = (fun _ => zeroWord n) then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact zeroZ_masked F n a b m hab p keepX keepY keepZ hx hy hz

end Classes

section ExactWindows

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem exact_selected_window (n a : ℕ) (statistic : Raw n → A)
    (counts : A → ℕ) (ν : A → ℝ) (η : ℝ)
    (happrox : ∀ s, |(counts s : ℝ) / (∑ s, counts s : ℕ) - ν s| ≤ η)
    (w : ExactStatisticWords.Words (fun u : Alphabet n a => statistic u.val) counts) :
    typeWindow ν η (fun i => statistic (w.val i).val) :=
  ExactStatisticWords.typeWindow_of_counts _ counts w ν η happrox

theorem exact_complementary_window (n a : ℕ) (statistic : Raw n → A)
    (κ : A ≃ A)
    (hstatistic : ∀ u : Alphabet n a, statistic (complementWord u.val) = κ (statistic u.val))
    (counts : A → ℕ) (ν : A → ℝ) (η : ℝ)
    (happrox : ∀ s, |(counts s : ℝ) / (∑ s, counts s : ℕ) - ν s| ≤ η)
    (w : ExactStatisticWords.Words (fun u : Alphabet n a => statistic u.val) counts) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (complementWord (w.val i).val)) := by
  have heq : (fun i => statistic (complementWord (w.val i).val)) =
      κ ∘ (fun i => statistic (w.val i).val) := by
    funext i
    exact hstatistic (w.val i)
  rw [heq]
  exact (typeWindow_equiv ν η _ κ).mpr
    (exact_selected_window n a statistic counts ν η happrox w)

omit [Fintype A] in
theorem zero_window (n m : ℕ) (hm : 0 < m) (statistic : Raw n → A)
    (ν : A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hν : ∀ s, ν s = if statistic (zeroWord n) = s then 1 else 0) :
    typeWindow ν η (fun _ : Fin m => statistic (zeroWord n)) := by
  intro s
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  by_cases hs : statistic (zeroWord n) = s <;>
    simpa [empiricalLaw, wordPopulation, hν s, hs, hm'] using hη

end ExactWindows

end MatrixMultiplication.CWWindowedLeaves

end

end OAI
