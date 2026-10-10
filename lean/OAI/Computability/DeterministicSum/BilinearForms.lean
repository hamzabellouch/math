import Mathlib

namespace OAI

/-! Exact bilinear formulas and recursive simultaneous matrix products. -/

namespace DeterministicThreeSum.Rectangular
open scoped BigOperators
open Finset

structure BilinearFormula (R I J O K : Type*) where
  left : K → I → R
  right : K → J → R
  out : K → O → R

namespace BilinearFormula
variable {R I J O K : Type*} [CommRing R] [Fintype I] [Fintype J] [Fintype K]

def coeff (f : BilinearFormula R I J O K) (i : I) (j : J) (o : O) : R :=
  ∑ k, f.left k i * f.right k j * f.out k o

def eval (f : BilinearFormula R I J O K) (x : I → R) (y : J → R) (o : O) : R :=
  ∑ k, ((∑ i, f.left k i * x i) * (∑ j, f.right k j * y j)) * f.out k o

lemma eval_eq (f : BilinearFormula R I J O K) (x : I → R) (y : J → R) (o : O) :
    f.eval x y o = ∑ i, ∑ j, f.coeff i j o * x i * y j := by
  simp only [eval, coeff, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

end BilinearFormula

end DeterministicThreeSum.Rectangular

namespace DeterministicThreeSum.Rectangular
open Finset
open scoped BigOperators
namespace BilinearFormula
variable {R I J O K : Type*} [CommRing R] [Fintype I] [Fintype J] [Fintype K]
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

def evalBilinear (f : BilinearFormula R I J O K) (B : M →ₗ[R] N →ₗ[R] P)
    (x : I → M) (y : J → N) (o : O) : P :=
  ∑ k, f.out k o • B (∑ i, f.left k i • x i) (∑ j, f.right k j • y j)

theorem evalBilinear_eq (f : BilinearFormula R I J O K) (B : M →ₗ[R] N →ₗ[R] P)
    (x : I → M) (y : J → N) (o : O) :
    f.evalBilinear B x y o = ∑ i, ∑ j, f.coeff i j o • B (x i) (y j) := by
  simp only [evalBilinear, coeff, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  congr 1
  ring

end BilinearFormula

def independentMatrixTensor {E A B C : Type*} [DecidableEq E] [DecidableEq A]
    [DecidableEq B] [DecidableEq C]
    (i : E × A × B) (j : E × B × C) (o : E × A × C) : ℤ :=
  if i.1 = j.1 ∧ j.1 = o.1 ∧ i.2.1 = o.2.1 ∧ i.2.2 = j.2.1 ∧ j.2.2 = o.2.2 then 1 else 0

section Independent
variable {R E A B C K : Type*} [CommRing R]
  [Fintype E] [Fintype A] [Fintype B] [Fintype C] [Fintype K]
  [DecidableEq E] [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

lemma independent_evalBilinear
    (f : BilinearFormula R (E × A × B) (E × B × C) (E × A × C) K)
    (hf : ∀ i j o, f.coeff i j o = (independentMatrixTensor i j o : R))
    (mul : M →ₗ[R] N →ₗ[R] P) (x : E × A × B → M) (y : E × B × C → N)
    (e : E) (a : A) (c : C) :
    f.evalBilinear mul x y (e,a,c) = ∑ b, mul (x (e,a,b)) (y (e,b,c)) := by
  classical
  rw [BilinearFormula.evalBilinear_eq]
  simp only [hf, independentMatrixTensor, Fintype.sum_prod_type]
  simp [ite_and]

theorem independent_block_products {U V W : Type*} [Fintype V]
    (f : BilinearFormula R (E × A × B) (E × B × C) (E × A × C) K)
    (hf : ∀ i j o, f.coeff i j o = (independentMatrixTensor i j o : R))
    (x : E × A × B → Matrix U V R) (y : E × B × C → Matrix V W R)
    (e : E) (a : A) (c : C) :
    f.evalBilinear (mulLinearMap R) x y (e,a,c) =
      ∑ b, x (e,a,b) * y (e,b,c) := by
  exact independent_evalBilinear f hf _ x y e a c

def reindexIndependent {E' K' : Type*}
    (f : BilinearFormula R (E × A × B) (E × B × C) (E × A × C) K)
    (e : E' ≃ E) (u : K' ≃ K) :
    BilinearFormula R (E' × A × B) (E' × B × C) (E' × A × C) K' where
  left t i := f.left (u t) (e i.1,i.2)
  right t j := f.right (u t) (e j.1,j.2)
  out t o := f.out (u t) (e o.1,o.2)

omit [Fintype E] [Fintype A] [Fintype B] [Fintype C] in
lemma reindexIndependent_correct {E' K' : Type*} [Fintype K'] [DecidableEq E']
    (f : BilinearFormula R (E × A × B) (E × B × C) (E × A × C) K)
    (hf : ∀ i j o, f.coeff i j o = (independentMatrixTensor i j o : R))
    (e : E' ≃ E) (u : K' ≃ K) (i : E' × A × B) (j : E' × B × C)
    (o : E' × A × C) :
    (reindexIndependent f e u).coeff i j o = (independentMatrixTensor i j o : R) := by
  unfold BilinearFormula.coeff reindexIndependent
  change (∑ t, f.left (u t) (e i.1,i.2)*f.right (u t) (e j.1,j.2)*
    f.out (u t) (e o.1,o.2)) = _
  rw [u.sum_comp (fun z => f.left z (e i.1,i.2)*f.right z (e j.1,j.2)*
    f.out z (e o.1,o.2))]
  change f.coeff (e i.1,i.2) (e j.1,j.2) (e o.1,o.2) = _
  rw [hf]
  simp only [independentMatrixTensor, Equiv.apply_eq_iff_eq]

end Independent
end DeterministicThreeSum.Rectangular

namespace DeterministicThreeSum.Rectangular
open Finset
open scoped BigOperators
noncomputable section

abbrev DigitBox (a j : ℕ) : Type :=
  Nat.rec (Fin 1) (fun _ W => Fin a × W) j

instance digitBoxZero (a : ℕ) : OfNat (DigitBox a 0) 0 :=
  inferInstanceAs (OfNat (Fin 1) 0)
instance digitBoxSubsingleton (a : ℕ) : Subsingleton (DigitBox a 0) :=
  inferInstanceAs (Subsingleton (Fin 1))

instance digitBoxFintype (a j : ℕ) : Fintype (DigitBox a j) := by
  induction j with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ j ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin a × DigitBox a j))

lemma card_DigitBox (a j : ℕ) : Fintype.card (DigitBox a j) = a^j := by
  induction j with
  | zero => simp [DigitBox]
  | succ j ih =>
    change Fintype.card (Fin a × DigitBox a j) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, mul_comm]

def batchCount (t k : ℕ) : ℕ := t ⌈/⌉ k

lemma batchCount_covers (t k : ℕ) (hk : 0 < k) : t ≤ k * batchCount t k :=
  (ceilDiv_le_iff_le_mul hk).mp le_rfl

variable {R : Type*} [CommRing R] {a b k r j t : ℕ}

abbrev FixedFormula (R : Type*) (a b k r : ℕ) :=
  BilinearFormula R (Fin k × Fin a × Fin b) (Fin k × Fin b × Fin a)
    (Fin k × Fin a × Fin a) (Fin r)

abbrev LeftBatch (R : Type*) (a b j t : ℕ) :=
  Fin t → Matrix (DigitBox a j) (DigitBox b j) R
abbrev RightBatch (R : Type*) (a b j t : ℕ) :=
  Fin t → Matrix (DigitBox b j) (DigitBox a j) R
abbrev OutputBatch (R : Type*) (a j t : ℕ) :=
  Fin t → Matrix (DigitBox a j) (DigitBox a j) R

def paddedLeft (x : LeftBatch R a b (j+1) t) (q : Fin (batchCount t k))
    (i : Fin k × Fin a × Fin b) : Matrix (DigitBox a j) (DigitBox b j) R :=
  if h : q.val*k+i.1.val < t then
    fun u v => x ⟨q.val*k+i.1.val,h⟩ (i.2.1,u) (i.2.2,v)
  else 0

def paddedRight (y : RightBatch R a b (j+1) t) (q : Fin (batchCount t k))
    (i : Fin k × Fin b × Fin a) : Matrix (DigitBox b j) (DigitBox a j) R :=
  if h : q.val*k+i.1.val < t then
    fun u v => y ⟨q.val*k+i.1.val,h⟩ (i.2.1,u) (i.2.2,v)
  else 0

def childLeft (f : FixedFormula R a b k r) (x : LeftBatch R a b (j+1) t) :
    LeftBatch R a b j (batchCount t k*r) := fun z =>
  let qs : Fin (batchCount t k) × Fin r := finProdFinEquiv.symm z
  ∑ i, f.left qs.2 i • paddedLeft x qs.1 i

def childRight (f : FixedFormula R a b k r) (y : RightBatch R a b (j+1) t) :
    RightBatch R a b j (batchCount t k*r) := fun z =>
  let qs : Fin (batchCount t k) × Fin r := finProdFinEquiv.symm z
  ∑ i, f.right qs.2 i • paddedRight y qs.1 i

def parentBatch (hk : 0 < k) (e : Fin t) : Fin (batchCount t k) :=
  ⟨e.val/k, (Nat.div_lt_iff_lt_mul hk).mpr
    (e.isLt.trans_le (by simpa [Nat.mul_comm] using batchCount_covers t k hk))⟩

def parentSlot (hk : 0 < k) (e : Fin t) : Fin k := ⟨e.val%k,Nat.mod_lt e.val hk⟩

lemma parent_index (hk : 0 < k) (e : Fin t) :
    (parentBatch hk e).val*k+(parentSlot hk e).val = e.val := by
  simpa only [parentBatch, parentSlot, Nat.mul_comm] using Nat.div_add_mod e.val k

def combineChildren (f : FixedFormula R a b k r) (hk : 0 < k)
    (z : OutputBatch R a j (batchCount t k*r)) : OutputBatch R a (j+1) t :=
  fun e uv wv => ∑ s : Fin r,
    f.out s (parentSlot hk e,uv.1,wv.1) *
      z (finProdFinEquiv (parentBatch hk e,s)) uv.2 wv.2

lemma paddedLeft_parent (hk : 0 < k) (x : LeftBatch R a b (j+1) t)
    (e : Fin t) (u : Fin a) (v : Fin b) :
    paddedLeft x (parentBatch hk e) (parentSlot hk e,u,v) =
      fun i j => x e (u,i) (v,j) := by
  unfold paddedLeft
  erw [dite_eq_left (show (parentBatch hk e).val*k+(parentSlot hk e).val < t by
    rw [parent_index]; exact e.isLt)]
  simp only [parent_index, Fin.eta]
  rfl

lemma paddedRight_parent (hk : 0 < k) (y : RightBatch R a b (j+1) t)
    (e : Fin t) (u : Fin b) (v : Fin a) :
    paddedRight y (parentBatch hk e) (parentSlot hk e,u,v) =
      fun i j => y e (u,i) (v,j) := by
  unfold paddedRight
  erw [dite_eq_left (show (parentBatch hk e).val*k+(parentSlot hk e).val < t by
    rw [parent_index]; exact e.isLt)]
  simp only [parent_index, Fin.eta]
  rfl

lemma combineChildren_correct (f : FixedFormula R a b k r) (hk : 0 < k)
    (hf : ∀ i j o, f.coeff i j o = (independentMatrixTensor i j o : R))
    (x : LeftBatch R a b (j+1) t) (y : RightBatch R a b (j+1) t) :
    combineChildren f hk (fun z => childLeft f x z * childRight f y z) =
      fun e => x e * y e := by
  funext e uv wv
  have h := independent_block_products f hf
    (paddedLeft x (parentBatch hk e)) (paddedRight y (parentBatch hk e))
    (parentSlot hk e) uv.1 wv.1
  have hv := congrFun (congrFun h uv.2) wv.2
  simp only [BilinearFormula.evalBilinear, Matrix.sum_apply, Matrix.smul_apply,
    mulLinearMap, mulLeftLinearMap, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at hv
  change (∑ s, f.out s (parentSlot hk e,uv.1,wv.1) *
    (childLeft f x (finProdFinEquiv (parentBatch hk e,s)) *
      childRight f y (finProdFinEquiv (parentBatch hk e,s))) uv.2 wv.2) = _
  simp only [childLeft, childRight, Equiv.symm_apply_apply]
  rw [hv]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [paddedLeft_parent, paddedRight_parent]

def multiplyBatch (f : FixedFormula R a b k r) (hk : 0 < k) :
    (j t : ℕ) → LeftBatch R a b j t → RightBatch R a b j t → OutputBatch R a j t
  | 0, _, x, y => fun e _ _ => x e 0 0 * y e 0 0
  | j+1, t, x, y => combineChildren f hk
      (multiplyBatch f hk j (batchCount t k*r) (childLeft f x) (childRight f y))

theorem multiplyBatch_correct (f : FixedFormula R a b k r) (hk : 0 < k)
    (hf : ∀ i j o, f.coeff i j o = (independentMatrixTensor i j o : R))
    (j t : ℕ) (x : LeftBatch R a b j t) (y : RightBatch R a b j t) :
    multiplyBatch f hk j t x y = fun e => x e * y e := by
  induction j generalizing t with
  | zero =>
    funext e i l
    have hi : i = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    subst i; subst l
    simp [multiplyBatch, Matrix.mul_apply]
  | succ j ih =>
    rw [multiplyBatch, ih]
    exact combineChildren_correct f hk hf x y

end
end DeterministicThreeSum.Rectangular

end OAI
