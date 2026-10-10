import Mathlib
import OAI.Computability.MinUncut.Estimates.F2

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators
open MeasureTheory ProbabilityTheory
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

def arraySum (B : FaceArray A m n) (x : Point m n) : Forms A := ∑ i : Fin m, B ⟨i,face x i⟩

lemma arraySum_apply (B : FaceArray A m n) (x : Point m n) (a : A) :
    arraySum B x a = ∑ i : Fin m, B ⟨i,face x i⟩ a := by
  let ev : Forms A →+ F₂ := { toFun := fun L => L a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact map_sum ev (fun i : Fin m => B ⟨i,face x i⟩) Finset.univ

lemma labelCode_add (B C : FaceArray A m n) (a : A) :
    labelCode (B+C) a = labelCode B a + labelCode C a := by
  apply Subtype.ext
  exact (faceSum m n).map_add _ _

lemma labelCode_eq_of_arraySum (B C : FaceArray A m n) (h : ∀ x, arraySum B x = arraySum C x)
    (a : A) : labelCode B a = labelCode C a := by
  apply Subtype.ext
  funext x
  have hh := congrArg (fun L : Forms A => L a) (h x)
  simpa only [arraySum_apply, labelCode_apply] using hh

lemma gradient_eq_of_arraySum (f : FoldedProof A) (B C : FaceArray A m n)
    (h : ∀ x, arraySum B x = arraySum C x) (σ η : ℝ) :
    gradient f B σ η = gradient f C σ η := by
  have hp : ∀ u d, pullQuery B u d = pullQuery C u d := by
    intros u d; funext a
    simp only [pullQuery, labelCode_eq_of_arraySum B C h]
  funext c x
  simp only [gradient, smooth, hp]

def addConstantArray (B : FaceArray A m n) (k : Row m n → F₂) : FaceArray A m n :=
  fun r => B r + AffineMap.const F₂ A (k r)

def rowCode (k : Row m n → F₂) : Code m n := ⟨faceSum m n k, ⟨k,rfl⟩⟩

lemma labelCode_addConstantArray (B : FaceArray A m n) (k : Row m n → F₂) (a : A) :
    labelCode (addConstantArray B k) a = labelCode B a + rowCode k := by
  apply Subtype.ext
  funext x
  simp [labelCode_apply, addConstantArray, rowCode, faceSum, Finset.sum_add_distrib]

def diagonal {ι : Type*} (k : ι → F₂) (u : ι → ℝ) : ι → ℝ :=
  fun x => BinaryFourier.sign (k x)*u x

lemma diagonal_involutive {ι : Type*} (k : ι → F₂) : Function.Involutive (diagonal k) := by
  intro u
  funext x
  dsimp [diagonal]
  rw [← mul_assoc, ← sq, BinaryFourier.sign_sq, one_mul]

lemma diagonal_add {ι : Type*} (k : ι → F₂) (u v : ι → ℝ) :
    diagonal k (u+v) = diagonal k u + diagonal k v := by
  funext x; exact mul_add _ _ _

lemma diagonal_smul {ι : Type*} (k : ι → F₂) (t : ℝ) (u : ι → ℝ) :
    diagonal k (t • u) = t • diagonal k u := by
  funext x; dsimp [diagonal]; ring

lemma diagonal_preserves {ι : Type*} [Fintype ι] (k : ι → F₂) :
    MeasurePreserving (diagonal k) (gauss ι) (gauss ι) := by
  apply measurePreserving_pi
  intro x
  change MeasurePreserving (fun t : ℝ => BinaryFourier.sign (k x)*t) _ _
  by_cases hk : k x = 0
  · rw [show (fun t : ℝ => BinaryFourier.sign (k x)*t) = id by funext t; simp [hk]]
    exact MeasurePreserving.id (gaussianReal 0 1)
  · rw [show (fun t : ℝ => BinaryFourier.sign (k x)*t) = (fun t => -t) by
      funext t; simp [BinaryFourier.sign, hk]]
    exact ⟨measurable_neg, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩

lemma integral_diagonal {ι : Type*} [Fintype ι] (k : ι → F₂) (F : (ι → ℝ) → ℝ) :
    (∫ u, F (diagonal k u) ∂gauss ι) = ∫ u, F u ∂gauss ι := by
  let e : Homeomorph (ι → ℝ) (ι → ℝ) :=
    { toEquiv := (diagonal_involutive k).toPerm
      continuous_toFun := by fun_prop [diagonal]
      continuous_invFun := by fun_prop [diagonal] }
  exact (diagonal_preserves k).integral_comp e.measurableEmbedding F

lemma integral_code_translate (k : Code m n) (F : (Code m n → ℝ) → ℝ) :
    (∫ l, F (fun z => l (z+k)) ∂gauss (Code m n)) = ∫ l, F l ∂gauss (Code m n) := by
  let e := Equiv.addRight k
  let p := MeasurableEquiv.piCongrLeft (fun _ : Code m n => ℝ) e
  have hp := measurePreserving_piCongrLeft (fun _ : Code m n => gaussianReal 0 1) e
  have he (l : Code m n → ℝ) : p l = (fun z => l (z+k)) := by
    funext z
    calc p l z = p l (e (e.symm z)) := by rw [e.apply_symm_apply]
         _ = l (e.symm z) := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Code m n => ℝ) e l (e.symm z)
         _ = l (z+k) := by
           congr 1
           simp [e, Equiv.addRight, BinaryFourier.neg_eq]
  have hh := hp.integral_comp p.measurableEmbedding F
  change (∫ l, F (p l) ∂gauss (Code m n)) = ∫ l, F l ∂gauss (Code m n) at hh
  simpa only [he] using hh

lemma query_translate (k z : Code m n) (u : Point m n → ℝ) (d : Code m n → ℝ) :
    query u d (z+k) = query (diagonal k.val u) (fun w => d (w+k)) z := by
  unfold query
  congr 2
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change u x * BinaryFourier.sign (z.val x+k.val x) = _
  rw [BinaryFourier.sign_add]
  dsimp [diagonal]
  ring

lemma pullQuery_addConstantArray (B : FaceArray A m n) (k : Row m n → F₂)
    (u : Point m n → ℝ) (d : Code m n → ℝ) :
    pullQuery (addConstantArray B k) u d =
      pullQuery B (diagonal (rowCode k).val u) (fun z => d (z+rowCode k)) := by
  funext a
  dsimp only [pullQuery]
  rw [labelCode_addConstantArray, query_translate]

lemma smooth_addConstantArray (f : FoldedProof A) (B : FaceArray A m n) (k : Row m n → F₂)
    (σ η : ℝ) (c : Point m n → ℝ) :
    smooth f (addConstantArray B k) σ η c = smooth f B σ η (diagonal (rowCode k).val c) := by
  unfold smooth
  simp_rw [pullQuery_addConstantArray, diagonal_add, diagonal_smul]
  have hl (g : Point m n → ℝ) := integral_code_translate (rowCode k)
    (fun l => bitSign (f.answer (pullQuery B
      (diagonal (rowCode k).val c+σ • diagonal (rowCode k).val g) (η • l))))
  simp_rw [show ∀ (l : Code m n → ℝ), (fun z => (η • l) (z+rowCode k)) =
      η • (fun z => l (z+rowCode k)) from fun l => rfl, hl]
  exact integral_diagonal (rowCode k).val (fun g => ∫ l : Code m n → ℝ,
    bitSign (f.answer (pullQuery B (diagonal (rowCode k).val c+σ • g) (η • l))) ∂gauss (Code m n))

variable [Fintype A]

theorem gradient_addConstantArray (f : FoldedProof A) (B : FaceArray A m n)
    (k : Row m n → F₂) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f (addConstantArray B k) σ η c x =
      BinaryFourier.sign ((rowCode k).val x) * gradient f B σ η (diagonal (rowCode k).val c) x := by
  rw [gradient_convolution f _ hσ, gradient_convolution f _ hσ]
  simp_rw [pullQuery_addConstantArray, diagonal_add, diagonal_smul]
  have hl (g : Point m n → ℝ) := integral_code_translate (rowCode k)
    (fun l => g x*bitSign (f.answer (pullQuery B
      (diagonal (rowCode k).val c+σ • diagonal (rowCode k).val g) (η • l))))
  simp_rw [show ∀ (l : Code m n → ℝ), (fun z => (η • l) (z+rowCode k)) =
      η • (fun z => l (z+rowCode k)) from fun l => rfl, hl]
  have hg := integral_diagonal (rowCode k).val (fun g =>
    ∫ l : Code m n → ℝ, g x * bitSign (f.answer (pullQuery B
      (diagonal (rowCode k).val c+σ • g) (η • l))) ∂gauss (Code m n))
  dsimp only [diagonal] at hg
  simp_rw [mul_assoc, integral_const_mul] at hg
  simp_rw [integral_const_mul]
  rw [← hg]
  have hs := BinaryFourier.sign_sq ((rowCode k).val x)
  ring_nf at hs ⊢
  simp only [hs, one_mul]
end MinUncut.Inner
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

def doubleMatch (i j : Fin m) (q x : Point m n) : Prop :=
  ∀ t : Fin m, t ≠ i → t ≠ j → x t = q t

def rowFill (q : Point m n) (r : Row m n) : Point m n :=
  fun t => if ht : t = r.1 then q t else r.2 ⟨t,ht⟩

lemma doubleMatch_rowFill (i j : Fin m) (q x : Point m n) (t : Fin m) (ht : t=i ∨ t=j) :
    doubleMatch i j q (rowFill q ⟨t,face x t⟩) ↔ doubleMatch i j q x := by
  unfold doubleMatch
  have hh (u : Fin m) (hui : u ≠ i) (huj : u ≠ j) : u ≠ t := by
    rcases ht with rfl | rfl <;> assumption
  simp only [rowFill, face]
  constructor
  · intro h u hui huj
    simpa only [dite_eq_right (hh u hui huj)] using h u hui huj
  · intro h u hui huj
    simpa only [dite_eq_right (hh u hui huj)] using h u hui huj

def cylinderArray (i j : Fin m) (q : Point m n) (a : Forms A) : FaceArray A m n :=
  fun r => if (r.1=i ∨ r.1=j) ∧ doubleMatch i j q (rowFill q r) then a else 0

lemma cylinderArray_local (i j : Fin m) (q x : Point m n) (a : Forms A) (t : Fin m) :
    cylinderArray i j q a ⟨t,face x t⟩ =
      if t=i ∨ t=j then (if doubleMatch i j q x then a else 0) else 0 := by
  by_cases ht : t=i ∨ t=j
  · simp only [cylinderArray, ht, true_and, ite_true, doubleMatch_rowFill i j q x t ht]
  · simp only [cylinderArray, ht, false_and, ite_false]

lemma cylinderArray_sum_zero (i j : Fin m) (hij : i ≠ j) (q x : Point m n) (a : Forms A) :
    arraySum (cylinderArray i j q a) x = 0 := by
  unfold arraySum
  simp_rw [cylinderArray_local]
  have he (t : Fin m) : (if t=i ∨ t=j then (if doubleMatch i j q x then a else 0) else 0) =
      (if t=i then (if doubleMatch i j q x then a else 0) else 0) +
      (if t=j then (if doubleMatch i j q x then a else 0) else 0) := by
    by_cases hi : t=i <;> by_cases hj : t=j <;> simp_all
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact BinaryFourier.self_add _

lemma arraySum_add (B C : FaceArray A m n) (x : Point m n) :
    arraySum (B+C) x = arraySum B x + arraySum C x := Finset.sum_add_distrib

theorem gradient_cylinder (f : FoldedProof A) (B : FaceArray A m n)
    (i j : Fin m) (hij : i ≠ j) (q : Point m n) (a : Forms A) (σ η : ℝ) :
    gradient f (B+cylinderArray i j q a) σ η = gradient f B σ η := by
  apply gradient_eq_of_arraySum
  intro x
  rw [arraySum_add, cylinderArray_sum_zero i j hij, add_zero]

variable [Fintype A]

theorem gradient_fourier_cylinder (f : FoldedProof A) (σ η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) (α : Module.Dual F₂ (FaceArray A m n))
    (hα : BinaryFourier.coefficient (fun B => gradient f B σ η c x) α ≠ 0)
    (i j : Fin m) (hij : i ≠ j) (q : Point m n) (a : Forms A) :
    α (cylinderArray i j q a) = 0 := by
  have ht := BinaryFourier.coefficient_translate (fun B : FaceArray A m n => gradient f B σ η c x)
    α (cylinderArray i j q a)
  have hg (B : FaceArray A m n) : gradient f (cylinderArray i j q a+B) σ η c x =
      gradient f B σ η c x := by rw [add_comm, gradient_cylinder f B i j hij]
  simp only [hg] at ht
  by_contra hn
  have hs : BinaryFourier.character α (cylinderArray i j q a) = -1 := by
    simp [BinaryFourier.character, BinaryFourier.sign, hn]
  rw [hs] at ht
  exact hα (by linarith)
end MinUncut.Inner

end

end OAI
