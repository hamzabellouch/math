import Mathlib
import OAI.Probability.BinarySweep.Trajectories.Trajectory

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
open Polynomial

def fallingMoment (m h n : ℕ) : ℝ := (m:ℝ)^n / ((m-h).descFactorial n : ℝ)

@[simp] lemma fallingMoment_zero (m h : ℕ) : fallingMoment m h 0 = 1 := by
  simp [fallingMoment]

lemma fallingMoment_pos {m h n : ℕ} (hm : 0 < m) (hn : h+n ≤ m) :
    0 < fallingMoment m h n := by
  apply div_pos (pow_pos (Nat.cast_pos.mpr hm) _)
  exact Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (by omega))

lemma fallingMoment_succ {m h n : ℕ} (hn : h+n < m) :
    ((m:ℝ)-h-n) * fallingMoment m h (n+1) = m * fallingMoment m h n := by
  have hh : h ≤ m := by omega
  have hi : n ≤ m-h := by omega
  have hd : ((m-h).descFactorial n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hi))
  have hc : ((m:ℝ)-h-n) ≠ 0 := by
    have hh' : (h:ℝ)+n < m := by exact_mod_cast hn
    exact ne_of_gt (by linarith)
  simp only [fallingMoment,Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_sub hh,
    Nat.cast_sub hi,pow_succ]
  field_simp

def lineMoment (m h : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => (fallingMoment m h n) • LinearMap.id)

lemma lineMoment_monomial (m h n : ℕ) (c : ℝ) :
    lineMoment m h (monomial n c) = c * fallingMoment m h n := by
  simp [lineMoment,Polynomial.lsum_apply,Polynomial.sum_monomial_index,mul_comm]

lemma lineMoment_X_pow (m h n : ℕ) :
    lineMoment m h (X^n) = fallingMoment m h n := by
  simpa only [one_mul,monomial_one_right_eq_X_pow] using lineMoment_monomial m h n 1

def stein (m h : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (C ((m:ℝ)-h) * X)) -
    (LinearMap.mulLeft ℝ (X^2)).comp (Polynomial.derivative) -
    LinearMap.mulLeft ℝ (C (m:ℝ))

lemma stein_apply (m h : ℕ) (P : ℝ[X]) :
    stein m h P = C ((m:ℝ)-h)*X*P - X^2*derivative P - C (m:ℝ)*P := rfl

lemma lineMoment_stein_monomial {m h n : ℕ} (hn : h+n < m) (c : ℝ) :
    lineMoment m h (stein m h (monomial n c)) = 0 := by
  rw [stein_apply,mul_assoc,X_mul_monomial,C_mul_monomial,derivative_monomial,
    X_pow_mul_monomial,C_mul_monomial]
  simp only [LinearMap.map_sub,lineMoment_monomial]
  have hh := fallingMoment_succ hn
  cases n with
  | zero => simp only [Nat.cast_zero,mul_zero,zero_mul,sub_zero] at *; linear_combination c * hh
  | succ n => simp only [Nat.add_sub_cancel] at *; linear_combination c * hh

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma lineLaw_zero (d : ℕ) (σ : Equiv.Perm (Slot d)) :
    lineLaw d 0 σ = (Fintype.card (Equiv.Perm (Slot d)):ℝ)⁻¹ := by
  simp only [lineLaw, sub_zero, one_mul, zero_mul, add_zero, uniformLaw]

lemma assignmentWeight_uniform_of_eq {X I : Type*} [Fintype X] [Fintype I]
    (p : Equiv.Perm X → ℝ) (hp : ∀σ, p σ=((Fintype.card X).factorial:ℝ)⁻¹)
    (A B : I ↪ X) :
    assignmentWeight p A B = ((Fintype.card X).descFactorial (Fintype.card I):ℝ)⁻¹ := by
  have he : p = fun _ => (Fintype.card (Equiv.Perm X):ℝ)⁻¹ := by
    funext σ
    rw [hp]
    simp only [Fintype.card_perm]
  rw [he]
  exact assignmentWeight_uniform A B

lemma localPathWeight_zero (j : Fin b) (y : GridOutside bits j) :
    localPathWeight H 0 j y = ((2^bits j).descFactorial (lineHoles H j y):ℝ)⁻¹ := by
  have hp (σ : Equiv.Perm (Slot (bits j))) :
      lineLaw (bits j) 0 σ=((Fintype.card (Slot (bits j))).factorial:ℝ)⁻¹ := by
    rw [lineLaw_zero]
    simp only [Fintype.card_perm]
  have hw := assignmentWeight_uniform_of_eq _ hp (lineInput H j y) (lineOutput H j y)
  have hc : Fintype.card (Slot (bits j))=2^bits j := by
    simp only [Slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  have hh : Fintype.card (LinePaths H j y)=lineHoles H j y := by
    unfold lineHoles LinePaths
    congr!
  rw [hc,hh] at hw
  exact hw

lemma card_fin_sum_pred {a c : ℕ} (P : Fin (a+c) → Prop) :
    Fintype.card {i // P i} = Fintype.card {i : Fin a // P (i.castAdd c)} +
      Fintype.card {i : Fin c // P (i.natAdd a)} := by
  have he := Fintype.card_congr ((finSumFinEquiv.symm).subtypeEquiv
    (p := P) (q := fun i : Fin a ⊕ Fin c => P (finSumFinEquiv i))
    (fun _ => by simp))
  change Fintype.card {i : Fin (a+c) // P i} =
    Fintype.card {i : Fin a ⊕ Fin c // P (finSumFinEquiv i)} at he
  rw [he,Fintype.card_congr (Equiv.subtypeSum (p := fun i : Fin a ⊕ Fin c => P (finSumFinEquiv i))),
    Fintype.card_sum]
  rfl

def trackedLineCount (x : Placement H k 0) (g : ConditionalChoices H)
    (j : Fin b) (y : GridOutside bits j) : ℕ :=
  Fintype.card {i : Fin k // (fun a : {a : Fin b // a≠j} =>
    gridPartialSweep bits g.val j.castSucc (x i).val a)=y}

lemma lineHoles_augment (x : Placement H k 0) (g : ConditionalChoices H)
    (j : Fin b) (y : GridOutside bits j) :
    lineHoles (augmentByChoice H x g) j y = lineHoles H j y + trackedLineCount H x g j y := by
  unfold lineHoles
  have he := card_fin_sum_pred (fun i : Fin (h+k) =>
    (fun a : {a : Fin b // a≠j} => (augmentByChoice H x g).position j.castSucc i a)=y)
  trans Fintype.card {i : Fin h // (fun a : {a : Fin b // a≠j} =>
    (augmentByChoice H x g).position j.castSucc (i.castAdd k) a)=y} +
    Fintype.card {i : Fin k // (fun a : {a : Fin b // a≠j} =>
    (augmentByChoice H x g).position j.castSucc (i.natAdd h) a)=y}
  · convert he using 1 <;> congr!
  congr 1
  · apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    change (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc
      (Fin.append (H.position 0) (fun i => (x i).val) (i.castAdd k)) a)=y ↔ _
    rw [Fin.append_left,gridPartialSweep_path H g.val g.property]
  · unfold trackedLineCount
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    change (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc
      (Fin.append (H.position 0) (fun i => (x i).val) (i.natAdd h)) a)=y ↔ _
    rw [Fin.append_right]

lemma uniform_extension_ratio {m a c : ℕ} (ha : a ≤ m) :
    ((m.descFactorial (a+c):ℝ)⁻¹ / (m.descFactorial a:ℝ)⁻¹) =
      ((m-a).descFactorial c:ℝ)⁻¹ := by
  have he := Nat.descFactorial_mul_descFactorial (show a≤a+c by omega) (n:=m)
  simp only [Nat.add_sub_cancel_left] at he
  rw [← he,Nat.cast_mul,mul_inv_rev,div_inv_eq_mul]
  have hn : (m.descFactorial a:ℝ)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr ha).ne'
  field_simp

theorem placementProbability_zero_factor (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H 0 x (placementBijection H k g x) =
      ∏j, ∏y : GridOutside bits j,
        ((2^bits j-lineHoles H j y).descFactorial (trackedLineCount H x g j y):ℝ)⁻¹ := by
  rw [placementProbability_augmentation,pathExtension_event_ratio (augmentByChoice_extension H x g),
    conditionalNormalizer_eq_prod,conditionalNormalizer_eq_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro y _
  rw [localPathWeight_zero,localPathWeight_zero,lineHoles_augment]
  exact uniform_extension_ratio (lineHoles_le H j y)

lemma sum_trackedLineCount (x : Placement H k 0) (g : ConditionalChoices H) (j : Fin b) :
    ∑y : GridOutside bits j, trackedLineCount H x g j y=k := by
  have he := Fintype.card_sigma (α := fun y : GridOutside bits j => {i : Fin k //
    (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc (x i).val a)=y})
  unfold trackedLineCount
  rw [← he]
  trans Fintype.card (Fin k)
  · exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun i : Fin k =>
      fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc (x i).val a))
  · exact Fintype.card_fin k

theorem placementProbability_zero_scaled (x : Placement H k 0) (g : ConditionalChoices H) :
    (gridSize bits:ℝ)^k * placementProbability H 0 x (placementBijection H k g x) =
      ∏j, ∏y : GridOutside bits j,
        Sparse.fallingMoment (2^bits j) (lineHoles H j y) (trackedLineCount H x g j y) := by
  rw [placementProbability_zero_factor]
  have he : (gridSize bits:ℝ)^k = ∏j, ∏y : GridOutside bits j,
      ((2^bits j:ℕ):ℝ)^trackedLineCount H x g j y := by
    simp_rw [Finset.prod_pow_eq_pow_sum,sum_trackedLineCount]
    rw [Finset.prod_pow]
    congr 1
    simp only [gridSize,Nat.cast_prod,Nat.cast_pow]
  rw [he,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_mul_distrib]
  rfl

end BinaryCoordinateSweeps

end

end OAI
