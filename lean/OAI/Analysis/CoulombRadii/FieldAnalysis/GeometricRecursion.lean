import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScreenRecurrence

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma square_recursion_bounded {x : ℕ → ℝ} {B : ℝ}
    (hb : ∀ j, x j≤B) (hs : ∀ j, (x j)^2-1≤x (j+1)) : x 0≤2 := by
  by_contra hn
  have hx0 : 2<x 0 := lt_of_not_ge hn
  have hg : ∀ j : ℕ, x 0+(j:ℝ)≤x j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hj : 2≤x j := by linarith [Nat.cast_nonneg (α:=ℝ) j]
      have hp := mul_nonneg (sub_nonneg.mpr hj) (show 0≤x j+1 by linarith)
      have hstep := hs j
      push_cast
      nlinarith
  obtain ⟨j,hj⟩ := exists_nat_gt (B-x 0)
  have hh := hg j
  have hh' := hb j
  linarith

lemma normalized_square_step {a c g h : ℝ} (ha : 1≤a) (hc : 1≤c)
    (hstep : g^2≤a*(1+h)) : (g/(a*c))^2-1≤h/(a*c*c) := by
  have ha0 : 0<a := by linarith
  have hc0 : 0<c := by linarith
  have hprod : a≤a*c := le_mul_of_one_le_right ha0.le hc
  have hsq : a≤(a*c)^2 := by nlinarith
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (mul_pos ha0 hc0))).mp
  calc
    (a*c)^2*((g/(a*c))^2-1)=g^2-(a*c)^2 := by field_simp
    _ ≤ a*h := by nlinarith
    _ = (a*c)^2*(h/(a*c*c)) := by field_simp

theorem geometric_screening_recursion {g : ℕ → ℝ} {C D : ℝ}
    (hC : 1≤C) (hD : 0≤D)
    (hcap : ∀ j, g j≤D*C^(j+1))
    (hstep : ∀ j, (g j)^2≤C^(j+1)*(1+g (j+1))) : g 0≤2*C^2 := by
  let x : ℕ → ℝ := fun j => g j/C^(j+2)
  have hC0 : 0<C := by linarith
  have hb : ∀ j, x j≤D := by
    intro j
    dsimp [x]
    rw [div_le_iff₀ (pow_pos hC0 _)]
    apply (hcap j).trans
    apply mul_le_mul_of_nonneg_left _ hD
    rw [show j+2=(j+1)+1 by omega,pow_succ]
    exact le_mul_of_one_le_right (mul_nonneg (pow_nonneg hC0.le _) hC0.le) hC
  have hs : ∀ j, (x j)^2-1≤x (j+1) := by
    intro j
    have H := normalized_square_step (one_le_pow₀ hC : 1≤C^(j+1)) hC (hstep j)
    simpa only [x,show j+2=(j+1)+1 by omega,show j+1+2=((j+1)+1)+1 by omega,pow_succ] using H
  have H := square_recursion_bounded hb hs
  dsimp [x] at H
  simpa only [Nat.zero_add] using (div_le_iff₀ (pow_pos hC0 2)).mp H

theorem geometric_screening_recursion_all {g : ℕ → ℝ} {C D : ℝ}
    (hC : 1≤C) (hD : 0≤D)
    (hcap : ∀ j, g j≤D*C^(j+1))
    (hstep : ∀ j, (g j)^2≤C^(j+1)*(1+g (j+1))) (l : ℕ) :
    g l≤2*C^(l+2) := by
  let x : ℕ → ℝ := fun j => g j/C^(j+2)
  have hC0 : 0<C := by linarith
  have hb : ∀ j, x j≤D := by
    intro j
    dsimp [x]
    rw [div_le_iff₀ (pow_pos hC0 _)]
    apply (hcap j).trans
    apply mul_le_mul_of_nonneg_left _ hD
    exact pow_le_pow_right₀ hC (by omega)
  have hs : ∀ j, (x j)^2-1≤x (j+1) := by
    intro j
    have H := normalized_square_step (one_le_pow₀ hC : 1≤C^(j+1)) hC (hstep j)
    simpa only [x,show j+2=(j+1)+1 by omega,show j+1+2=((j+1)+1)+1 by omega,pow_succ] using H
  have H := square_recursion_bounded (x:=fun j => x (l+j))
    (fun j => hb (l+j)) (fun j => by simpa only [Nat.add_assoc] using hs (l+j))
  simp only [Nat.add_zero,x] at H
  exact (div_le_iff₀ (pow_pos hC0 _)).mp H

theorem deterministic_screening_tree {α : ℕ → Type*} (f : (j : ℕ) → α j → ℝ)
    {C D : ℝ} (hC : 1≤C) (hD : 0≤D)
    (hcap : ∀ j x, f j x≤D*C^(j+1))
    (hstep : ∀ j x, ∃ y : α (j+1), (f j x)^2≤C^(j+1)*(1+f (j+1) y))
    (x0 : α 0) : f 0 x0≤2*C^2 := by
  let t : (j : ℕ) → α j := fun j => Nat.rec x0 (fun j x => Classical.choose (hstep j x)) j
  have ht : ∀ j, (f j (t j))^2≤C^(j+1)*(1+f (j+1) (t (j+1))) := by
    intro j
    exact Classical.choose_spec (hstep j (t j))
  exact geometric_screening_recursion hC hD (fun j => hcap j (t j)) ht

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

theorem atomicRawSup_uniform {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2) (j : ℕ) :
    atomicRawSup S ψ a (screenFieldUnit δ P a) j ≤ 2*atomicRecursionC^(j+2) := by
  have hw := screenFieldUnit_pos (δ:=δ) hP ha
  have hC : 1≤atomicRecursionC := le_trans (by norm_num) atomicRecursionC_ge_four
  apply geometric_screening_recursion_all hC
    (div_nonneg (totalCharge_nonneg S) (show 0≤100000*a*screenFieldUnit δ P a by positivity))
    _ (atomicRawSup_recursion S hatom ψ hm hE hstate hδ hP ha hc) j
  intro l
  apply (atomicRawSup_cap S hatom ψ hm ha hw l).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (totalCharge_nonneg S) (by positivity))
  exact (pow_le_pow_left₀ (by norm_num) atomicRecursionC_ge_four l).trans
    (pow_le_pow_right₀ hC (by omega))

theorem AtomicCutHistory.positive_field {J n j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ P a : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0≤δ) (hP : 1≤P) (ha : 0<a)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2)
    (T : AtomicCutHistory S ψ j) (hT : ∀ i, AtomicScaleWindow a (4^j) (T.target i))
    (y : Space) (hy : AtomicScaleWindow a (4^j) y) :
    Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
      2*atomicRecursionC^(j+2)*screenFieldUnit δ P a := by
  have hw := screenFieldUnit_pos (δ:=δ) hP ha
  have H : Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y))/screenFieldUnit δ P a ≤
      atomicRawSup S ψ a (screenFieldUnit δ P a) j :=
    le_csSup (atomicRawValues_bdd S hatom ψ hm ha hw j)
      (Set.mem_insert_of_mem _ ⟨j,le_rfl,T,hT,y,hy,rfl⟩)
  exact (div_le_iff₀ hw).mp (H.trans (atomicRawSup_uniform S hatom ψ hm hE hstate hδ hP ha hc j))

theorem AtomicCutHistory.positive_field_actual_counts {J n j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hm : mass ψ=1)
    {E δ a : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0≤δ) (ha : 0<a)
    (T : AtomicCutHistory S ψ j) (hT : ∀ i, AtomicScaleWindow a (4^j) (T.target i))
    (y : Space) (hy : AtomicScaleWindow a (4^j) y) :
    Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
      2*atomicRecursionC^(j+2)*screenFieldUnit δ (screenCountParameter ψ δ) a :=
  T.positive_field S hatom ψ hm hE hstate hδ (screenCountParameter_ge_one ψ δ) ha
    (fun _ hy => screenCountParameter_controls ψ hm δ hy) hT y hy

end Coulomb

end

end OAI
