import OAI.MeasureTheory.Falconer.Incidence.LoomisWhitneyCoordinates

namespace OAI

/-! # The finite weighted Loomis–Whitney induction step -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finite_root_product_raise {ι : Type*} (I : Finset ι) {n : ℕ} (hn : 0 < n)
    (b : ι → ℝ) (hb : ∀ i ∈ I, 0 ≤ b i) :
    (∏ i ∈ I, (b i)^(1/(n:ℝ)))^((n:ℝ)/((n+1:ℕ):ℝ)) =
      ∏ i ∈ I, (b i)^(1/((n+1:ℕ):ℝ)) := by
  rw [← Real.finsetProd_rpow I _ (fun i hi => Real.rpow_nonneg (hb i hi) _) _]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Real.rpow_mul (hb i hi)]
  congr 1
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

def FiniteWeightedLoomis (n : ℕ) (X : Type*) [Fintype X] : Prop :=
  ∀ f : Fin (n+1) → (Fin n → X) → ℝ, (∀ i z, 0 ≤ f i z) →
    (∑ z : Fin (n+1) → X, ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ))) ≤
      ∏ i : Fin (n+1), (∑ y : Fin n → X, f i y)^(1/(n:ℝ))

theorem finite_weighted_loomis_step {n : ℕ} (hn : 0 < n)
    (ih : FiniteWeightedLoomis n X) : FiniteWeightedLoomis (n+1) X := by
  classical
  intro f hf
  let g : Fin (n+1) → (Fin n → X) → ℝ := fun i y => ∑ x : X, f i.succ (Fin.cons x y)
  have hg : ∀ i y, 0 ≤ g i y := fun i y => Finset.sum_nonneg (fun x _ => hf _ _)
  let H : (Fin (n+1) → X) → ℝ := fun y => ∏ i : Fin (n+1), (g i (eraseFinCoordinate i y))^(1/(n:ℝ))
  have hH : ∀ y, 0 ≤ H y := fun y => Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hg _ _) _)
  let p : ℝ := 1/((n+1:ℕ):ℝ)
  let q : ℝ := (n:ℝ)/((n+1:ℕ):ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hh : (∑ y, H y) ≤ ∏ i : Fin (n+1), (∑ z, g i z)^(1/(n:ℝ)) := ih g hg
  have hfirst :
      (∑ z : Fin (n+2) → X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i z))^p) ≤
        ∑ y : Fin (n+1) → X, (f 0 y)^p*(H y)^q := by
    rw [sum_tuple_cons,Finset.sum_comm]
    apply Finset.sum_le_sum
    intro y _
    have he : (∑ x : X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i (Fin.cons x y)))^p) =
        (f 0 y)^p*(∑ x : X, ∏ i : Fin (n+1), (f i.succ (Fin.cons x (eraseFinCoordinate i y)))^p) := by
      simp only [Fin.prod_univ_succ,remove_coordinate_cons_zero,remove_coordinate_cons_succ,
        Finset.mul_sum]
    rw [he]
    have hc := finite_holder_equal (Finset.univ : Finset (Fin (n+1)))
      (Finset.univ : Finset X) (by simp)
      (fun i x => f i.succ (Fin.cons x (eraseFinCoordinate i y))) (fun i _ x _ => hf _ _)
    have hr : (∏ i : Fin (n+1), (g i (eraseFinCoordinate i y))^p) = (H y)^q :=
      (finite_root_product_raise Finset.univ hn _ (fun i _ => hg _ _)).symm
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hf _ _) _)
    rw [← hr]
    simpa only [Finset.card_univ,Fintype.card_fin,p,g] using hc
  have houter := finite_holder_two_successor (n := n) (Finset.univ : Finset (Fin (n+1) → X))
    (f 0) H (fun y _ => hf _ _) (fun y _ => hH y)
  have hraise := Real.rpow_le_rpow (Finset.sum_nonneg (fun y _ => hH y)) hh hq
  have hgSum (i : Fin (n+1)) : (∑ z : Fin n → X, g i z) = ∑ y : Fin (n+1) → X, f i.succ y := by
    rw [sum_tuple_cons]
    exact Finset.sum_comm
  have hraise' : (∑ y, H y)^q ≤ ∏ i : Fin (n+1), (∑ y, f i.succ y)^p := by
    apply hraise.trans_eq
    rw [finite_root_product_raise Finset.univ hn _ (fun i _ => Finset.sum_nonneg (fun y _ => hg _ _))]
    apply Finset.prod_congr rfl
    intro i _
    rw [hgSum]
  change (∑ z : Fin (n+2) → X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i z))^p) ≤
    ∏ i : Fin (n+2), (∑ y : Fin (n+1) → X, f i y)^p
  apply hfirst.trans
  apply houter.trans
  rw [Fin.prod_univ_succ]
  exact mul_le_mul_of_nonneg_left hraise' (Real.rpow_nonneg (Finset.sum_nonneg (fun y _ => hf _ _)) _)

end Falconer

end OAI
