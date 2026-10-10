import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Jacobsthal.Probability.UniformMoment

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

private lemma hasSum_mul_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ y, 0 ≤ g y) :
    HasSum (fun s : α × β => f s.1 * g s.2) (a * b) :=
  HasSum.mul hf hg (Summable.mul_of_nonneg hf.summable hg.summable hfn hgn)

theorem hasSum_fin_product {α : Type*} {n : ℕ} (w : Fin n → α → ℝ)
    (a : Fin n → ℝ) (hw : ∀ i x, 0 ≤ w i x) (hs : ∀ i, HasSum (w i) (a i)) :
    HasSum (fun s : Fin n → α => ∏ i, w i (s i)) (∏ i, a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht : HasSum (fun s : Fin n → α => ∏ i : Fin n, w i.succ (s i))
        (∏ i : Fin n, a i.succ) :=
      ih (fun i => w i.succ) (fun i => a i.succ)
      (fun i => hw i.succ) (fun i => hs i.succ)
    have hn : ∀ s : Fin n → α, 0 ≤ ∏ i, w i.succ (s i) := by
      intro s; exact Finset.prod_nonneg (fun i _ => hw i.succ (s i))
    have hprod : HasSum (fun s : α × (Fin n → α) =>
        w 0 s.1 * ∏ i : Fin n, w i.succ (s.2 i)) (a 0 * ∏ i : Fin n, a i.succ) :=
      hasSum_mul_nonneg (f := w 0)
        (g := fun s : Fin n → α => ∏ i : Fin n, w i.succ (s i))
        (a := a 0) (b := ∏ i : Fin n, a i.succ) (hs 0) ht (hw 0) hn
    apply (Fin.consEquiv (fun _ : Fin (n+1) => α)).hasSum_iff.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hprod

theorem hasSum_finite_product {ι α : Type*} [Fintype ι]
    (w : ι → α → ℝ) (a : ι → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    (hs : ∀ i, HasSum (w i) (a i)) :
    HasSum (fun s : ι → α => ∏ i, w i (s i)) (∏ i, a i) := by
  let e := (Fintype.equivFin ι).symm
  have h := hasSum_fin_product (fun i => w (e i)) (fun i => a (e i))
    (fun i => hw (e i)) (fun i => hs (e i))
  rw [e.prod_comp a] at h
  apply (Equiv.piCongrLeft (fun _ : ι => α) e).hasSum_iff.mp
  apply h.congr_fun
  intro s
  dsimp only [Function.comp_def]
  rw [← e.prod_comp]
  congr 1
  funext i
  simp [Equiv.piCongrLeft]

theorem product_coordinate_hasSum {ι α : Type*} [Fintype ι]
    (w : ι → α → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    (hs : ∀ i, HasSum (w i) 1) (j : ι) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) {b : ℝ} (hb : HasSum (fun x => w j x * f x) b) :
    HasSum (fun s : ι → α => (∏ i, w i (s i)) * f (s j)) b := by
  classical
  have h := hasSum_finite_product
    (fun i x => w i x * if i = j then f x else 1)
    (fun i => if i = j then b else 1)
    (by intro i x; exact mul_nonneg (hw i x) (by split_ifs; exact hf x; norm_num))
    (by intro i; by_cases hij : i = j
        · subst i; simpa only [ite_true] using hb
        · simpa only [ite_eq_right hij, mul_one] using hs i)
  simpa only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ite_true] using h

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

abbrev Outcomes (E : Finset ℕ) := E → Sample
noncomputable def productMass (E : Finset ℕ) (s : Outcomes E) : ℝ :=
  ∏ p : E, jointMass (p : ℝ) (s p)
noncomputable def excessLog (E : Finset ℕ) (s : Outcomes E) : ℝ :=
  ∑ p : E, ((upperExponent (s p) - lowerExponent (s p) : ℕ) : ℝ) * Real.log (p : ℝ)
noncomputable def eventMass (E : Finset ℕ) (A : Outcomes E → Prop) : ℝ :=
  ∑' s : Outcomes E, if A s then productMass E s else 0

variable (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p)
include hE

lemma productMass_nonneg (s : Outcomes E) : 0 ≤ productMass E s := by
  apply Finset.prod_nonneg
  intro p _
  exact jointMass_nonneg (by exact_mod_cast hE p p.property) (s p)

theorem productMass_hasSum : HasSum (productMass E) 1 := by
  have h := hasSum_finite_product (fun p : E => jointMass (p : ℝ)) (fun _ => (1 : ℝ))
    (fun p => jointMass_nonneg (by exact_mod_cast hE p p.property))
    (fun p => jointMass_hasSum (by exact_mod_cast hE p p.property))
  change HasSum (fun s : E → Sample => ∏ p : E, jointMass (p : ℝ) (s p)) 1
  simpa only [Finset.prod_const_one] using h

lemma product_event_summable (A : Outcomes E → Prop) :
    Summable (fun s => if A s then productMass E s else 0) := by
  apply (productMass_hasSum E hE).summable.of_nonneg_of_le
  · intro s; split_ifs <;> simp_all only [le_refl, productMass_nonneg E hE]
  · intro s; split_ifs <;> simp_all only [le_refl, productMass_nonneg E hE]

lemma excessLog_nonneg (s : Outcomes E) : 0 ≤ excessLog E s := by
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (hE p p.property).trans' (by omega : 1 ≤ 2)))

theorem product_excess_hasSum :
    HasSum (fun s => productMass E s * excessLog E s)
      (∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ) - 1)^2) := by
  have hlocal (p : E) : HasSum (fun s : Outcomes E => productMass E s *
      (((upperExponent (s p) - lowerExponent (s p) : ℕ) : ℝ) * Real.log (p : ℝ)))
      (Real.log (p : ℝ) / ((p : ℝ)-1)^2) := by
    apply product_coordinate_hasSum (fun q : E => jointMass (q : ℝ))
      (fun q => jointMass_nonneg (by exact_mod_cast hE q q.property))
      (fun q => jointMass_hasSum (by exact_mod_cast hE q q.property)) p
      (fun s => (((upperExponent s - lowerExponent s : ℕ) : ℝ) * Real.log (p : ℝ)))
    · intro s
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (hE p p.property).trans' (by omega : 1 ≤ 2)))
    · have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hE p p.property
      rw [← expected_log_excess hp]
      simpa only [mul_assoc] using (log_excess_summable hp).hasSum
  have h := hasSum_sum (s := Finset.univ) (fun p _ => hlocal p)
  have he : (∑ p : E, Real.log (p : ℝ) / ((p : ℝ)-1)^2) =
      ∑ p ∈ E, Real.log (p : ℝ) / ((p : ℝ)-1)^2 := by
    exact Finset.sum_attach E (fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ)-1)^2)
  rw [he] at h
  convert h using 1
  funext s
  exact Finset.mul_sum _ _ _

theorem product_excess_mean_le :
    (∑' s : Outcomes E, productMass E s * excessLog E s) ≤ uniformMomentBound := by
  rw [(product_excess_hasSum E hE).tsum_eq]
  exact finite_log_moment_le E

theorem excess_tail_le {t : ℝ} (ht : 0 < t) :
    eventMass E (fun s => t < excessLog E s) ≤ uniformMomentBound / t := by
  apply (le_div_iff₀ ht).mpr
  rw [eventMass, ← tsum_mul_right]
  apply le_trans _ (product_excess_mean_le E hE)
  apply Summable.tsum_le_tsum
  · intro s
    by_cases h : t < excessLog E s
    · simp only [ite_eq_left h]
      exact mul_le_mul_of_nonneg_left h.le (productMass_nonneg E hE s)
    · simp only [ite_eq_right h, zero_mul]
      exact mul_nonneg (productMass_nonneg E hE s) (excessLog_nonneg E hE s)
  · exact (product_event_summable E hE _).mul_right t
  · exact (product_excess_hasSum E hE).summable

end EulerWeightedLower



namespace EulerWeightedLower
attribute [local instance] Classical.propDecidable

theorem finite_product_restrict {ι α : Type*} [Fintype ι] (P : ι → Prop)
    (w : ι → α → ℝ) (hw : ∀ i x, 0 ≤ w i x) (hs : ∀ i, HasSum (w i) 1)
    (A : ({i // P i} → α) → Prop) :
    (∑' s : ι → α, if A (fun i => s i) then ∏ i, w i (s i) else 0) =
      ∑' s : {i // P i} → α, if A s then ∏ i : {i // P i}, w i (s i) else 0 := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => α)
  have hsub := hasSum_finite_product (fun i : {i // P i} => w i) (fun _ => (1 : ℝ))
    (fun i => hw i) (fun i => hs i)
  have hcomp := hasSum_finite_product (fun i : {i // ¬P i} => w i) (fun _ => (1 : ℝ))
    (fun i => hw i) (fun i => hs i)
  simp only [Finset.prod_const_one] at hsub hcomp
  have hn (s : {i // P i} → α) : 0 ≤ ∏ i : {i // P i}, w i (s i) :=
    Finset.prod_nonneg (fun i _ => hw i.val (s i))
  have hc (s : {i // ¬P i} → α) : 0 ≤ ∏ i : {i // ¬P i}, w i (s i) :=
    Finset.prod_nonneg (fun i _ => hw i.val (s i))
  have hA : Summable (fun s : {i // P i} → α => if A s then ∏ i : {i // P i}, w i (s i) else 0) := by
    apply hsub.summable.of_nonneg_of_le
    · intro s; split_ifs; exact hn s; rfl
    · intro s; split_ifs; rfl; exact hn s
  have hprod := hA.mul_of_nonneg hcomp.summable
    (by intro s; dsimp only [Pi.zero_apply]; split_ifs; exact hn s; rfl) hc
  calc
    _ = ∑' z : ({i // P i} → α) × ({i // ¬P i} → α),
        (if A z.1 then ∏ i : {i // P i}, w i (z.1 i) else 0) * ∏ i : {i // ¬P i}, w i (z.2 i) := by
      rw [← e.symm.tsum_eq]
      apply tsum_congr
      intro z
      have hsplit := Fintype.prod_subtype_mul_prod_subtype P (fun i => w i (e.symm z i))
      rw [← hsplit]
      have hl (i : {i // P i}) : e.symm z i = z.1 i := by
        simp [e, Equiv.piEquivPiSubtypeProd, i.property]
      have hr (i : {i // ¬P i}) : e.symm z i = z.2 i := by
        simp [e, Equiv.piEquivPiSubtypeProd, i.property]
      simp only [hl, hr]
      by_cases hh : A z.1 <;> simp only [hh, ite_true, ite_false, zero_mul]
    _ = _ := by
      rw [hprod.tsum_prod]
      simp only [tsum_mul_left, hcomp.tsum_eq, mul_one]

end EulerWeightedLower


end Erdos970

end OAI
