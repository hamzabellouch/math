import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.DeterminantWave

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma perm_eq_or_comp_swap_of_eq_off_two {α : Type*} [DecidableEq α]
    (p q : Equiv.Perm α) (i j : α) (_hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → p k = q k) :
    q = p ∨ q = p * Equiv.swap i j := by
  by_cases hi : p i = q i
  · left
    symm
    apply perm_eq_of_eq_off p q j
    intro k hkj
    by_cases hki : k = i
    · simpa only [hki] using hi
    · exact h k hki hkj
  · right
    have hki : q.symm (p i) ≠ i := by
      intro he
      apply hi
      simpa only [he] using (q.apply_symm_apply (p i)).symm
    have hkj : q.symm (p i) = j := by
      by_contra he
      have H : p (q.symm (p i)) = p i := (h _ hki he).trans (q.apply_symm_apply _)
      exact hki (p.injective H)
    have hji : p i = q j := by simpa only [hkj] using (q.apply_symm_apply (p i)).symm
    have hE : p = q * Equiv.swap i j := by
      apply perm_eq_of_eq_off p (q * Equiv.swap i j) j
      intro k hkj'
      by_cases hki' : k = i
      · subst k
        simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using hji
      · simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki' hkj'] using h k hki' hkj'
    rw [hE, mul_assoc, Equiv.swap_mul_self, mul_one]

lemma perm_mul_swap_ne {α : Type*} [DecidableEq α] (p : Equiv.Perm α)
    (i j : α) (hij : i ≠ j) : p * Equiv.swap i j ≠ p := by
  intro h
  have H := congrArg (fun r : Equiv.Perm α => r i) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at H
  exact hij (p.injective H).symm

lemma permutation_second_minor {α : Type*} [Fintype α] [DecidableEq α]
    (p q : Equiv.Perm α) (i j : α) (hij : i ≠ j) :
    (∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1 : ℂ) else 0) =
      (if q = p then 1 else 0) + (if q = p * Equiv.swap i j then 1 else 0) := by
  by_cases h1 : q = p
  · subst q
    simp [Ne.symm (perm_mul_swap_ne p i j hij)]
  by_cases h2 : q = p * Equiv.swap i j
  · rw [ite_eq_right h1, ite_eq_left h2, zero_add]
    apply Finset.prod_eq_one
    intro k hk
    obtain ⟨hkj,hki,_⟩ := Finset.mem_erase.mp hk |>.imp_right Finset.mem_erase.mp
    simp only [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, ite_true]
  · rw [ite_eq_right h1, ite_eq_right h2, zero_add]
    obtain ⟨k,hki,hkj,hk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ p k ≠ q k := by
      by_contra he
      have h := perm_eq_or_comp_swap_of_eq_off_two p q i j hij (fun k hki hkj => by
        by_contra hk
        exact he ⟨k,hki,hkj,hk⟩)
      exact h.elim h1 h2
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩⟩)
      (ite_eq_right hk)

lemma sign_star_mul_swap {n : ℕ} (p : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    star (((p.sign : ℤ) : ℂ)) * ((((p * Equiv.swap i j).sign : ℤ) : ℂ)) = -1 := by
  rw [map_mul, Equiv.Perm.sign_swap hij]
  simp only [Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg,
    Int.cast_one, ← mul_assoc, sign_star_mul, one_mul]

lemma pair_minor_trace {n : ℕ} (K : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        (K (p i) (p j) (q i) (q j) *
          ∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1:ℂ) else 0)) =
      K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i) := by
  simp_rw [permutation_second_minor p _ i j hij, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
      (K (p i) (p j) (q i) (q j) * (if q = p then 1 else 0))) = K (p i) (p j) (p i) (p j) := by
    rw [Finset.sum_eq_single p]
    · simp only [ite_true, mul_one, sign_star_mul, one_mul]
    · intro q _ hq
      simp only [ite_eq_right hq, mul_zero]
    · simp
  have h2 : (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
      (K (p i) (p j) (q i) (q j) * (if q = p * Equiv.swap i j then 1 else 0))) =
        -K (p i) (p j) (p j) (p i) := by
    rw [Finset.sum_eq_single (p * Equiv.swap i j)]
    · simp only [ite_true, mul_one, sign_star_mul_swap p i j hij, neg_one_mul,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · intro q _ hq
      simp only [ite_eq_right hq, mul_zero]
    · simp
  rw [h1,h2,sub_eq_add_neg]

lemma pair_trace_reindex {n : ℕ} (K : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p : Equiv.Perm (Fin n)) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i))) =
      ∑ i, ∑ j, (K i j i j - K i j j i) := by
  have he (i : Fin n) : (∑ j ∈ Finset.univ.erase i,
      (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i))) =
      ∑ j, (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i)) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [sub_self, sub_zero]
  simp_rw [he]
  have hi (i : Fin n) : (∑ j, (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i))) =
      ∑ j, (K (p i) j (p i) j - K (p i) j j (p i)) :=
    Equiv.sum_comp p (fun j => K (p i) j (p i) j - K (p i) j j (p i))
  simp_rw [hi]
  exact Equiv.sum_comp p (fun i => ∑ j, (K i j i j - K i j j i))

lemma slater_two_body_trace_algebra {n : ℕ} (K : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
      star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          K (p i) (p j) (q i) (q j) *
            ∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1:ℂ) else 0) =
      (n.factorial : ℂ) * ∑ i, ∑ j, (K i j i j - K i j j i) := by
  have hp (p : Equiv.Perm (Fin n)) :
      (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          K (p i) (p j) (q i) (q j) *
            ∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1:ℂ) else 0) =
      ∑ i, ∑ j, (K i j i j - K i j j i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
          (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        exact pair_minor_trace K p i j (Finset.mem_erase.mp hj).1.symm
      _ = _ := pair_trace_reindex K p
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def pairIndexEquiv {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j) :
    Fin 2 ≃ {k : I // k = i ∨ k = j} where
  toFun b := if b = 0 then ⟨i, Or.inl rfl⟩ else ⟨j, Or.inr rfl⟩
  invFun k := if k.1 = i then 0 else 1
  left_inv b := by fin_cases b <;> simp [Ne.symm hij]
  right_inv k := by
    rcases k with ⟨k,hk | hk⟩ <;> subst k <;> simp [Ne.symm hij]

noncomputable def pairSelectedEquiv {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) : ({k : I // k = i ∨ k = j} → A) ≃ᵐ (A × A) :=
  (MeasurableEquiv.piCongrLeft (fun _ : {k : I // k = i ∨ k = j} => A)
    (pairIndexEquiv i j hij)).symm.trans MeasurableEquiv.finTwoArrow

noncomputable def pairSplit {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) : (I → A) ≃ᵐ (A × A) × ({k : I // ¬ (k = i ∨ k = j)} → A) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => A) (fun k => k = i ∨ k = j)).trans
    ((pairSelectedEquiv i j hij).prodCongr (MeasurableEquiv.refl _))

lemma pairSplit_first {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) : ((pairSplit i j hij) x).1.1 = x i := by
  change x ((pairIndexEquiv i j hij) 0).1 = x i
  simp [pairIndexEquiv]

lemma pairSplit_second {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) : ((pairSplit i j hij) x).1.2 = x j := by
  change x ((pairIndexEquiv i j hij) 1).1 = x j
  simp [pairIndexEquiv]

lemma pairSplit_rest {I A : Type*} [DecidableEq I] [MeasurableSpace A]
    (i j : I) (hij : i ≠ j) (x : I → A) (k : {k : I // ¬ (k = i ∨ k = j)}) :
    ((pairSplit i j hij) x).2 k = x k := rfl

lemma pairSplit_measurePreserving {I A : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] (i j : I) (hij : i ≠ j) :
    MeasurePreserving (pairSplit (A := A) i j hij) (Measure.pi fun _ => μ)
      ((μ.prod μ).prod (Measure.pi fun _ => μ)) := by
  have hp : MeasurePreserving (pairSelectedEquiv (A := A) i j hij)
      (Measure.pi fun _ => μ) (μ.prod μ) :=
    (measurePreserving_finTwoArrow μ).comp
      ((measurePreserving_piCongrLeft (fun _ => μ) (pairIndexEquiv i j hij)).symm)
  exact (hp.prod (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ => μ) (fun k => k = i ∨ k = j))

lemma prod_erase_pair {I : Type*} [Fintype I] [DecidableEq I] (i j : I) (hij : i ≠ j)
    (f : I → ℂ) :
    (∏ k, f k) = (f i * f j) * ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) f (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
    ← mul_assoc]
  congr 1
  exact Finset.prod_subtype ((Finset.univ.erase i).erase j) (fun k => by simp [and_comm]) f

lemma pair_weight_tensor_integrable {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] (i j : I) (hij : i ≠ j)
    (f : I → A → ℂ) (w : A → A → ℂ) (hf : ∀ k, Integrable (f k) μ)
    (hw : Integrable (fun ab : A × A => w ab.1 ab.2 * (f i ab.1 * f j ab.2)) (μ.prod μ)) :
    Integrable (fun x : I → A => w (x i) (x j) * ∏ k, f k (x k)) (Measure.pi fun _ => μ) := by
  have hR : Integrable (fun x : {k : I // ¬ (k = i ∨ k = j)} → A => ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (x k))
      (Measure.pi fun _ => μ) := Integrable.fintype_prod (fun k => hf k)
  have h := (pairSplit_measurePreserving μ i j hij).integrable_comp_of_integrable (hw.mul_prod hR)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairSplit_first, pairSplit_second, pairSplit_rest,
    prod_erase_pair i j hij]
  ring

lemma pair_weight_tensor_integral {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ] (i j : I) (hij : i ≠ j)
    (f : I → A → ℂ) (w : A → A → ℂ) :
    (∫ x : I → A, w (x i) (x j) * ∏ k, f k (x k) ∂(Measure.pi fun _ => μ)) =
      (∫ ab : A × A, w ab.1 ab.2 * (f i ab.1 * f j ab.2) ∂(μ.prod μ)) *
        ∏ k ∈ (Finset.univ.erase i).erase j, ∫ a, f k a ∂μ := by
  have he (x : I → A) : w (x i) (x j) * ∏ k, f k (x k) =
      (w ((pairSplit i j hij) x).1.1 ((pairSplit i j hij) x).1.2 *
        (f i ((pairSplit i j hij) x).1.1 * f j ((pairSplit i j hij) x).1.2)) *
          ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (((pairSplit i j hij) x).2 k) := by
    simp only [pairSplit_first, pairSplit_second, pairSplit_rest, prod_erase_pair i j hij]
    ring
  simp_rw [he]
  rw [(pairSplit_measurePreserving μ i j hij).integral_comp'
    (fun z => (w z.1.1 z.1.2 * (f i z.1.1 * f j z.1.2)) * ∏ k : {k : I // ¬ (k = i ∨ k = j)}, f k (z.2 k)),
    integral_prod_mul (fun ab : A × A => w ab.1 ab.2 * (f i ab.1 * f j ab.2))
      (fun x : {k : I // ¬ (k = i ∨ k = j)} → A => ∏ k, f k.1 (x k)),
    integral_fintype_prod_eq_prod]
  congr 1
  exact (Finset.prod_subtype ((Finset.univ.erase i).erase j) (fun k => by simp [and_comm]) (fun k => ∫ a, f k a ∂μ)).symm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
