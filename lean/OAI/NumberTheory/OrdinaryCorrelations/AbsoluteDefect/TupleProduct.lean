import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Phase

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryPrimeDirichletMoments
open OrdinaryDirichletMeanSquare
open Finset

def tupleProduct {P : Finset ℕ} {k : ℕ} (v : Fin k → P) : ℕ := ∏ i, (v i : ℕ)

def tupleCoefficient {P : Finset ℕ} {k : ℕ} (a : ℕ → ℂ) (v : Fin k → P) : ℂ :=
  ∏ i, a (v i)

def productSupport (P : Finset ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact univ.image (tupleProduct (P := P) (k := k))

def coefficient (P : Finset ℕ) (k : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ v ∈ univ.filter (fun v : Fin k → P => tupleProduct v = n), tupleCoefficient a v

lemma prime_lists_perm {v w : List ℕ} (hv : ∀ p ∈ v, Nat.Prime p)
    (hw : ∀ p ∈ w, Nat.Prime p) (hprod : v.prod = w.prod) : v.Perm w := by
  apply Multiset.coe_eq_coe.mp
  have h₁ := Nat.factors_multiset_prod_of_irreducible (s := (v : Multiset ℕ))
    (fun p hp => Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp (hv p hp)))
  have h₂ := Nat.factors_multiset_prod_of_irreducible (s := (w : Multiset ℕ))
    (fun p hp => Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp (hw p hp)))
  simp only [Multiset.prod_coe] at h₁ h₂
  rw [hprod] at h₁
  exact h₁.symm.trans h₂

lemma tuple_list_injective {P : Finset ℕ} {k : ℕ} :
    Function.Injective (fun v : Fin k → P => List.ofFn (fun i => (v i : ℕ))) := by
  intro v w h
  have hfun := List.ofFn_injective h
  funext i
  apply Subtype.ext
  exact congrFun hfun i

lemma prime_fiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (k n : ℕ) :
    (univ.filter (fun v : Fin k → P => tupleProduct v = n)).card ≤ k.factorial := by
  classical
  let S := univ.filter (fun v : Fin k → P => tupleProduct v = n)
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    have hvprod : tupleProduct v = n := (mem_filter.mp hv).2
    let l : List ℕ := List.ofFn (fun i => (v i : ℕ))
    have hp (w : Fin k → P) : ∀ p ∈ List.ofFn (fun i => (w i : ℕ)), Nat.Prime p := by
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hP _ (w i).property
    have hsub : S.image (fun w => List.ofFn (fun i => (w i : ℕ))) ⊆ l.permutations.toFinset := by
      intro l' hmem
      obtain ⟨w, htuple, rfl⟩ := mem_image.mp hmem
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      apply prime_lists_perm (hp w) (hp v)
      simp only [List.prod_ofFn]
      change tupleProduct w = tupleProduct v
      exact (mem_filter.mp htuple).2.trans hvprod.symm
    calc
      _ = (S.image (fun w => List.ofFn (fun i => (w i : ℕ)))).card :=
        (card_image_of_injective S tuple_list_injective).symm
      _ ≤ l.permutations.toFinset.card := card_le_card hsub
      _ ≤ l.permutations.length := List.toFinset_card_le _
      _ = k.factorial := by simp [l, List.length_permutations]
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ _
    simp [he]

lemma tuple_phase {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) {k : ℕ}
    (v : Fin k → P) (x : ℝ) :
    ∏ i, phase (Real.log (v i : ℕ)) x = phase (Real.log (tupleProduct v)) x := by
  unfold phase tupleProduct
  rw [Nat.cast_prod, Real.log_prod (fun i hi => by exact_mod_cast (hP _ (v i).property).ne_zero)]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]

lemma polynomial_power (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a : ℕ → ℂ) (k : ℕ) (x : ℝ) :
    (polynomial P a (fun p => Real.log p) x)^k =
      polynomial (productSupport P k) (coefficient P k a) (fun n => Real.log n) x := by
  classical
  have he : polynomial P a (fun p => Real.log p) x =
      ∑ p : P, a p * phase (Real.log (p : ℕ)) x := by
    exact (Finset.sum_coe_sort P (fun p => a p * phase (Real.log p) x)).symm
  rw [he, Fintype.sum_pow]
  have ht (v : Fin k → P) : (∏ i, a (v i) * phase (Real.log (v i : ℕ)) x) =
      tupleCoefficient a v * phase (Real.log (tupleProduct v)) x := by
    rw [Finset.prod_mul_distrib, tuple_phase hP]
    rfl
  simp_rw [ht]
  symm
  unfold polynomial coefficient
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ n ∈ productSupport P k,
        ∑ v ∈ univ.filter (fun v : Fin k → P => tupleProduct v = n),
          tupleCoefficient a v * phase (Real.log (tupleProduct v)) x := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun v hv => mem_image.mpr ⟨v, mem_univ _, rfl⟩) _

lemma coefficient_energy (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a : ℕ → ℂ) (k : ℕ) :
    ∑ n ∈ productSupport P k, ‖coefficient P k a n‖^2 ≤
      (k.factorial : ℝ) * (∑ p ∈ P, ‖a p‖^2)^k := by
  classical
  have hb (n : ℕ) : ‖coefficient P k a n‖^2 ≤
      (k.factorial : ℝ) * ∑ v ∈ univ.filter (fun v : Fin k → P => tupleProduct v = n),
        ‖tupleCoefficient a v‖^2 := by
    unfold coefficient
    calc
      _ ≤ (∑ v ∈ univ.filter (fun v : Fin k → P => tupleProduct v = n),
          ‖tupleCoefficient a v‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
      _ ≤ ((univ.filter (fun v : Fin k → P => tupleProduct v = n)).card : ℝ) *
          ∑ v ∈ univ.filter (fun v : Fin k → P => tupleProduct v = n),
            ‖tupleCoefficient a v‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast prime_fiber_card P hP k n)
          (sum_nonneg fun v hv => sq_nonneg _)
  calc
    _ ≤ ∑ n ∈ productSupport P k, (k.factorial : ℝ) *
        ∑ v ∈ univ.filter (fun v : Fin k → P => tupleProduct v = n),
          ‖tupleCoefficient a v‖^2 := sum_le_sum fun n hn => hb n
    _ = (k.factorial : ℝ) * ∑ v : Fin k → P, ‖tupleCoefficient a v‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun v hv => mem_image.mpr ⟨v, mem_univ _, rfl⟩) _
    _ = _ := by
      congr 1
      simp only [tupleCoefficient, norm_prod, ← Finset.prod_pow]
      rw [← Fintype.sum_pow (fun p : P => ‖a p‖^2) k]
      congr 1
      exact Finset.sum_coe_sort P (fun p => ‖a p‖^2)

lemma product_support_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (k : ℕ) {Q : ℝ} (hQ : 0 < Q) (hPQ : ∀ p ∈ P, (p : ℝ) ≤ Q) :
    ∀ n ∈ productSupport P k, 0 < (n : ℝ) ∧ (n : ℝ) ≤ Q^k := by
  intro n hn
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
  rw [tupleProduct, Nat.cast_prod]
  constructor
  · exact prod_pos fun i hi => by exact_mod_cast (hP _ (v i).property).pos
  · have hscaled : (∏ index : Fin k, ((v index : ℕ) : ℝ) / Q) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => div_nonneg (Nat.cast_nonneg _) hQ.le)
        (fun index _ => (div_le_one hQ).mpr (hPQ _ (v index).property))
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hscaled
    exact (div_le_one (pow_pos hQ k)).mp hscaled

theorem prime_high_moment (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (a : ℕ → ℂ) (k : ℕ) {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T)
    (hPQ : ∀ p ∈ P, (p : ℝ) ≤ Q) :
    (∫ x : ℝ in Set.Icc (-T) T, ‖polynomial P a (fun p => Real.log p) x‖^(2*k)) ≤
      4 * Real.exp (1+1/4) * gaussianConstant * (T+Q^k) *
        (k.factorial : ℝ) * (∑ p ∈ P, ‖a p‖^2)^k := by
  have he (x : ℝ) : ‖polynomial P a (fun p => Real.log p) x‖^(2*k) =
      ‖polynomial (productSupport P k) (coefficient P k a) (fun n => Real.log n) x‖^2 := by
    rw [← polynomial_power P hP a k x, norm_pow, ← pow_mul]
    congr 1
    omega
  simp_rw [he]
  apply (logarithmic_interval_energy (productSupport P k) (coefficient P k a)
    (pow_pos hQ k) hT (product_support_bounds P hP k hQ hPQ)).trans
  have hc : 0 ≤ 4 * Real.exp (1+1/4) * gaussianConstant * (T+Q^k) := by
    have hg : 0 ≤ gaussianConstant := norm_nonneg _
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (coefficient_energy P hP a k) hc

end OrdinaryPrimeDirichletMoments

end

end OAI
