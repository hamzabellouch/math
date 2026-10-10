import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardPrimesLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EarlierTuple

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.PivotSummation
open Finset Classical Filter

theorem core_tuple_bins (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ Real.exp (B^r) < (p : ℝ)) →
      ∀ (n : ℕ) (H : ℝ) (D : ∀ i : Fin n, (Fin i.val → ↥s) → ℝ),
      (∀ i pre, 0 < D i pre) →
      (∑ x : Fin n → ↥s,
        ∏ i, if H < (x i : ℝ) * D i (earlierTuple x i) ∧
          (x i : ℝ) * D i (earlierTuple x i) ≤ τ * H then (x i : ℝ)⁻¹ else 0) ≤
      (((Real.log 4 + 1) * τ) / B^r)^n := by
  filter_upwards [PrimeIntervals.uniform_prime_bin r τ hr hτ,
    eventually_ge_atTop (1 : ℝ)] with B hB hB1
  intro s hs n H D hD
  have hk : 0 ≤ ((Real.log 4 + 1)*τ)/B^r := by positivity
  simpa only [prod_const,card_univ,Fintype.card_fin] using
    triangular_product_sum (P := ↥s) n
      (fun i pre p => if H < (p : ℝ)*D i pre ∧ (p : ℝ)*D i pre ≤ τ*H
        then (p : ℝ)⁻¹ else 0) (fun _ => ((Real.log 4+1)*τ)/B^r)
      (by intro i pre p; split_ifs <;> positivity) (fun _ => hk) (by
        intro i pre
        let t := s.filter (fun (p : ℕ) => H < (p : ℝ)*D i pre ∧ (p : ℝ)*D i pre ≤ τ*H)
        have hb : (∑ p ∈ t, (p : ℝ)⁻¹) ≤ ((Real.log 4+1)*τ)/B^r := by
          apply hB (H / D i pre) t
          intro p hp
          obtain ⟨hp,hbin⟩ := mem_filter.mp hp
          refine ⟨(hs p hp).1,(hs p hp).2,?_,?_⟩
          · exact (div_lt_iff₀ (hD i pre)).mpr hbin.1
          · rw [← mul_div_assoc]
            exact (le_div_iff₀ (hD i pre)).mpr hbin.2
        rw [sum_coe_sort s (fun (p : ℕ) => if H < (p : ℝ)*D i pre ∧
          (p : ℝ)*D i pre ≤ τ*H then (p : ℝ)⁻¹ else 0)]
        simpa only [t,sum_filter] using hb)

lemma earlier_product {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∏ j ∈ univ.filter (fun j => j < i), f j) =
    ∏ j : Fin i.val, f ⟨j.val,lt_trans j.isLt i.isLt⟩ := by
  apply prod_bij (fun j hj => (⟨j.val,(mem_filter.mp hj).2⟩ : Fin i.val))
  · intro j hj; exact mem_univ _
  · intro j hj k hk h
    exact Fin.ext (congrArg (fun a : Fin i.val => a.val) h)
  · intro j hj
    refine ⟨⟨j.val,lt_trans j.isLt i.isLt⟩,mem_filter.mpr ⟨mem_univ _,j.isLt⟩,?_⟩
    rfl
  · intro j hj; rfl
end OrdinaryCorrelations.PivotSummation

end

end OAI
