import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BinWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Nonempty
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CoreTupleBins

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.PivotSummation
open OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

def slotWeight (S : PrimeSystem) (c : Prop) (p : S.Index) : ℝ :=
  if c ↔ S.IsCore p then (p.val : ℝ)⁻¹ else 0

lemma slotWeight_nonneg (S : PrimeSystem) (c : Prop) (p : S.Index) :
    0 ≤ slotWeight S c p := by unfold slotWeight; split_ifs <;> positivity

lemma slotWeight_sum (S : PrimeSystem) (c : Prop) :
    (∑ p : S.Index, slotWeight S c p) =
    if c then S.harmonicCore else S.harmonicCenter := by
  by_cases hc : c
  · simp only [slotWeight,hc,true_iff,ite_true]
    have he := Finset.sum_subtype (F := inferInstance) (p := S.IsCore) (univ.filter S.IsCore)
      (by simp) (fun p : S.Index => (p.val : ℝ)⁻¹)
    simpa only [sum_filter,harmonicCore] using he
  · simp only [slotWeight,hc,false_iff,ite_false]
    have he := Finset.sum_subtype (F := inferInstance) (p := fun p => ¬S.IsCore p) (univ.filter (fun p => ¬S.IsCore p))
      (by simp) (fun p : S.Index => (p.val : ℝ)⁻¹)
    simpa only [sum_filter,harmonicCenter] using he

theorem core_system_tuple_bins (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (S : PrimeSystem),
      (∀ p ∈ S.core, Real.exp (B^r) < (p : ℝ)) →
      ∀ (n : ℕ) (H : ℝ) (D : ∀ i : Fin n, (Fin i.val → S.Index) → ℝ),
      (∀ i pre, 0 < D i pre) →
      (∑ x : Fin n → S.Index,
        ∏ i, if (x i).val ∈ S.core ∧ H < (x i).val * D i (earlierTuple x i) ∧
          (x i).val * D i (earlierTuple x i) ≤ τ * H then ((x i).val : ℝ)⁻¹ else 0) ≤
      (((Real.log 4 + 1) * τ) / B^r)^n := by
  filter_upwards [PrimeIntervals.uniform_prime_bin r τ hr hτ,
    eventually_ge_atTop (1 : ℝ)] with B hB hB1
  intro S hS n H D hD
  have hk : 0 ≤ ((Real.log 4 + 1)*τ)/B^r := by positivity
  simpa only [prod_const,card_univ,Fintype.card_fin] using
    triangular_product_sum (P := S.Index) n
      (fun i pre p => if p.val ∈ S.core ∧ H < p.val *D i pre ∧ p.val *D i pre ≤ τ*H
        then (p.val : ℝ)⁻¹ else 0) (fun _ => ((Real.log 4+1)*τ)/B^r)
      (by intro i pre p; split_ifs <;> positivity) (fun _ => hk) (by
        intro i pre
        let t := S.primes.filter (fun p => p ∈ S.core ∧ H < (p : ℝ)*D i pre ∧
          (p : ℝ)*D i pre ≤ τ*H)
        have hb : (∑ p ∈ t, (p : ℝ)⁻¹) ≤ ((Real.log 4+1)*τ)/B^r := by
          apply hB (H / D i pre) t
          intro p hp
          obtain ⟨hp,hpc,hbin⟩ := mem_filter.mp hp
          refine ⟨S.prime_mem p hp,hS p hpc,?_,?_⟩
          · exact (div_lt_iff₀ (hD i pre)).mpr hbin.1
          · rw [← mul_div_assoc]
            exact (le_div_iff₀ (hD i pre)).mpr hbin.2
        rw [sum_coe_sort S.primes (fun p : ℕ => if p ∈ S.core ∧
          H < (p : ℝ)*D i pre ∧ (p : ℝ)*D i pre ≤ τ*H then (p : ℝ)⁻¹ else 0)]
        simpa only [t,sum_filter] using hb)

variable {S : PrimeSystem} {h ℓ : ℕ} {w : ClosedLine h ℓ}

theorem shape_system_bins (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (S : PrimeSystem),
      (∀ p ∈ S.core, Real.exp (B^r) < (p : ℝ)) →
      ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ),
      ∀ (n : ℕ) (Q : Fin n → Shape w), StrictMono (fun i => (Q i).topEdge) →
      ∀ (H : ℝ) (C : Fin n → ℝ), (∀ i, 0 < C i) →
      (∑ x : Fin n → S.Index,
        ∏ i, if S.IsCore (x i) ∧
          H < C i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then ((x j).val : ℝ) else 1) ∧
          C i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then ((x j).val : ℝ) else 1) ≤ τ*H
          then ((x i).val : ℝ)⁻¹ else 0) ≤ (((Real.log 4+1)*τ)/B^r)^n := by
  filter_upwards [core_system_tuple_bins r τ hr hτ] with B hB
  intro S hs h ℓ w n Q hQ H C hC
  let D : ∀ i : Fin n, (Fin i.val → S.Index) → ℝ := fun i pre =>
    C i * ∏ j : Fin i.val, if (Q i).topEdge ∈
      (Q ⟨j.val,lt_trans j.isLt i.isLt⟩).edges.val then ((pre j).val : ℝ) else 1
  have hD : ∀ i pre, 0 < D i pre := by
    intro i pre
    apply mul_pos (hC i)
    apply prod_pos
    intro j hj
    split_ifs
    · exact_mod_cast (S.prime_mem (pre j).val (pre j).property).pos
    · exact zero_lt_one
  have he (x : Fin n → S.Index) (i : Fin n) :
      C i * ∏ j, (if (Q i).topEdge ∈ (Q j).edges.val then ((x j).val : ℝ) else 1) =
      (x i).val *D i (earlierTuple x i) := by
    rw [selected_prime_product Q hQ (fun j => ((x j).val : ℝ)) i, earlier_product i]
    dsimp only [D,earlierTuple]
    ring
  simp_rw [he]
  refine le_trans ?_ (hB S hs n H D hD)
  apply le_of_eq
  apply sum_congr rfl
  intro x hx
  apply prod_congr rfl
  intro i hi
  by_cases hc : S.IsCore (x i)
  · have hc' : (x i).val ∈ S.core := hc
    simp only [hc,hc']
  · have hc' : (x i).val ∉ S.core := hc
    simp only [hc,hc']

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
