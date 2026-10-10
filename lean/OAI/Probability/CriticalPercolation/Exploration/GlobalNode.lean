import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedCauchy
import OAI.Probability.CriticalPercolation.Modular.InputMass

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy FiniteProduct

variable {E I : Type*} [Fintype E] [Fintype I]

abbrev GlobalNode (t : I → QueryTree E) := (o : Order I) × (combined t o.val).bare.Node

noncomputable abbrev globalTag (t : I → QueryTree E) (x : GlobalNode t) : LocalNode t :=
  (combined t x.1.val).nodeLabel x.2

omit [Fintype E] in
lemma pooled_weighted_sum (t : I → QueryTree E) (w : Order I → I → ℝ)
    (f : GlobalNode t → ℝ) (a : LocalNode t) :
    (∑ x : GlobalNode t, if globalTag t x = a then w x.1 (globalTag t x).1 * f x else 0) =
      ∑ o : Order I, w o a.1 * ∑ g : (combined t o.val).bare.Node,
        if (combined t o.val).nodeLabel g = a then f ⟨o,g⟩ else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : globalTag t ⟨o,g⟩ = a
  · simp only [h, ite_eq_left]
  · simp only [h, ite_false, mul_zero]

lemma weighted_node_square_bound (t : I → QueryTree E) (p : ℝ)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (x : GlobalNode t) :
    (orderWeight x.1 (globalTag t x).1 * (combined t x.1.val).bare.inputNumerator p P x.2)^2 ≤
      (orderSquare x.1 (globalTag t x).1 * (combined t x.1.val).bare.inputMass P x.2) *
      (orderMass x.1 * (combined t x.1.val).bare.inputNumerator p P x.2 ^ 2 /
        (combined t x.1.val).bare.inputMass P x.2) := by
  let M := (combined t x.1.val).bare.inputMass P x.2
  let N := (combined t x.1.val).bare.inputNumerator p P x.2
  have hM : 0 ≤ M := inputMass_nonneg _ P hP x.2
  change (orderWeight x.1 (globalTag t x).1 * N)^2 ≤
    (orderSquare x.1 (globalTag t x).1 * M)*(orderMass x.1*N^2/M)
  rcases eq_or_lt_of_le hM with hz | hp
  · have hN : N = 0 := inputNumerator_eq_zero _ p P hP x.2 hz.symm
    simp [hN]
  · have hh := mul_le_mul_of_nonneg_right (orderWeight_sq_le x.1 (globalTag t x).1)
      (sq_nonneg N)
    calc
      _ = (orderWeight x.1 (globalTag t x).1)^2 * N^2 := by ring
      _ ≤ (orderSquare x.1 (globalTag t x).1 * orderMass x.1)*N^2 := hh
      _ = _ := by field_simp

theorem overlap_four_charge (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (p : ℝ) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4) :
    (∑ i, (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P)) ≤
      16 * ∑ o : Order I, orderMass o *
        (combined t o.val).bare.charge (fun r => (r-p)^2)
          (pushMass (combined t o.val).bare.run P) := by
  let M (x : GlobalNode t) := (combined t x.1.val).bare.inputMass P x.2
  let N (x : GlobalNode t) := (combined t x.1.val).bare.inputNumerator p P x.2
  let z (x : GlobalNode t) := orderWeight x.1 (globalTag t x).1 * N x
  let u (x : GlobalNode t) := orderSquare x.1 (globalTag t x).1 * M x
  let v (x : GlobalNode t) := orderMass x.1 * (N x)^2 / M x
  have h := pooled_two_weight_bound (globalTag t) z u v
    (fun a : LocalNode t => (t a.1).inputMass P a.2)
    (fun a : LocalNode t => (t a.1).inputNumerator p P a.2)
    (C := 16)
    (fun x => mul_nonneg (orderSquare_nonneg _ _) (inputMass_nonneg _ P hP _))
    (fun x => div_nonneg (mul_nonneg (orderMass_nonneg _) (sq_nonneg _))
      (inputMass_nonneg _ P hP _))
    (weighted_node_square_bound t p P hP)
    (fun a => inputMass_nonneg _ P hP _) (by norm_num) ?_ ?_
  · convert h using 1
    · rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      exact charge_eq_input_sum (t i) p P
    · rw [Fintype.sum_sigma]
      congr 1
      apply Finset.sum_congr rfl
      intro o _
      rw [charge_eq_input_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      dsimp [v,N,M]
      ring
  · intro a
    exact (weighted_pooled_numerator t ht p P hP hover a.1 a.2).symm.trans
      (pooled_weighted_sum t orderWeight N a).symm
  · intro a
    exact (pooled_weighted_sum t orderSquare M a).trans_le
      (weighted_pooled_mass_le t ht P hP a.1 a.2)

theorem overlap_four_entropy {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (t : I → QueryTree E) (ht : ∀ i, (t i).Valid ∅)
    (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω) (hMass : ∑ ω, P ω = 1)
    (hover : ∀ ω, 0 < P ω → ∀ e, (users t ω e).card ≤ 4) :
    (∑ i, divergence (pushMass (t i).run P) ((t i).reference p)) ≤
      16/(2*p*(1-p)) * divergence P (density (bitWeight p)) := by
  have hc := overlap_four_charge t ht p P hP hover
  have hb : 2*(∑ o : Order I, orderMass o *
      (combined t o.val).bare.charge (fun r => (r-p)^2)
        (pushMass (combined t o.val).bare.run P)) ≤ divergence P (density (bitWeight p)) := by
    calc
      _ = ∑ o : Order I, orderMass o * (2*
            (combined t o.val).bare.charge (fun r => (r-p)^2)
              (pushMass (combined t o.val).bare.run P)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro o _; ring
      _ ≤ ∑ o : Order I, orderMass o * divergence P (density (bitWeight p)) := by
        apply Finset.sum_le_sum
        intro o _
        exact mul_le_mul_of_nonneg_left
          (quadratic_bias_budget hp _ (combined_valid t o.val) P hP hMass) (orderMass_nonneg o)
      _ = _ := by rw [← Finset.sum_mul, sum_orderMass, one_mul]
  have hlocal : (∑ i, (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P)) ≤
      8 * divergence P (density (bitWeight p)) := by linarith
  calc
    _ ≤ ∑ i, (p*(1-p))⁻¹ * (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P) :=
      Finset.sum_le_sum (fun i _ => transcript_divergence_upper hp (t i) P hP hMass)
    _ = (p*(1-p))⁻¹ * ∑ i, (t i).charge (fun r => (r-p)^2) (pushMass (t i).run P) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (p*(1-p))⁻¹ * (8 * divergence P (density (bitWeight p))) :=
      mul_le_mul_of_nonneg_left hlocal (inv_nonneg.mpr (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)))
    _ = _ := by field_simp; ring

end CriticalPercolation.OrderedQuery

end
end

end OAI
