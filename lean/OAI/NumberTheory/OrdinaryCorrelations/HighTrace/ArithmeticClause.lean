import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BinWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EarlierTuple
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.HarmonicCongruenceBound

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical OrdinaryCorrelations.PivotSummation

inductive ArithmeticClause
  | divisor (D : ℤ)
  | linear (a c : ℤ) (r : ℕ)

namespace ArithmeticClause

def Holds (P K : ℝ) (t : ArithmeticClause) (q : ℕ) : Prop :=
  match t with
  | .divisor D => D ≠ 0 ∧ Real.log (|(D:ℝ)|+2) ≤ K ∧ (q:ℤ) ∣ D
  | .linear a c r => Nat.Prime r ∧ P ≤ (r:ℝ) ∧ ¬(r:ℤ) ∣ a ∧ (r:ℤ) ∣ a*q+c

def weight (P K : ℝ) (t : ArithmeticClause) (q : ℕ) : ℝ :=
  if t.Holds P K q then (q:ℝ)⁻¹ else 0

lemma weight_nonneg (P K : ℝ) (t : ArithmeticClause) (q : ℕ) :
    0 ≤ t.weight P K q := by unfold weight; split_ifs <;> positivity

lemma weight_sum_le (S : Finset ℕ) (P B K : ℝ)
    (hP : 0 < P) (hB : 0 ≤ B) (_ : 0 ≤ K)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B)
    (t : ArithmeticClause) :
    ∑ q ∈ S, t.weight P K q ≤ max (K/(P*Real.log 2)) ((2+B)/P) := by
  have hδ : 0 ≤ max (K/(P*Real.log 2)) ((2+B)/P) := by positivity
  cases t with
  | divisor D =>
    by_cases hD : D ≠ 0
    · by_cases hsize : Real.log (|(D:ℝ)|+2) ≤ K
      · have hb := harmonic_divisor_bound (S.filter (fun (q:ℕ) => (q:ℤ) ∣ D)) P D hP hD (by
          intro q hq
          obtain ⟨hq,hqd⟩ := mem_filter.mp hq
          exact ⟨(hS q hq).1,(hS q hq).2.1,hqd⟩)
        have he : (∑ q ∈ S, (divisor D).weight P K q) =
            ∑ q ∈ S.filter (fun (q:ℕ) => (q:ℤ) ∣ D), (q:ℝ)⁻¹ := by
          simp [weight,Holds,hD,hsize,sum_filter]
        rw [he]
        exact (hb.trans (div_le_div_of_nonneg_right hsize (by positivity))).trans (le_max_left _ _)
      · simpa [weight,Holds,hsize] using hδ
    · simpa [weight,Holds,hD] using hδ
  | linear a c r =>
    by_cases hrp : Nat.Prime r
    · by_cases hr : P ≤ (r:ℝ)
      · by_cases ha : ¬(r:ℤ) ∣ a
        · have hb := harmonic_linear_bound (S.filter (fun (q:ℕ) => (r:ℤ) ∣ a*(q:ℤ)+c))
            P B r a c hP hB hr hrp ha (by
              intro q hq
              obtain ⟨hq,hqd⟩ := mem_filter.mp hq
              exact ⟨(hS q hq).2.1,(hS q hq).2.2,hqd⟩)
          have he : (∑ q ∈ S, (linear a c r).weight P K q) =
              ∑ q ∈ S.filter (fun (q:ℕ) => (r:ℤ) ∣ a*(q:ℤ)+c), (q:ℝ)⁻¹ := by
            simp [weight,Holds,hrp,hr,ha,sum_filter]
          rw [he]
          exact hb.trans (le_max_right _ _)
        · simpa [weight,Holds,ha] using hδ
      · simpa [weight,Holds,hr] using hδ
    · simpa [weight,Holds,hrp] using hδ
end ArithmeticClause

theorem triangular_arithmetic_saving (S : Finset ℕ) (P B K : ℝ)
    (hP : 0 < P) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ P ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp B)
    (n : ℕ) (T : ∀ i : Fin n, (Fin i.val → S) → ArithmeticClause) :
    (∑ x : Fin n → S, ∏ i, (T i (earlierTuple x i)).weight P K (x i).val) ≤
      (max (K/(P*Real.log 2)) ((2+B)/P))^n := by
  simpa only [prod_const,card_univ,Fintype.card_fin] using
    triangular_product_sum n
      (fun i pre q => (T i pre).weight P K q.val)
      (fun _ => max (K/(P*Real.log 2)) ((2+B)/P))
      (fun i pre q => ArithmeticClause.weight_nonneg P K _ _)
      (by intro i; positivity) (by
        intro i pre
        rw [sum_coe_sort S (fun q => (T i pre).weight P K q)]
        exact ArithmeticClause.weight_sum_le S P B K hP hB hK hS (T i pre))

end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
