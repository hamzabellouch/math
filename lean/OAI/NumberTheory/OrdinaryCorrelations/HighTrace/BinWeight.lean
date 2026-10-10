import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardPrimesLe

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.PivotSummation
open Finset Classical Filter

def binWeight {P : Type*} (value : P → ℕ) (H τ : ℝ)
    (D : List P → ℝ) (pre : List P) (p : P) : ℝ :=
  if H < (value p : ℝ) * D pre ∧ (value p : ℝ) * D pre ≤ τ * H
  then (value p : ℝ)⁻¹ else 0

def pathWeight {P : Type*} (value : P → ℕ) (H τ : ℝ)
    (D : List P → ℝ) : List P → List P → ℝ
  | _, [] => 1
  | pre, p :: tail => binWeight value H τ D pre p *
      pathWeight value H τ D (pre ++ [p]) tail

lemma binWeight_nonneg {P : Type*} (value : P → ℕ) (H τ : ℝ)
    (D : List P → ℝ) (pre : List P) (p : P) :
    0 ≤ binWeight value H τ D pre p := by
  unfold binWeight
  split_ifs <;> positivity

lemma pathWeight_nonneg {P : Type*} (value : P → ℕ) (H τ : ℝ)
    (D : List P → ℝ) (pre tail : List P) :
    0 ≤ pathWeight value H τ D pre tail := by
  induction tail generalizing pre with
  | nil => simp [pathWeight]
  | cons p tail ih => exact mul_nonneg (binWeight_nonneg ..) (ih _)

theorem triangular_sum {P : Type*} [Fintype P]
    (value : P → ℕ) (H τ : ℝ) (D : List P → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hbin : ∀ pre, ∑ p : P, binWeight value H τ D pre p ≤ K)
    (n : ℕ) (pre : List P) :
    ∑ x : Fin n → P, pathWeight value H τ D pre (List.ofFn x) ≤ K^n := by
  induction n generalizing pre with
  | zero => simp [pathWeight]
  | succ n ih =>
    have he := (Fin.consEquiv (fun _ : Fin (n+1) => P)).sum_comp
      (fun x : Fin (n+1) → P => pathWeight value H τ D pre (List.ofFn x))
    calc
      _ = ∑ z : P × (Fin n → P),
          binWeight value H τ D pre z.1 *
            pathWeight value H τ D (pre ++ [z.1]) (List.ofFn z.2) := by
        rw [← he]
        apply sum_congr rfl
        intro z hz
        simp [Fin.consEquiv,List.ofFn_succ,pathWeight]
      _ = ∑ p : P, binWeight value H τ D pre p *
          ∑ x : Fin n → P, pathWeight value H τ D (pre ++ [p]) (List.ofFn x) := by
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro p hp
        rw [mul_sum]
      _ ≤ ∑ p : P, binWeight value H τ D pre p * K^n :=
        sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (ih _) (binWeight_nonneg ..))
      _ = (∑ p : P, binWeight value H τ D pre p) * K^n := by rw [sum_mul]
      _ ≤ K * K^n := mul_le_mul_of_nonneg_right (hbin pre) (pow_nonneg hK _)
      _ = K^(n+1) := by rw [pow_succ]; ring

theorem core_pivots (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ Real.exp (B^r) < (p : ℝ)) →
      ∀ (H : ℝ) (D : List ↥s → ℝ), (∀ pre, 0 < D pre) →
      ∀ (n : ℕ) (pre : List ↥s),
      ∑ x : Fin n → ↥s, pathWeight Subtype.val H τ D pre (List.ofFn x) ≤
        (((Real.log 4 + 1) * τ) / B^r)^n := by
  filter_upwards [PrimeIntervals.uniform_prime_bin r τ hr hτ,
    eventually_ge_atTop (1 : ℝ)] with B hB hB1
  intro s hs H D hD n pre
  apply triangular_sum Subtype.val H τ D _ (by positivity)
  intro earlier
  let t : Finset ℕ := s.filter (fun (p : ℕ) => H < (p : ℝ) * D earlier ∧ (p : ℝ) * D earlier ≤ τ * H)
  have hb : ∑ p ∈ t, (p : ℝ)⁻¹ ≤ ((Real.log 4 + 1) * τ) / B^r := by
    apply hB (H / D earlier) t
    intro p hp
    obtain ⟨hp,hbin⟩ := mem_filter.mp hp
    refine ⟨(hs p hp).1,(hs p hp).2,?_,?_⟩
    · exact (div_lt_iff₀ (hD earlier)).mpr hbin.1
    · rw [← mul_div_assoc]
      exact (le_div_iff₀ (hD earlier)).mpr hbin.2
  change (∑ p : ↥s, if H < (p.val : ℝ) * D earlier ∧
    (p.val : ℝ) * D earlier ≤ τ * H then (p.val : ℝ)⁻¹ else 0) ≤ _
  rw [sum_coe_sort s (fun p : ℕ => if H < (p : ℝ) * D earlier ∧
    (p : ℝ) * D earlier ≤ τ * H then (p : ℝ)⁻¹ else 0)]
  simpa only [t,sum_filter] using hb

end OrdinaryCorrelations.PivotSummation

end

end OAI
