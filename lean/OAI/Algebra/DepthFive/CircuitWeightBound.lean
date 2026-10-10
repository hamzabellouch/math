import OAI.Algebra.DepthFive.HighDegreeWeights
import OAI.Algebra.DepthFive.CircuitProductBound

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

/-- The numerical parameter estimates needed by the circuit upper rank bound. -/
structure WeightParameters (n : ℕ) (s q : ℝ) : Prop where
  large : 64 ≤ n
  s_pos : 0 < s
  s_lower : Real.sqrt n / 2 ≤ s
  s_upper : s ≤ Real.sqrt n
  q_pos : 0 < q
  q_half : q ≤ 1 / 2
  q_sqrt : q ≤ 2 / Real.sqrt n
  q_pow : q ≤ (n : ℝ) ^ (-(2 / 5 : ℝ))
  q_small : 5 * q ^ ((3 : ℝ) / 16) ≤ 1

/-- The product-rank statement is kept explicit as the one algebraic input. -/
def HomogeneousProductRankBound {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (q lam D : ℝ) : Prop :=
  ∀ factors : List (MvPolynomial σ K × ℕ),
    (∀ f ∈ factors, 0 < f.2 ∧ f.1.IsHomogeneous f.2) →
    (factors.map Prod.snd).sum = n →
    R (factors.map Prod.fst).prod ≤
      2 * D * (factors.map (fun f => degreeWeight q lam f.2)).prod

/-- A common bound for a small product and for one expanded high product. -/
def circuitProductEnvelope (n : ℕ) (D : ℝ) : ℝ :=
  2 * D * Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
    (n : ℝ) ^ (-Real.sqrt n / 100)

private lemma sum_get_eq_map_sum {α M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

private lemma prod_get_eq_map_prod {α M : Type*} [CommMonoid M]
    (l : List α) (f : α → M) :
    (∏ i : Fin l.length, f (l.get i)) = (l.map f).prod := by
  rw [← List.prod_ofFn]
  change (List.ofFn (f ∘ l.get)).prod = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- A `Fin`-indexed product-rank theorem supplies the list interface used by circuits. -/
theorem homogeneousProductRankBound_of_fin {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (q lam D : ℝ)
    (h : ∀ (m : ℕ) (P : Fin m → MvPolynomial σ K) (e : Fin m → ℕ),
      (∀ i, 0 < e i) → (∀ i, (P i).IsHomogeneous (e i)) →
      (∑ i, e i) = n → R (∏ i, P i) ≤ 2 * D * ∏ i, degreeWeight q lam (e i)) :
    HomogeneousProductRankBound R n q lam D := by
  intro factors hf hsum
  have hsum' : (∑ i : Fin factors.length, (factors.get i).2) = n := by
    rw [sum_get_eq_map_sum factors Prod.snd]
    exact hsum
  have hb := h factors.length (fun i => (factors.get i).1) (fun i => (factors.get i).2)
    (fun i => (hf _ (List.get_mem _ _)).1)
    (fun i => (hf _ (List.get_mem _ _)).2) hsum'
  simpa only [prod_get_eq_map_prod factors Prod.fst,
    prod_get_eq_map_prod factors (fun f => degreeWeight q lam f.2)] using hb

lemma lowProductBound_of_product_rank {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (s q D : ℝ)
    (hp : WeightParameters n s q) (hD : 0 ≤ D)
    (hprod : HomogeneousProductRankBound R n q (1 / 2 - s / (2 * n)) D) :
    LowProductBound R n ((n : ℝ) / (4 * s)) (circuitProductEnvelope n D) := by
  intro factors hf hsum
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by have := hp.large; omega)
  have hsumreal : (∑ i : Fin factors.length, ((factors.get i).2 : ℝ)) = n := by
    rw [sum_get_eq_map_sum factors (fun f => (f.2 : ℝ))]
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using
      congrArg (fun k : ℕ => (k : ℝ)) hsum
  have hw := low_degreeWeight_product_bound Finset.univ (fun i : Fin factors.length => (factors.get i).2)
    hn1 hp.s_pos hp.s_lower hp.s_upper hp.q_pos hp.q_half hp.q_sqrt hp.q_pow hp.q_small
    (fun i _ => (hf _ (List.get_mem _ _)).1)
    (fun i _ => (hf _ (List.get_mem _ _)).2.2) hsumreal
  rw [prod_get_eq_map_prod factors (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)] at hw
  have hr := hprod factors (fun f h => ⟨(hf f h).1, (hf f h).2.1⟩) hsum
  have hcommon := all_low_common_rank_bound (n : ℝ) 1 D 6 hn1 (by norm_num) hD
  norm_num only [mul_one, one_mul] at hcommon
  calc
    R (factors.map Prod.fst).prod ≤
        2 * D * (factors.map (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)).prod := hr
    _ ≤ 2 * D * (Real.exp (24 * Real.sqrt n) * (n : ℝ) ^ (-Real.sqrt n / 20)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ circuitProductEnvelope n D := by
      simpa only [circuitProductEnvelope, show (4 : ℝ) * 6 = 24 by norm_num,
        mul_assoc] using hcommon

lemma highProductBound_of_product_rank {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (s q D : ℝ)
    (hp : WeightParameters n s q) (hD : 0 ≤ D)
    (hprod : HomogeneousProductRankBound R n q (1 / 2 - s / (2 * n)) D) :
    HighProductBound R n ((n : ℝ) / (4 * s)) (circuitProductEnvelope n D) := by
  intro linears others hlin hothers hlarge hsum
  have hn64 : 64 ≤ (n : ℝ) := by exact_mod_cast hp.large
  have hn1 : 1 ≤ (n : ℝ) := by linarith
  have hbudgetNat : (others.map Prod.snd).sum ≤ n := by omega
  have hbudget : (∑ i : Fin others.length, ((others.get i).2 : ℝ)) ≤ n := by
    rw [sum_get_eq_map_sum others (fun f => (f.2 : ℝ))]
    have hc : ((others.map Prod.snd).sum : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbudgetNat
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using hc
  have hw := expanded_degreeWeight_product_bound Finset.univ
    (fun i : Fin others.length => (others.get i).2) linears.length
    hn64 hp.s_pos hp.s_upper hp.q_pos hp.q_half hp.q_sqrt hp.q_pow hp.q_small
    (fun i _ => (hothers _ (List.get_mem _ _)).1) hbudget hlarge
  rw [prod_get_eq_map_prod others (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)] at hw
  let factors := linears.map (fun p => (p, 1)) ++ others
  have hfactor : ∀ f ∈ factors, 0 < f.2 ∧ f.1.IsHomogeneous f.2 := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hf
      exact ⟨by norm_num, hlin p hp'⟩
    · exact hothers f hf
  have htotal : (factors.map Prod.snd).sum = n := by
    simpa [factors, List.map_append, List.map_map, Function.comp_def] using hsum
  have hr := hprod factors hfactor htotal
  have hr' : R (linears.prod * (others.map Prod.fst).prod) ≤
      2 * D * ((degreeWeight q (1 / 2 - s / (2 * n)) 1) ^ linears.length *
        (others.map (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)).prod) := by
    simpa [factors, List.map_append, List.map_map, Function.comp_def] using hr
  have hcommon := one_high_common_rank_bound (n : ℝ) s 1 D 6 hn1 hp.s_upper
    (by norm_num) hD
  norm_num only [mul_one, one_mul] at hcommon
  calc
    R (linears.prod * (others.map Prod.fst).prod) ≤
        2 * D * ((degreeWeight q (1 / 2 - s / (2 * n)) 1) ^ linears.length *
          (others.map (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)).prod) := hr'
    _ ≤ 2 * D * ((5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) *
        (n : ℝ) ^ (-(3 * Real.sqrt n / 160))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ circuitProductEnvelope n D := by
      simpa only [circuitProductEnvelope, show (4 : ℝ) * 6 = 24 by norm_num,
        neg_div, mul_assoc] using hcommon

/-- The full circuit upper rank estimate, reducing the actual circuit only to
the homogeneous-product rank theorem and explicit numerical parameters. -/
theorem circuit_rank_bound_from_product_rank
    {K : Type*} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (s q D : ℝ) (hp : WeightParameters n s q) (hD : 0 ≤ D)
    (houtput : c.outputDegree = n)
    (hprod : HomogeneousProductRankBound R n q (1 / 2 - s / (2 * n)) D) :
    R (circuitValue c) ≤ 2 * (circuitSize c : ℝ) ^ 2 * D *
      Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) * (n : ℝ) ^ (-Real.sqrt n / 100) := by
  have hB : 0 ≤ circuitProductEnvelope n D := by
    unfold circuitProductEnvelope
    positivity
  have h := circuit_measure_le_of_product_estimates c R hzero hadd hscale n houtput
    ((n : ℝ) / (4 * s)) (circuitProductEnvelope n D) hB
    (lowProductBound_of_product_rank R n s q D hp hD hprod)
    (highProductBound_of_product_rank R n s q D hp hD hprod)
  calc
    R (circuitValue c) ≤ (circuitSize c : ℝ) ^ 2 * circuitProductEnvelope n D := h
    _ = _ := by unfold circuitProductEnvelope; ring

end Problem335

end

end OAI
