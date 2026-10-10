import Mathlib.NumberTheory.Harmonic.Bounds
import PrimeNumberTheoremAnd.Erdos970.MertensClassical
import OAI.NumberTheory.Jacobsthal.Probability.CouplingEvent
import OAI.NumberTheory.Jacobsthal.Sieve.ExponentMarginals

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

noncomputable def paperWeight (E : Finset ℕ) (d : ℕ) : ℝ :=
  ∏ p ∈ E with ¬p ∣ d, (1 - 1 / ((p : ℝ) - 1))
noncomputable def ordinaryProduct (E : Finset ℕ) : ℝ :=
  ∏ p ∈ E, (1 - 1 / (p : ℝ))

lemma eventMass_congr (E : Finset ℕ) {A B : Outcomes E → Prop}
    (h : ∀ s, A s ↔ B s) : eventMass E A = eventMass E B := by
  apply tsum_congr
  intro s
  simp only [h s]

lemma eulerMass_as_weight {p : ℝ} (hp : 2 ≤ p) (j : ℕ) :
    eulerMass p j = (if j = 0 then (1 - 1 / (p - 1)) else 1) / p ^ j := by
  cases j with
  | zero =>
    simp only [eulerMass, ite_true, pow_zero, div_one]
    have hp1 : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  | succ j => simp [eulerMass]

variable (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
include hE

theorem product_eq_iff_vector {d : ℕ} (hd : d ≠ 0) (hs : d.primeFactors ⊆ E)
    (k : E → ℕ) :
    integerProduct E k = d ↔ ∀ p, k p = d.factorization p := by
  constructor
  · intro hh p
    rw [← hh, integerProduct_factorization E hE]
  · intro hh
    rw [show k = (fun p : E => d.factorization p) from funext hh]
    exact integerProduct_factorization_reconstruct E hd hs

theorem upper_integer_mass {d : ℕ} (hd : d ≠ 0) (hs : d.primeFactors ⊆ E) :
    eventMass E (fun s => upperInteger E s = d) = paperWeight E d / (d : ℝ) := by
  calc
    _ = eventMass E (fun s => ∀ p, upperExponent (s p) = d.factorization p) :=
      eventMass_congr E (fun s => product_eq_iff_vector E hE hd hs (fun p => upperExponent (s p)))
    _ = ∏ p : E, eulerMass (p : ℝ) (d.factorization p) :=
      upper_vector_marginal E (fun p hp => (hE p hp).two_le) _
    _ = (∏ p : E, if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1) /
        (∏ p : E, (p : ℝ) ^ d.factorization p) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p _
      exact eulerMass_as_weight (by exact_mod_cast (hE p p.property).two_le) _
    _ = paperWeight E d / (d : ℝ) := by
      congr 1
      · unfold paperWeight
        rw [Finset.prod_filter]
        have he : (∏ p : E, if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1) =
            ∏ p ∈ E, if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1 :=
          Finset.prod_attach E (fun p : ℕ => if d.factorization p = 0 then (1-1/((p : ℝ)-1)) else 1)
        rw [he]
        apply Finset.prod_congr rfl
        intro p hp
        simp only [Nat.factorization_eq_zero_iff, hd, hE p hp, not_true_eq_false,
          or_false, false_or]
      · have hh := congrArg (fun n : ℕ => (n : ℝ)) (integerProduct_factorization_reconstruct E hd hs)
        simpa only [integerProduct, Nat.cast_prod, Nat.cast_pow] using hh

theorem lower_integer_mass {d : ℕ} (hd : d ≠ 0) (hs : d.primeFactors ⊆ E) :
    eventMass E (fun s => lowerInteger E s = d) = ordinaryProduct E / (d : ℝ) := by
  calc
    _ = eventMass E (fun s => ∀ p, lowerExponent (s p) = d.factorization p) :=
      eventMass_congr E (fun s => product_eq_iff_vector E hE hd hs (fun p => lowerExponent (s p)))
    _ = ∏ p : E, geometricMass (p : ℝ) (d.factorization p) :=
      lower_vector_marginal E (fun p hp => (hE p hp).two_le) _
    _ = (∏ p : E, (1 - 1 / (p : ℝ))) / (∏ p : E, (p : ℝ) ^ d.factorization p) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p _
      simp [geometricMass, div_eq_mul_inv]
    _ = ordinaryProduct E / (d : ℝ) := by
      congr 1
      · exact Finset.prod_attach E (fun p : ℕ => 1 - 1 / (p : ℝ))
      · have hh := congrArg (fun n : ℕ => (n : ℝ)) (integerProduct_factorization_reconstruct E hd hs)
        simpa only [integerProduct, Nat.cast_prod, Nat.cast_pow] using hh

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

def supportedIntegers (E : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ E)
noncomputable def weightedSmallSum (E : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ d ∈ supportedIntegers E N, paperWeight E d / (d : ℝ)
noncomputable def ordinarySmallSum (E : Finset ℕ) (N : ℕ) : ℝ :=
  ordinaryProduct E * ∑ d ∈ supportedIntegers E N, 1 / (d : ℝ)

theorem eventMass_finite_values (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p)
    (f : Outcomes E → ℕ) (D : Finset ℕ) :
    eventMass E (fun s => f s ∈ D) = ∑ d ∈ D, eventMass E (fun s => f s = d) := by
  unfold eventMass
  rw [← Summable.tsum_finsetSum (fun d _ => product_event_summable E hE (fun s => f s = d))]
  apply tsum_congr
  intro s
  have he := Finset.sum_ite_eq D (f s) (fun _ : ℕ => productMass E s)
  convert he.symm using 1
  all_goals first
    | (apply Finset.sum_congr rfl; intro d _; split_ifs <;> rfl)
    | (split_ifs <;> rfl)

theorem product_mem_supported_iff (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (k : E → ℕ) (N : ℕ) :
    integerProduct E k ∈ supportedIntegers E N ↔ integerProduct E k ≤ N := by
  simp only [supportedIntegers, Finset.mem_filter, Finset.mem_Icc]
  have hp := integerProduct_pos E hE k
  have hs := integerProduct_support E hE k
  exact ⟨fun h => h.1.2, fun h => ⟨⟨hp, h⟩, hs⟩⟩

theorem weightedSmallSum_eq_event (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) (N : ℕ) :
    weightedSmallSum E N = eventMass E (fun s => upperInteger E s ≤ N) := by
  unfold weightedSmallSum
  simp only [upperInteger]
  rw [← eventMass_congr E (fun s => product_mem_supported_iff E hE (fun p => upperExponent (s p)) N)]
  rw [eventMass_finite_values E (fun p hp => (hE p hp).two_le)]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hd
  exact (upper_integer_mass E hE (by have := (Finset.mem_Icc.mp hI).1; omega) hs).symm

theorem ordinarySmallSum_eq_event (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) (N : ℕ) :
    ordinarySmallSum E N = eventMass E (fun s => lowerInteger E s ≤ N) := by
  simp only [lowerInteger]
  rw [← eventMass_congr E (fun s => product_mem_supported_iff E hE (fun p => lowerExponent (s p)) N)]
  rw [eventMass_finite_values E (fun p hp => (hE p hp).two_le)]
  unfold ordinarySmallSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hd
  have hm := lower_integer_mass E hE (d := d) (by have := (Finset.mem_Icc.mp hI).1; omega) hs
  calc
    _ = ordinaryProduct E / (d : ℝ) := by ring
    _ = _ := hm.symm

theorem weightedSmallSum_coupling_lower (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    {P : ℝ} (hP : 1 < P) :
    ordinarySmallSum E ⌊P ^ (94 / 100 : ℝ)⌋₊ - 100 * uniformMomentBound / Real.log P ≤
      weightedSmallSum E ⌊P ^ (95 / 100 : ℝ)⌋₊ := by
  rw [ordinarySmallSum_eq_event E hE, weightedSmallSum_eq_event E hE]
  have he (f : Outcomes E → ℕ) (a : ℝ) :
      eventMass E (fun s => f s ≤ ⌊P ^ a⌋₊) = eventMass E (fun s => (f s : ℝ) ≤ P ^ a) := by
    apply eventMass_congr E
    intro s
    exact Nat.le_floor_iff (Real.rpow_nonneg (by linarith) _)
  rw [he, he]
  exact small_product_coupling_lower E hE hP

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

theorem finite_product_reindex {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : κ → α → ℝ) (A : (κ → α) → Prop) :
    (∑' s : ι → α, if A ((Equiv.piCongrLeft (fun _ : κ => α) e) s)
      then ∏ i, w (e i) (s i) else 0) =
    ∑' s : κ → α, if A s then ∏ i, w i (s i) else 0 := by
  rw [← (Equiv.piCongrLeft (fun _ : κ => α) e).tsum_eq]
  apply tsum_congr
  intro s
  split_ifs
  · rw [← e.prod_comp]
    apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piCongrLeft]
  · rfl

def restrictOutcomes {E F : Finset ℕ} (hEF : E ⊆ F) (s : Outcomes F) : Outcomes E :=
  fun p => s ⟨p, hEF p.property⟩

def retainedIndexEquiv {E F : Finset ℕ} (hEF : E ⊆ F) :
    {p : F // (p : ℕ) ∈ E} ≃ E where
  toFun p := ⟨p.val, p.property⟩
  invFun p := ⟨⟨p, hEF p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem eventMass_restrict {E F : Finset ℕ} (hEF : E ⊆ F)
    (hF : ∀ p ∈ F, 2 ≤ p) (A : Outcomes E → Prop) :
    eventMass F (fun s => A (restrictOutcomes hEF s)) = eventMass E A := by
  let e := retainedIndexEquiv hEF
  let ep := Equiv.piCongrLeft (fun _ : E => Sample) e
  have h := finite_product_restrict (fun p : F => (p : ℕ) ∈ E)
    (fun p : F => jointMass (p : ℝ))
    (fun p => jointMass_nonneg (by exact_mod_cast hF p p.property))
    (fun p => jointMass_hasSum (by exact_mod_cast hF p p.property))
    (fun s => A (ep s))
  have hr := finite_product_reindex e (fun p : E => jointMass (p : ℝ)) A
  calc
    _ = ∑' s : F → Sample, if A (ep (fun p => s p)) then ∏ p : F, jointMass (p : ℝ) (s p) else 0 := by
      apply tsum_congr
      intro s
      have hh : ep (fun p => s p) = restrictOutcomes hEF s := by
        funext p
        rfl
      simp only [hh, productMass]
    _ = _ := h
    _ = _ := by
      convert hr using 1
      all_goals
        apply tsum_congr
        intro s
        split_ifs
        · apply Finset.prod_congr
          · ext i; simp only [Finset.mem_univ]
          · intro i _; rfl
        · rfl

theorem lowerInteger_restrict_le {E F : Finset ℕ} (hEF : E ⊆ F)
    (hF : ∀ p ∈ F, Nat.Prime p) (s : Outcomes F) :
    lowerInteger E (restrictOutcomes hEF s) ≤ lowerInteger F s := by
  let f : ℕ → ℕ := fun p => if hp : p ∈ F then p ^ lowerExponent (s ⟨p, hp⟩) else 1
  have he : lowerInteger E (restrictOutcomes hEF s) = ∏ p ∈ E, f p := by
    rw [lowerInteger, integerProduct, ← Finset.prod_attach E f]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dite_eq_left (hEF p.property), restrictOutcomes]
  have hf : lowerInteger F s = ∏ p ∈ F, f p := by
    rw [lowerInteger, integerProduct, ← Finset.prod_attach F f]
    apply Finset.prod_congr rfl
    intro p _
    simp only [f, dite_eq_left p.property]
  rw [he, hf]
  apply Finset.prod_le_prod_of_subset_of_one_le₀ hEF
  · intro p _; exact Nat.zero_le _
  · intro p hp _
    simp only [f, dite_eq_left hp]
    exact one_le_pow₀ (hF p hp).pos

theorem ordinarySmallSum_antitone {E F : Finset ℕ} (hEF : E ⊆ F)
    (hF : ∀ p ∈ F, Nat.Prime p) (N : ℕ) :
    ordinarySmallSum F N ≤ ordinarySmallSum E N := by
  rw [ordinarySmallSum_eq_event F hF,
    ordinarySmallSum_eq_event E (fun p hp => hF p (hEF hp))]
  rw [← eventMass_restrict hEF (fun p hp => (hF p hp).two_le)]
  apply Summable.tsum_le_tsum
  · intro s
    have hn := productMass_nonneg F (fun p hp => (hF p hp).two_le) s
    by_cases h : lowerInteger F s ≤ N
    · have hh := (lowerInteger_restrict_le hEF hF s).trans h
      simp only [ite_eq_left h, ite_eq_left hh, le_refl]
    · simp only [ite_eq_right h]; split_ifs <;> linarith
  · exact product_event_summable F (fun p hp => (hF p hp).two_le) _
  · exact product_event_summable F (fun p hp => (hF p hp).two_le) _

end EulerWeightedLower



namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def primesThrough (P : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊P⌋₊).filter Nat.Prime

lemma primesThrough_prime {P : ℝ} {p : ℕ} (hp : p ∈ primesThrough P) : Nat.Prime p :=
  (Finset.mem_filter.mp hp).2

lemma ordinaryProduct_nonneg (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p) :
    0 ≤ ordinaryProduct E := by
  apply Finset.prod_nonneg
  intro p hp
  exact sub_nonneg.mpr (reciprocal_lt_one (by exact_mod_cast (hE p hp).two_le)).le

theorem supportedIntegers_primesThrough {P : ℝ} {N : ℕ} (hN : N ≤ ⌊P⌋₊) :
    supportedIntegers (primesThrough P) N = Finset.Icc 1 N := by
  apply Finset.filter_eq_self.mpr
  intro d hd p hp
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hpd : p ≤ d := Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hp)
  have hpr := Nat.prime_of_mem_primeFactors hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpr.pos, hpd.trans ((Finset.mem_Icc.mp hd).2.trans hN)⟩, hpr⟩

lemma harmonic_real_eq (N : ℕ) :
    (harmonic N : ℝ) = ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem ordinarySmallSum_primesThrough {P : ℝ} {N : ℕ} (hN : N ≤ ⌊P⌋₊) :
    ordinarySmallSum (primesThrough P) N = ordinaryProduct (primesThrough P) * (harmonic N : ℝ) := by
  rw [ordinarySmallSum, supportedIntegers_primesThrough hN, harmonic_real_eq]

noncomputable def uniformLowerEnvelope (P : ℝ) : ℝ :=
  (94 / 100 : ℝ) * Real.log P * ordinaryProduct (primesThrough P) -
    100 * uniformMomentBound / Real.log P

theorem weightedSmallSum_uniform_lower {P : ℝ} (hP : 1 < P)
    (E : Finset ℕ) (hE : E ⊆ primesThrough P) :
    uniformLowerEnvelope P ≤ weightedSmallSum E ⌊P ^ (95 / 100 : ℝ)⌋₊ := by
  have hpr : ∀ p ∈ primesThrough P, Nat.Prime p := fun p hp => primesThrough_prime hp
  have hEs : ∀ p ∈ E, Nat.Prime p := fun p hp => hpr p (hE hp)
  have hpow : P ^ (94 / 100 : ℝ) ≤ P := Real.rpow_le_self_of_one_le hP.le (by norm_num)
  have hfloor := Nat.floor_mono hpow
  have hm := ordinarySmallSum_antitone hE hpr ⌊P ^ (94 / 100 : ℝ)⌋₊
  rw [ordinarySmallSum_primesThrough hfloor] at hm
  have hh := log_le_harmonic_floor (P ^ (94 / 100 : ℝ)) (Real.rpow_nonneg (by linarith) _)
  rw [Real.log_rpow (by linarith : 0 < P)] at hh
  have hl := mul_le_mul_of_nonneg_left hh (ordinaryProduct_nonneg _ hpr)
  have hc := weightedSmallSum_coupling_lower E hEs hP
  unfold uniformLowerEnvelope
  nlinarith

theorem uniformLowerEnvelope_limit :
    Tendsto uniformLowerEnvelope atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) * (94 / 100 : ℝ))) := by
  have he3 : Tendsto _root_.Erdos970.Mertens.E₃ atTop (𝓝 (0 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have hm : Tendsto (fun P : ℝ => Real.log P * ordinaryProduct (primesThrough P))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    have h := he3.rexp.const_mul (Real.exp (-Real.eulerMascheroniConstant))
    simp only [Real.exp_zero, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    rw [ordinaryProduct, primesThrough, _root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hP]
    field_simp [ne_of_gt (Real.log_pos hP)]
  have hz : Tendsto (fun P : ℝ => 100 * uniformMomentBound / Real.log P) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  convert (hm.const_mul (94 / 100 : ℝ)).sub hz using 1
  · funext P; unfold uniformLowerEnvelope; ring
  · congr 1; ring

theorem weightedSmallSum_eventually_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℝ in atTop, ∀ E : Finset ℕ, E ⊆ primesThrough P →
      Real.exp (-Real.eulerMascheroniConstant) * ((94 / 100 : ℝ) - ε) ≤
        weightedSmallSum E ⌊P ^ (95 / 100 : ℝ)⌋₊ := by
  have hgap : Real.exp (-Real.eulerMascheroniConstant) * ((94 / 100 : ℝ) - ε) <
      Real.exp (-Real.eulerMascheroniConstant) * (94 / 100 : ℝ) := by
    nlinarith [Real.exp_pos (-Real.eulerMascheroniConstant)]
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    uniformLowerEnvelope_limit.eventually (lt_mem_nhds hgap)] with P hP hbound
  intro E hE
  exact hbound.le.trans (weightedSmallSum_uniform_lower hP E hE)

end EulerWeightedLower


end Erdos970

end OAI
