import OAI.NumberTheory.JointDickman.Amplification.GeneratingDegreeExpansion
import OAI.NumberTheory.JointDickman.Arithmetic.OrderedPrimeTupleLimit
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicAvoidanceDickman

namespace OAI

/-! # Limits of the prime-avoidance coefficients -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology

 theorem orderedPrimeBox_full_mass {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((FiniteMeasure.pi (fun _ : Fin n => logarithmicPrimeMeasure c))
      (orderedPrimeBox n (fun _ => c) (fun _ => 1) 1) : ℝ) = logarithmicSimplex n c := by
  have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
    rw [ae_iff]
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
  have hp : ∀ᵐ t : Fin n → ℝ ∂Measure.pi (fun _ : Fin n =>
      (logarithmicPrimeMeasure c : Measure ℝ)), t ∈ Set.pi Set.univ (fun _ => Set.Ioc c 1) := by
    have ht := eventually_all.mpr (fun i : Fin n => (Measure.tendsto_eval_ae_ae (i := i)).eventually hs)
    exact ht.mono (fun t ht i _ => ht i)
  have he : orderedPrimeBox n (fun _ => c) (fun _ => 1) 1 =
      Set.pi Set.univ (fun _ => Set.Ioc c 1) ∩ orderedTupleRegion n 1 := by
    ext t
    simp only [orderedPrimeBox, primeBoxCutoff, orderedTupleRegion, Set.mem_inter_iff]
    tauto
  change ((Measure.pi (fun _ : Fin n => (logarithmicPrimeMeasure c : Measure ℝ)))
    (orderedPrimeBox n (fun _ => c) (fun _ => 1) 1)).toReal = _
  rw [he, Measure.measure_inter_eq_of_ae hp]
  rfl

 theorem primeAvoidanceDegree_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) (n : ℕ) :
    Tendsto (fun x => primeGeneratingDegree (largePrimeSet x (x^c)) (fun _ => 0) ⌊x⌋₊ (n+1))
      atTop (𝓝 ((-1 : ℝ)^(n+1)*logarithmicSimplex (n+1) c)) := by
  have ht := (orderedReciprocalPrimeTuple_scaled_box_tendsto hc hc1 zero_lt_one n
    (fun _ => c) (fun _ => 1)).const_mul ((-1 : ℝ)^(n+1))
  rw [orderedPrimeBox_full_mass hc] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [primeGeneratingDegree_ordered, mul_sum]
  apply sum_congr rfl
  intro v hv
  have hb (i : Fin (n+1)) : x^c < v i ∧ (v i : ℝ) ≤ x := by
    obtain ⟨hp,hlo⟩ := mem_filter.mp ((orderedPrimeTuples_mem.mp hv).1 i)
    obtain ⟨hpx,_⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hlo,(Nat.le_floor_iff (zero_lt_one.trans hx).le).mp hpx⟩
  have hbd : (∏ i, v i) ≤ ⌊x⌋₊ ↔ (∏ i, (v i : ℝ)) ≤ x := by
    rw [Nat.le_floor_iff (zero_lt_one.trans hx).le]
    norm_cast
  have hi : (∀ i, x^c < v i ∧ (v i : ℝ) ≤ x^1) := by simpa using hb
  have hden : (∏ i, 1/(v i : ℝ)) = 1/(∏ i, v i : ℕ) := by
    push_cast
    simp [one_div, prod_inv_distrib]
  simp only [hi, true_and, one_mul, hbd, zero_sub, prod_const, card_univ, Fintype.card_fin]
  split_ifs <;> simp_all [div_eq_mul_inv]

end JointDickman

end OAI
