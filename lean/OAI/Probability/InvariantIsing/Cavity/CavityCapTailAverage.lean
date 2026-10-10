import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCapTail

namespace OAI

/-! Expected cap errors depend only on discarded full-Gibbs mass. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

theorem cavity_replica_cap_tail_expectation {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (T : ℝ) (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (hgood : ∀ ω x, x ∉ s ω → H (ω,x) ≤ T)
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    |(∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (min (H (ω,x)) T))
        (fun σ => F (ω,σ)) ∂P) -
      ∫ ω, cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
        (fun σ => F (ω,σ)) ∂P| ≤
      2 * B * r * ∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real (s ω) ∂P := by
  classical
  let Z := fun ω => ∫ x, (if x ∈ s ω then (1 : ℝ) else 0)
    ∂(ν ω).tilted (fun x => H (ω,x))
  have hsω ω : MeasurableSet (s ω) := hs.preimage measurable_prodMk_left
  have hZ ω : Z ω = ((ν ω).tilted (fun x => H (ω,x))).real (s ω) := by
    change (∫ x, (s ω).indicator (fun _ => (1 : ℝ)) x
      ∂(ν ω).tilted (fun x => H (ω,x))) = _
    simp only [integral_indicator_const _ (hsω ω), smul_eq_mul, mul_one]
  have hmZ : Measurable Z := measurable_random_tilted_integral hν hH
    (Measurable.ite hs measurable_const measurable_const)
  have hiZ : Integrable Z P := Integrable.of_bound hmZ.aestronglyMeasurable 1 (by
    filter_upwards [he] with ω hω
    let := isProbabilityMeasure_tilted hω
    have hb := norm_integral_le_of_norm_le_const (μ := (ν ω).tilted (fun x => H (ω,x)))
      (f := fun x => if x ∈ s ω then (1 : ℝ) else 0) (C := 1)
      (ae_of_all _ fun x => by split_ifs <;> norm_num)
    simpa only [probReal_univ, mul_one] using hb)
  have hc : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (min (H (ω,x)) T)) (ν ω) :=
    ae_of_all _ fun ω => integrable_of_measurable_abs_le
      (((hH.comp measurable_prodMk_left).min measurable_const).exp)
      (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (min_le_right _ _))
  have hiC := cavity_exp_replicaMean_integrable P ν hν (fun p => min (H p) T)
    (hH.min measurable_const) F hF hc hFb
  have hiF := cavity_exp_replicaMean_integrable P ν hν H hH F hF he hFb
  let D := fun ω => cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (min (H (ω,x)) T))
      (fun σ => F (ω,σ)) - cavityWeightedReplicaMean (ν ω) (fun x => Real.exp (H (ω,x)))
      (fun σ => F (ω,σ))
  have hb : ∀ᵐ ω ∂P, |D ω| ≤ (2 * B * r) * Z ω := by
    filter_upwards [he] with ω hω
    rw [hZ]
    exact cavity_replica_cap_tail_error (ν ω) (fun x => H (ω,x))
      (hH.comp measurable_prodMk_left) hω T (s ω) (hsω ω) (hgood ω)
      (fun σ => F (ω,σ)) (hF.comp measurable_prodMk_left) hB (hFb ω)
  rw [← integral_sub hiC hiF]
  calc
    _ ≤ ∫ ω, |D ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2 * B * r) * Z ω ∂P :=
      integral_mono_ae (hiC.sub hiF).abs (hiZ.const_mul _) hb
    _ = _ := by simp only [integral_const_mul, hZ]

end InvariantIsing

end

end OAI
