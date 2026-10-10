import OAI.Probability.InvariantIsing.Cavity.CavityCapTailAverage
import OAI.Probability.InvariantIsing.Cavity.CavityFullTightness

namespace OAI

/-! Radial tightness from the second moment of the full tilted law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma cavity_square_tail_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (R : X → ℝ)
    (hi : Integrable (fun x => R x ^ 2) ν) {A : ℝ} (hA : 0 < A) :
    ν.real {x | A < |R x|} ≤ (∫ x, R x ^ 2 ∂ν) / A ^ 2 := by
  have hs : {x | A < |R x|} ⊆ {x | A ^ 2 ≤ R x ^ 2} := by
    intro x hx
    change A ^ 2 ≤ R x ^ 2
    have h := pow_le_pow_left₀ hA.le (le_of_lt hx) 2
    simpa only [sq_abs] using h
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all ν fun x => sq_nonneg (R x)) hi (A ^ 2)
  have ht := mul_le_mul_of_nonneg_left (measureReal_mono (μ := ν) hs) (sq_nonneg A)
  nlinarith

theorem cavity_random_tilted_square_tail {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H) (hR : Measurable R)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^2)
      ((ν ω).tilted (fun x => H (ω,x))))
    (hmi : Integrable (fun ω => ∫ x, R (ω,x)^2
      ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {M A : ℝ} (hA : 0 < A)
    (hM : (∫ ω, ∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ M) :
    (∫ ω, ((ν ω).tilted (fun x => H (ω,x))).real {x | A < |R (ω,x)|} ∂P) ≤
      M / A^2 := by
  classical
  let Z := fun ω => ∫ x, (if A < |R (ω,x)| then (1 : ℝ) else 0)
    ∂(ν ω).tilted (fun x => H (ω,x))
  have hs : MeasurableSet {p : Ω × X | A < |R p|} :=
    measurableSet_lt measurable_const hR.abs
  have hZ ω : Z ω = ((ν ω).tilted (fun x => H (ω,x))).real {x | A < |R (ω,x)|} := by
    change (∫ x, {x | A < |R (ω,x)|}.indicator (fun _ => (1 : ℝ)) x
      ∂(ν ω).tilted (fun x => H (ω,x))) = _
    exact integral_indicator_one (hs.preimage measurable_prodMk_left)
  have hmZ : Measurable Z := measurable_random_tilted_integral hν hH
    (Measurable.ite hs measurable_const measurable_const)
  have hiZ : Integrable Z P := Integrable.of_bound hmZ.aestronglyMeasurable 1 (by
    filter_upwards [he] with ω hω
    let := isProbabilityMeasure_tilted hω
    have hb := norm_integral_le_of_norm_le_const (μ := (ν ω).tilted (fun x => H (ω,x)))
      (f := fun x => if A < |R (ω,x)| then (1 : ℝ) else 0) (C := 1)
      (ae_of_all _ fun x => by split_ifs <;> norm_num)
    simpa only [probReal_univ, mul_one] using hb)
  have hb : ∀ᵐ ω ∂P, Z ω ≤
      (∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) / A^2 := by
    filter_upwards [he, hi] with ω heω hiω
    let := isProbabilityMeasure_tilted heω
    rw [hZ]
    exact cavity_square_tail_le _ _ hiω hA
  have hh := integral_mono_ae hiZ (hmi.div_const (A^2)) hb
  simp only [hZ, integral_div] at hh
  exact hh.trans (div_le_div_of_nonneg_right hM (sq_nonneg A))

lemma cavity_tightness_add (f g : ℕ → ℝ → ℝ)
    (hf : ∀ n, Antitone (f n)) (hg : ∀ n, Antitone (g n))
    (htf : ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop, f n A < ε)
    (htg : ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop, g n A < ε) :
    ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop, f n A + g n A < ε := by
  intro ε hε
  obtain ⟨A, hA, hAf⟩ := htf (ε/2) (by positivity)
  obtain ⟨B, hB, hBg⟩ := htg (ε/2) (by positivity)
  refine ⟨max A B, lt_max_of_lt_left hA, ?_⟩
  filter_upwards [hAf, hBg] with n hfn hgn
  have hfn' := (hf n (le_max_left A B)).trans_lt hfn
  have hgn' := (hg n (le_max_right A B)).trans_lt hgn
  linarith

end InvariantIsing

end

end OAI
