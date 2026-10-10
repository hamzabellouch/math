import OAI.Analysis.LipschitzHilbert.Trees.SourceCrudeMomentAE

namespace OAI

/-! The polynomial total-mass factor requires one extra unit of logarithmic
slack beyond the manuscript's log N ≤ 2L. This leaves the same Gaussian
large-imaginary argument, with exp(6√L) in its crude bound. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

/-- For p=√L the root mass contributes only exp(6√L), uniformly
in the imaginary phase. This is the crude estimate in §11. -/
theorem eventually_source_crude_mass_budget (q b : ℝ) (_hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (μ : Measure X)
      (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (U S alpha r : ℝ),
      (∀ x, 0 < n x) → (∀ᵐ x ∂μ, n x ≤ U) → Measurable n → Integrable n μ →
      Measurable A → 0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ r →
      Real.log U ≤ 3*L → (∫ x, n x ∂μ) ≤ L^b*S →
      (∀ᵐ x ∂μ, ‖A x‖ ≤ L^q*(1+r)*n x) →
      Integrable (fun x => ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L)) μ ∧
      (∫ x, ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L) ∂μ)^(1/Real.sqrt L) ≤
        (L^(q+1)*S^(1/Real.sqrt L))*(1+r)*Real.exp (6*Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop b] with L hL hpB
  intro μ n A U S alpha r hn hnU hnmeas hnint hAmeas hU hS ha ha3 hr hlog hmass hnode
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  obtain ⟨hi,hbound⟩ := source_node_normalized_moment_ae μ n A U (L^q*(1+r))
    alpha (Real.sqrt L) hn hnU hnmeas hnint hAmeas hU (by positivity) ha hp hnode
  have hUpow : U^((alpha-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) :=
    by
      have hs2 := Real.sq_sqrt hL0.le
      have he : 0 ≤ (alpha-1)/Real.sqrt L := div_nonneg (by linarith) hp.le
      rw [Real.rpow_def_of_pos hU]
      apply Real.exp_le_exp.mpr
      calc
        Real.log U*((alpha-1)/Real.sqrt L) ≤ (3*L)*((alpha-1)/Real.sqrt L) :=
          mul_le_mul_of_nonneg_right hlog he
        _ ≤ (3*L)*(2/Real.sqrt L) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) hp.le) (by positivity)
        _ = 6*Real.sqrt L := by
          field_simp
          nlinarith
  have hmasspow : (∫ x, n x ∂μ)^(1/Real.sqrt L) ≤ L*S^(1/Real.sqrt L) := by
    have h := Real.rpow_le_rpow (integral_nonneg fun x => (hn x).le) hmass
      (one_div_nonneg.mpr hp.le)
    rw [Real.mul_rpow (Real.rpow_nonneg hL0.le _) hS,← Real.rpow_mul hL0.le] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hS _)
    calc
      L^(b*(1/Real.sqrt L)) ≤ L^((1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hL (by
          have hbp := (div_le_one hp).mpr hpB
          simpa only [div_eq_mul_inv,one_div,one_mul] using hbp)
      _ = L := Real.rpow_one L
  refine ⟨hi,hbound.trans ?_⟩
  calc
    _ ≤ (L^q*(1+r))*Real.exp (6*Real.sqrt L)*(L*S^(1/Real.sqrt L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hUpow (by positivity)) hmasspow
        (Real.rpow_nonneg (integral_nonneg fun x => (hn x).le) _) (by positivity)
    _ = _ := by
      rw [show L^(q+1) = L^q*L from by rw [Real.rpow_add hL0,Real.rpow_one]]
      ring


end LipschitzHilbert

end

end OAI
