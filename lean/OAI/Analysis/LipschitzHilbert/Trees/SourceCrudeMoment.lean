import OAI.Analysis.LipschitzHilbert.Trees.SourceCentralHolder
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedMassPower

namespace OAI

/-! The linear node envelope gives the crude normalized moment on the
whole phase tube. Only the first power of the mass is integrated; its
remaining small power is controlled by the root mass bound. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem source_node_normalized_energy_le {n U C alpha p : ℝ}
    (A : EuclideanSpace ℂ κ) (hn : 0 < n) (hnU : n ≤ U)
    (hC : 0 ≤ C) (ha : 1 ≤ alpha) (hp : 0 < p) (hA : ‖A‖ ≤ C*n) :
    ‖(n^(alpha/p-1)) • A‖^p ≤ C^p*U^(alpha-1)*n := by
  rw [normalized_vertex_energy_eq hn hp.ne']
  calc
    _ ≤ n^(alpha-p)*(C*n)^p := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hA hp.le) (Real.rpow_nonneg hn.le _)
    _ = C^p*(n^(alpha-1)*n) := by
      rw [Real.mul_rpow hC hn.le]
      have hsum : n^(alpha-p)*n^p = n^alpha := by
        rw [← Real.rpow_add hn]
        congr 1
        ring
      have hsplit : n^(alpha-1)*n = n^alpha := by
        conv_lhs => rhs; rw [← Real.rpow_one n]
        rw [← Real.rpow_add hn]
        congr 1
        ring
      rw [hsplit]
      calc
        _ = C^p*(n^(alpha-p)*n^p) := by ring
        _ = _ := by rw [hsum]
    _ ≤ _ := by
      have hpow := Real.rpow_le_rpow hn.le hnU (sub_nonneg.mpr ha)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hC p)) hn.le

theorem source_node_normalized_moment (μ : Measure X)
    (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (U C alpha p : ℝ)
    (hn : ∀ x, 0 < n x) (hnU : ∀ x, n x ≤ U) (hnmeas : Measurable n)
    (hnint : Integrable n μ) (hAmeas : Measurable A)
    (hU : 0 < U) (hC : 0 ≤ C) (ha : 1 ≤ alpha) (hp : 0 < p)
    (hA : ∀ x, ‖A x‖ ≤ C*n x) :
    Integrable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) μ ∧
      (∫ x, ‖(n x^(alpha/p-1)) • A x‖^p ∂μ)^(1/p) ≤
        C*U^((alpha-1)/p)*(∫ x, n x ∂μ)^(1/p) := by
  have hpoint := fun x => source_node_normalized_energy_le (A x) (hn x) (hnU x)
    hC ha hp (hA x)
  have hmeas : Measurable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) :=
    (((hnmeas.pow_const _).smul hAmeas).norm).pow_const _
  have hi : Integrable (fun x => ‖(n x^(alpha/p-1)) • A x‖^p) μ :=
    (hnint.const_mul (C^p*U^(alpha-1))).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hpoint x)
  have hb : (∫ x, ‖(n x^(alpha/p-1)) • A x‖^p ∂μ) ≤
      C^p*U^(alpha-1)*(∫ x, n x ∂μ) := by
    simpa only [integral_const_mul] using integral_mono hi
      (hnint.const_mul (C^p*U^(alpha-1))) hpoint
  refine ⟨hi,?_⟩
  apply (Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) hb
    (one_div_nonneg.mpr hp.le)).trans_eq
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hU.le _))
      (integral_nonneg fun x => (hn x).le),
    Real.mul_rpow (Real.rpow_nonneg hC _) (Real.rpow_nonneg hU.le _),
    ← Real.rpow_mul hC,← Real.rpow_mul hU.le,mul_one_div_cancel hp.ne',Real.rpow_one]
  rw [show (alpha-1)*(1/p) = (alpha-1)/p by ring]

/-- For p=√L the root mass contributes only exp(4√L), uniformly
in the imaginary phase. This is the crude estimate in §11. -/
theorem eventually_source_crude_normalized_moment (q b : ℝ) (_hb : 0 ≤ b) :
    ∀ᶠ L : ℝ in atTop, ∀ (μ : Measure X)
      (n : X → ℝ) (A : X → EuclideanSpace ℂ κ) (U S alpha r : ℝ),
      (∀ x, 0 < n x) → (∀ x, n x ≤ U) → Measurable n → Integrable n μ →
      Measurable A → 0 < U → 0 ≤ S → 1 ≤ alpha → alpha ≤ 3 → 0 ≤ r →
      Real.log U ≤ 2*L → (∫ x, n x ∂μ) ≤ L^b*S →
      (∀ x, ‖A x‖ ≤ L^q*(1+r)*n x) →
      Integrable (fun x => ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L)) μ ∧
      (∫ x, ‖(n x^(alpha/Real.sqrt L-1)) • A x‖^(Real.sqrt L) ∂μ)^(1/Real.sqrt L) ≤
        (L^(q+1)*S^(1/Real.sqrt L))*(1+r)*Real.exp (4*Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop b] with L hL hpB
  intro μ n A U S alpha r hn hnU hnmeas hnint hAmeas hU hS ha ha3 hr hlog hmass hnode
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  obtain ⟨hi,hbound⟩ := source_node_normalized_moment μ n A U (L^q*(1+r))
    alpha (Real.sqrt L) hn hnU hnmeas hnint hAmeas hU (by positivity) ha hp hnode
  have hUpow : U^((alpha-1)/Real.sqrt L) ≤ Real.exp (4*Real.sqrt L) := by
    have he : 0 ≤ (alpha-1)/Real.sqrt L := div_nonneg (sub_nonneg.mpr ha) hp.le
    rw [Real.rpow_def_of_pos hU]
    apply Real.exp_le_exp.mpr
    calc
      Real.log U*((alpha-1)/Real.sqrt L) ≤ (2*L)*((alpha-1)/Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hlog he
      _ ≤ (2*L)*(2/Real.sqrt L) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith) hp.le) (by positivity)
      _ = 4*Real.sqrt L := by
        have hs2 := Real.sq_sqrt hL0.le
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
    _ ≤ (L^q*(1+r))*Real.exp (4*Real.sqrt L)*(L*S^(1/Real.sqrt L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hUpow (by positivity)) hmasspow
        (Real.rpow_nonneg (integral_nonneg fun x => (hn x).le) _) (by positivity)
    _ = _ := by
      rw [show L^(q+1) = L^q*L from by rw [Real.rpow_add hL0,Real.rpow_one]]
      ring

end LipschitzHilbert

end

end OAI
