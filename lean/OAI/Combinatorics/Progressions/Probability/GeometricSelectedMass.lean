import OAI.Combinatorics.Progressions.Sampling.AllocatedUniformGeometricSampling

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedGeometricSamplingInput_mass_bounds (m : ℕ) {p c e E t : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E) (ht : 0 ≤ t) :
    2 ≤ allocatedGeometricSamplingInput m p c e E t ∧
      (probabilityProfileLipschitz : ℝ) ≤ allocatedGeometricSamplingInput m p c e E t := by
  let q := allocatedGeometrySourceInput m p c e E
  let u := siteSourceParameter m q
  let w := siteSourceMaskLog m q
  let v := allocatedIdealProfileLog m u e
  have hq : 0 ≤ q := (allocatedGeometricSourceBudget_controls m hp hc he hE).1
  have hu : 0 ≤ u := (siteSourceParameter_bounds m hq).1
  have hw : 0 ≤ w := siteSourceMaskLog_nonneg m hq
  have hv : 0 ≤ v := allocatedIdealProfileLog_nonneg m hu he
  obtain ⟨hL, _, hTL, _, hUF, _, hLF⟩ := allocatedSiteErrorFourier_budgets m hu hw hv
  have hF : 0 ≤ allocatedSiteErrorFourierOutput m u w v := hu.trans hUF
  have hcontrols := allocatedGeometricSamplingInput_controls m hp hc he hE ht
  constructor
  · change 2 ≤ (m + 2 : ℕ) * (t + 1) + allocatedSiteErrorFourierOutput m u w v
    have hm : (2 : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show 2 ≤ m + 2 by omega)
    nlinarith
  · have hD := allocatedComparisonDimension_bounds m hu
    have hprofile : (probabilityProfileLipschitz : ℝ) ≤ allocatedComparisonDimension m u := by
      apply le_trans _ hD.2.2.2.2.2.2.2.2
      exact (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
    have hDT := (allocatedSiteErrorPrimitiveLog_bounds m hu hw hv).2.2.1
    have hLle : allocatedSiteErrorFourierInput m u w v ≤ allocatedSiteErrorFourierOutput m u w v := by
      apply le_trans _ hLF
      exact le_add_of_nonneg_left (by positivity)
    exact hprofile.trans (hDT.trans (hTL.trans (hLle.trans hcontrols.2.2.2)))

end Erdos3.VectorPolynomial

namespace Erdos3

open scoped BigOperators

theorem selectedResidue_mass_of_polynomial_threshold {Q I : Type*} [Fintype Q] [Fintype I]
    (k : ℕ) (hk : 2 ≤ k) {P Pbase ρ : ℝ}
    (hP : 2 ≤ P) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ P)
    (hbase : Pbase ≤ P) (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp Pbase)
    (stride : I → ℕ) (hstride : ∀ i, 0 < stride i)
    (hstrideP : ∀ i, (stride i : ℝ) ≤ Real.exp Pbase)
    (H : I → ℝ) (hH : ∀ i, Real.exp ((P + k) ^ k) ≤ H i)
    (cells : Finset (ColumnResiduePattern Q I stride)) (hcells : cells.Nonempty)
    (W : Q × I → ℝ) (hW : ∀ z, 0 < W z) (hwidth : ∀ z, ρ * H z.2 ≤ W z) :
    0 < ∑' z, selectedResidueSmoothWeight stride cells W z := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : 3 * P + 8 ≤ (P + k) ^ k := by
    have hsquare : (P + 2) ^ 2 ≤ (P + k) ^ k :=
      (pow_le_pow_left₀ (by linarith) (by linarith) 2).trans
        (pow_le_pow_right₀ (by linarith) hk)
    exact (show 3 * P + 8 ≤ (P + 2) ^ 2 by nlinarith).trans hsquare
  have hebase := Real.exp_le_exp.mpr hbase
  have hinv : ρ⁻¹ ≤ Real.exp P := by simpa only [one_div] using hρP.trans hebase
  have hρlower : Real.exp (-P) ≤ ρ := by
    have h := (inv_le_inv₀ (Real.exp_pos P) (inv_pos.mpr hρ)).2 hinv
    simpa only [Real.exp_neg, inv_inv] using h
  have hHlarge (i : I) : Real.exp (3 * P + 8) ≤ H i :=
    (Real.exp_le_exp.mpr hpow).trans (hH i)
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    hprofile.trans (by linarith [Real.add_one_le_exp P])
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hwLarge (z : Q × I) : 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride W z := by
    have hq := (hstrideP z.2).trans hebase
    have hmul : 8 * (probabilityProfileLipschitz : ℝ) * (stride z.2 : ℝ) ≤ W z := by
      calc
        _ ≤ Real.exp 8 * Real.exp P * Real.exp P := by gcongr
        _ = Real.exp (-P) * Real.exp (3 * P + 8) := by
          simp only [← Real.exp_add]
          congr 1
          ring
        _ ≤ ρ * H z.2 := mul_le_mul hρlower (hHlarge z.2) (Real.exp_pos _).le hρ.le
        _ ≤ W z := hwidth z
    exact (le_div_iff₀ (Nat.cast_pos.mpr (hstride z.2))).2 hmul
  apply selectedResidueSmoothWeight_mass_pos stride cells hcells W hW
  intro r
  rw [← residueSmoothWeight_mass _ stride hstride W hW]
  exact shiftedSmoothProductMass_pos_of_large _ _ hwLarge

end Erdos3

end

end OAI
