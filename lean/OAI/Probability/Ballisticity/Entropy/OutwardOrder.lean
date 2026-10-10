import Mathlib
import OAI.Probability.Ballisticity.Estimates.OutwardCapLocality

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outward_canonical_bound_of_log_bound {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) {A D B : ℝ} (hA : 0 < A) (hD : 0 < D) (hB : 0 < B)
    (hdata : ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            A*Real.log ((t:ℝ)+2)+D*(W ω+1))) :
    ∃ c B' : ℝ, 0 < c ∧ 0 < B' ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      let Z := outwardCanonicalExcess e f A x
      (∀ ω, 0 ≤ Z ω) ∧
      @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _ Z ∧
      Integrable (fun ω => Real.exp (c*Z ω)) (environmentLaw ν) ∧
      (∫ ω, Real.exp (c*Z ω) ∂environmentLaw ν) ≤ B' ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
        0 < outwardKernelMass e f (t+1) x ω ∧
        -Real.log (outwardKernelMass e f (t+1) x ω) ≤ 2*A*Real.log ((t:ℝ)+2)+Z ω) := by
  refine ⟨D⁻¹,Real.exp 1*B,inv_pos.mpr hD,mul_pos (Real.exp_pos _) hB,?_⟩
  intro a x hx
  obtain ⟨W,hW,hW0,hWi,hWB,hbound⟩ := hdata a x hx
  let Z := outwardCanonicalExcess e f A x
  have hZm : Measurable Z := measurable_outwardCanonicalExcess e f A x
  have hZbound : ∀ᵐ ω ∂environmentLaw ν, Z ω ≤ D*(W ω+1) ∧
      ∀ n, -Real.log (outwardKernelMass e f (n+1) x ω) ≤ 2*A*Real.log ((n:ℝ)+2)+Z ω := by
    filter_upwards [hbound] with ω hω
    exact canonicalLogExcess_bounds hA.le hD.le (hW0 ω) _ ω (fun n => (hω n).2)
  have hdom : Integrable (fun ω => Real.exp 1*Real.exp (W ω)) (environmentLaw ν) := hWi.const_mul _
  have hexp : ∀ᵐ ω ∂environmentLaw ν, Real.exp (D⁻¹*Z ω) ≤ Real.exp 1*Real.exp (W ω) := by
    filter_upwards [hZbound] with ω hω
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hω.1 (inv_nonneg.mpr hD.le)
    rw [←mul_assoc,inv_mul_cancel₀ hD.ne',one_mul] at hh
    linarith
  have hZi : Integrable (fun ω => Real.exp (D⁻¹*Z ω)) (environmentLaw ν) :=
    hdom.mono_nonneg (hZm.const_mul _ |>.exp |>.aestronglyMeasurable)
      (Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hexp
  refine ⟨fun ω => canonicalLogExcess_nonneg _ _ ω,outwardCanonicalExcess_upper_rows e f A a x hx,hZi,?_,?_⟩
  · calc
      _ ≤ ∫ ω, Real.exp 1*Real.exp (W ω) ∂environmentLaw ν := integral_mono_ae hZi hdom hexp
      _ = Real.exp 1*(∫ ω, Real.exp (W ω) ∂environmentLaw ν) := integral_const_mul _ _
      _ ≤ Real.exp 1*B := mul_le_mul_of_nonneg_left hWB (Real.exp_pos _).le
  · filter_upwards [hbound,hZbound] with ω hω hZω
    exact fun n => ⟨(hω n).1,hZω.2 n⟩

theorem actual_outward_order {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A c B : ℝ, 0 < A ∧ 0 < c ∧ 0 < B ∧
      (∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
        let Z := outwardCanonicalExcess e f A x
        (∀ ω, 0 ≤ Z ω) ∧
        @Measurable _ _ (rowSigma {y | a ≤ dot (realPosition y) (realPosition (step e))}) _ Z ∧
        Integrable (fun ω => Real.exp (c*Z ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (c*Z ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤ 2*A*Real.log ((t:ℝ)+2)+Z ω)) ∧
      (∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
        ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
        ∃ F : Environment d → ℝ,
          @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
          (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
          (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ) := by
  obtain ⟨A,D,B,hA,hD,hB,hdata⟩ := actual_outward_log_bound ν hue e f hef htrans
  obtain ⟨c,B',hc,hB',hbound⟩ := outward_canonical_bound_of_log_bound ν e f hA hD hB hdata
  exact ⟨A,c,B',hA,hc,hB',hbound,
    outward_canonical_cap_locality_of_log_bound ν hue e f hA hD hB hdata⟩

end DirectionalTransience

end

end

end OAI
