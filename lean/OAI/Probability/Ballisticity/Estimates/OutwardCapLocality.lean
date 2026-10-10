import Mathlib
import OAI.Probability.Ballisticity.Crossings.CanonicalHeightCutoff
import OAI.Probability.Ballisticity.Walk.FiniteOutwardRowApproximation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outward_canonical_cap_locality_of_log_bound {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) {A D B : ℝ} (hA : 0 < A) (hD : 0 < D) (hB : 0 < B)
    (hdata : ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ B ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ t : ℕ,
          0 < outwardKernelMass e f (t+1) x ω ∧
          -Real.log (outwardKernelMass e f (t+1) x ω) ≤
            A*Real.log ((t:ℝ)+2)+D*(W ω+1))) :
    ∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
      @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
      (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
      (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ := by
  obtain ⟨κ,hκ,hκae⟩ := environment_uniform_elliptic ν hue
  intro C ε δ hC hε hδ
  let M := Real.log (B/δ+1)
  have harg : 0 < B/δ+1 := by positivity
  have heM : Real.exp M = B/δ+1 := Real.exp_log harg
  have hprob : B/Real.exp M < δ := by
    apply (div_lt_iff₀ (Real.exp_pos M)).mpr
    rw [heM,mul_add,mul_one,mul_div_cancel₀ B hδ.ne']
    linarith
  obtain ⟨N,hN⟩ := exists_log_height_cutoff (D:=D) (M:=M) hA
  obtain ⟨R,hR⟩ := finite_outward_upper_row_approximation hκ e f A N hε hC.le
  refine ⟨R,?_⟩
  intro a x hx
  obtain ⟨F,hF,hFb,hFerr⟩ := hR a x hx
  refine ⟨F,hF,hFb,?_⟩
  obtain ⟨W,hW,hW0,hWi,hWB,hbound⟩ := hdata a x hx
  have hcut := canonical_height_cutoff_probability (environmentLaw ν) hA.le hD.le
    (fun n => outwardKernelMass e f (n+1) x) W hWi hWB
    (hbound.mono fun ω hω n => (hω n).2) N hN
  have hs : ∀ᵐ ω ∂environmentLaw ν,
      (ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|) →
      canonicalLogExcess A (fun n => outwardKernelMass e f (n+1) x) ω ≠
        finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω := by
    filter_upwards [hκae] with ω hω herr heq
    have hh := hFerr ω hω
    change ε < |min (canonicalLogExcess A (fun n => outwardKernelMass e f (n+1) x) ω) C-F ω| at herr
    rw [heq] at herr
    exact (not_lt_of_ge hh) herr
  have hm := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
  exact (hm.trans hcut).trans_lt hprob

theorem actual_outward_canonical_cap_locality {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε δ : ℝ, 0 < C → 0 < ε → 0 < δ → ∃ R : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∃ F : Environment d → ℝ,
      @Measurable _ _ (rowSigma (upperPairNeighborhood e a x R)) _ F ∧
      (∀ ω, 0 ≤ F ω ∧ F ω ≤ C) ∧
      (environmentLaw ν).real {ω | ε < |min (outwardCanonicalExcess e f A x ω) C-F ω|} < δ := by
  obtain ⟨A,D,B,hA,hD,hB,hdata⟩ := actual_outward_log_bound ν hue e f hef htrans
  exact ⟨A,hA,outward_canonical_cap_locality_of_log_bound ν hue e f hA hD hB hdata⟩
end DirectionalTransience

end

end

end OAI
