import Mathlib
import OAI.Probability.Ballisticity.Walk.OutwardCanonicalRows

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma measurable_finiteLogExcess {Ω : Type*} [MeasurableSpace Ω]
    (A : ℝ) (p : ℕ → Ω → ℝ) (hp : ∀ n, Measurable (p n)) (N : ℕ) :
    Measurable (finiteLogExcess A p N) := by
  unfold finiteLogExcess
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro n
  exact ((hp n).log.neg.sub_const _).ennreal_ofReal

lemma exists_log_height_cutoff {A D M : ℝ} (hA : 0 < A) :
    ∃ N : ℕ, D*(M+1) ≤ A*Real.log ((N:ℝ)+2) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp (D*(M+1)/A))
  refine ⟨N,?_⟩
  have hh : Real.exp (D*(M+1)/A) ≤ (N:ℝ)+2 := by linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hlog
  simpa only [mul_comm A] using (div_le_iff₀ hA).mp hlog

lemma canonical_height_cutoff_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A D B M : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (p : ℕ → Ω → ℝ) (W : Ω → ℝ)
    (hWi : Integrable (fun ω => Real.exp (W ω)) μ)
    (hWB : (∫ ω, Real.exp (W ω) ∂μ) ≤ B)
    (hp : ∀ᵐ ω ∂μ, ∀ n, -Real.log (p n ω) ≤ A*Real.log ((n:ℝ)+2)+D*(W ω+1))
    (N : ℕ) (hN : D*(M+1) ≤ A*Real.log ((N:ℝ)+2)) :
    μ.real {ω | canonicalLogExcess A p ω ≠ finiteLogExcess A p N ω} ≤ B/Real.exp M := by
  have hsub : ∀ᵐ ω ∂μ, (canonicalLogExcess A p ω ≠ finiteLogExcess A p N ω) →
      Real.exp M ≤ Real.exp (W ω) := by
    filter_upwards [hp] with ω hω hne
    apply Real.exp_le_exp.mpr
    by_contra hh
    exact hne (canonicalLogExcess_eq_finite hA hD (le_of_lt (lt_of_not_ge hh)) p ω hω N hN)
  have hle := measure_mono_ae hsub
  have hr : μ.real {ω | canonicalLogExcess A p ω ≠ finiteLogExcess A p N ω} ≤
      μ.real {ω | Real.exp M ≤ Real.exp (W ω)} := ENNReal.toReal_mono (measure_ne_top _ _) hle
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => (Real.exp_pos (W ω)).le)) hWi (Real.exp M)
  apply hr.trans
  apply (le_div_iff₀ (Real.exp_pos M)).mpr
  have hm' : μ.real {ω | Real.exp M ≤ Real.exp (W ω)} * Real.exp M ≤
      ∫ ω, Real.exp (W ω) ∂μ := by simpa only [mul_comm] using hm
  exact hm'.trans hWB

theorem actual_outward_finite_height_approximation {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A D B : ℝ, 0 < A ∧ 0 < D ∧ 0 < B ∧ ∀ M : ℝ, ∃ N : ℕ,
      ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      (environmentLaw ν).real {ω | outwardCanonicalExcess e f A x ω ≠
        finiteLogExcess A (fun n => outwardKernelMass e f (n+1) x) N ω} ≤ B/Real.exp M := by
  obtain ⟨A,D,B,hA,hD,hB,hdata⟩ := actual_outward_log_bound ν hue e f hef htrans
  refine ⟨A,D,B,hA,hD,hB,?_⟩
  intro M
  obtain ⟨N,hN⟩ := exists_log_height_cutoff (D:=D) (M:=M) hA
  refine ⟨N,?_⟩
  intro a x hx
  obtain ⟨W,hW,hW0,hWi,hWB,hbound⟩ := hdata a x hx
  apply canonical_height_cutoff_probability (environmentLaw ν) hA.le hD.le _ W hWi hWB _ N hN
  exact hbound.mono fun ω hω n => (hω n).2
end DirectionalTransience

end

end

end OAI
