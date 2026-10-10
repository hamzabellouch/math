import Mathlib
import OAI.Analysis.SymmetricDomains.MaximizerBundleBorel

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

lemma parameterPeak_log_norm {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {p z : Affine N}
    (hp : MvPolynomial.eval p P ≠ 0) (hz : MvPolynomial.eval z P ≠ 0) :
    Real.log ‖parameterPeak P a p z‖ =
      (parameterLogBase P z + (a z).re) - (parameterLogBase P p + (a p).re) - coordinateEnergy (z-p) := by
  rw [parameterPeak_norm,parameterPotential_eq_exp P a hz,parameterPotential_eq_exp P a hp,
    ← Real.exp_sub,← Real.exp_add,Real.log_exp]
  ring

lemma coordinateEnergy_sub_hasFDerivAt {N : ℕ} (p : Affine N) :
    HasFDerivAt (fun z => coordinateEnergy (z-p)) (0 : Affine N →L[ℝ] ℝ) p := by
  have h (i : Fin N) : HasFDerivAt (fun z : Affine N => ‖z i-p i‖^2) (0 : Affine N →L[ℝ] ℝ) p := by
    simpa using ((ContinuousLinearMap.proj i : Affine N →L[ℝ] ℂ).hasFDerivAt (x := p) |>.sub_const (p i)).norm_sq
  simpa only [coordinateEnergy,Pi.sub_apply,Finset.sum_const_zero,Finset.sum_apply] using
    HasFDerivAt.fun_sum (fun i (_hi : i ∈ Finset.univ) => h i)

theorem parameterPeak_log_norm_hasFDerivAt {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {p : Affine N} (hp : MvPolynomial.eval p P ≠ 0) :
    HasFDerivAt (fun z => Real.log ‖parameterPeak P a p z‖)
      (fderiv ℝ (parameterLogBase P) p + Complex.reCLM.comp (a.restrictScalars ℝ)) p := by
  have hb := (parameterLogBase_contDiffAt P hp (r := 1)).differentiableAt one_ne_zero
  have hd := ((hb.hasFDerivAt.add (Complex.reCLM.comp (a.restrictScalars ℝ)).hasFDerivAt).sub_const
    (parameterLogBase P p + (a p).re)).sub (coordinateEnergy_sub_hasFDerivAt p)
  simp only [sub_zero] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [(MvPolynomial.continuous_eval P).continuousAt.eventually_ne hp] with z hz
  exact parameterPeak_log_norm P a hp hz

theorem parameterPeak_log_differential {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {p : Affine N} (hp : MvPolynomial.eval p P ≠ 0) :
    AnalyticAt ℂ (fun z => Complex.log (parameterPeak P a p z)) p ∧
      Complex.log (parameterPeak P a p p) = 0 ∧
      Complex.reCLM.comp ((fderiv ℂ (fun z => Complex.log (parameterPeak P a p z)) p).restrictScalars ℝ) =
        fderiv ℝ (parameterLogBase P) p + Complex.reCLM.comp (a.restrictScalars ℝ) := by
  have hs := parameterPeak_self P a hp
  have hh : AnalyticAt ℂ (fun z => Complex.log (parameterPeak P a p z)) p :=
    (parameterPeak_analytic P a p p (mem_univ _)).clog (hs ▸ Complex.one_mem_slitPlane)
  refine ⟨hh,by rw [hs,Complex.log_one],?_⟩
  have hr := Complex.reCLM.hasFDerivAt.comp p (hh.differentiableAt.hasFDerivAt.restrictScalars ℝ)
  have he : (fun z => (Complex.log (parameterPeak P a p z)).re) =
      (fun z => Real.log ‖parameterPeak P a p z‖) := funext (fun _ => Complex.log_re _)
  change HasFDerivAt (fun z => (Complex.log (parameterPeak P a p z)).re) _ p at hr
  rw [he] at hr
  exact hr.unique (parameterPeak_log_norm_hasFDerivAt P a hp)

theorem prime_zeroLocus_fixed_charts {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ (d : ℕ) (Q : MvPolynomial (Fin n) ℂ), Q ∉ J ∧
      ∀ q ∈ MvPolynomial.zeroLocus ℂ J, MvPolynomial.eval q Q ≠ 0 →
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ J ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ J → Affine n) ⁻¹' W) ∧ q ∈ W ∧
          ∃ B : Set (Affine d), IsOpen B ∧ Nonempty (Biholomorph W B) := by
  obtain ⟨d,_,G,hG,hGi⟩ := exists_integral_inj_algHom_of_quotient J Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ J (G (MvPolynomial.X j))
  obtain ⟨D,r,hD,_,hs⟩ := normalization_analytic_sheets J G hG hGi P hP
  let Q := MvPolynomial.bind₁ P D
  have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.bind₁ P) = G := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using hP j
  have hQ : Q ∉ J := by
    intro hQ
    have he : (Ideal.Quotient.mkₐ ℂ J) Q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hQ
    change ((Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.bind₁ P)) D = 0 at he
    rw [hcomp] at he
    exact hD (hG (he.trans (map_zero G).symm))
  refine ⟨d,Q,hQ,fun q hq hqQ => ?_⟩
  let π : Affine n → Affine d := fun z j => MvPolynomial.eval z (P j)
  have hπ : AnalyticOnNhd ℂ π univ :=
    AnalyticOnNhd.pi (fun j => AnalyticOnNhd.eval_mvPolynomial (P j))
  have hqD : MvPolynomial.eval (π q) D ≠ 0 := by
    convert! hqQ using 1
    exact (MvPolynomial.aeval_bind₁ q P D).symm
  obtain ⟨I,g,A,_,hA,hqa,hg,hsheets⟩ := hs (π q) hqD
  obtain ⟨W,hWV,hW,hqW,B,hB,hWB⟩ :=
    finite_analytic_sheets_chart _ π hπ hA g hg hsheets hq hqa
  exact ⟨W,hWV,hW,hqW,B,hB,hWB⟩

end Release061

end

end OAI
