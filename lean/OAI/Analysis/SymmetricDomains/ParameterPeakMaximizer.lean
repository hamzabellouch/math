import Mathlib
import OAI.Analysis.SymmetricDomains.DiscRelationCompactLocal

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
namespace Release061
open Set Complex Filter Metric
open scoped Topology
def parameterPotential {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (q : Affine n) : ℝ :=
  ‖MvPolynomial.eval q P‖ * Real.exp (coordinateEnergy q + (a q).re)

def parameterPeak {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p q : Affine n) : ℂ :=
  (MvPolynomial.eval q P / MvPolynomial.eval p P) *
    Complex.exp (peakLinear p q + a (q-p))

theorem parameterPeak_norm {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p q : Affine n) :
    ‖parameterPeak P a p q‖ =
      parameterPotential P a q / parameterPotential P a p *
        Real.exp (-coordinateEnergy (q-p)) := by
  simp only [parameterPeak,norm_mul,norm_div,Complex.norm_exp,Complex.add_re,
    peakLinear_re,map_sub,Complex.sub_re,parameterPotential]
  rw [show coordinateEnergy q-coordinateEnergy p-coordinateEnergy (q-p)+
      ((a q).re-(a p).re) = (coordinateEnergy q+(a q).re)-
        (coordinateEnergy p+(a p).re)-coordinateEnergy (q-p) by ring,
    Real.exp_sub,Real.exp_sub,Real.exp_neg]
  ring

theorem parameterPeak_analytic {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p : Affine n) :
    AnalyticOnNhd ℂ (parameterPeak P a p) univ := by
  intro q _
  have hsub : AnalyticAt ℂ (fun x : Affine n => x-p) q := analyticAt_id.sub analyticAt_const
  have ha := (a.analyticAt (q-p)).comp (f := fun x : Affine n => x-p) (x := q) hsub
  exact (((AnalyticOnNhd.eval_mvPolynomial P) q (mem_univ _)).mul analyticAt_const).mul
    (((peakLinear_analytic p q (mem_univ _)).add
      ha).cexp)

theorem parameterPeak_self {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {p : Affine n} (hp : MvPolynomial.eval p P ≠ 0) :
    parameterPeak P a p p = 1 := by simp [parameterPeak,peakLinear,hp]

theorem parameterPeak_bound {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {K : Set (Affine n)} {p : Affine n}
    (hp : MvPolynomial.eval p P ≠ 0) (hmax : IsMaxOn (parameterPotential P a) K p) :
    ∀ q ∈ K, ‖parameterPeak P a p q‖ ≤ Real.exp (-(dist q p)^2) := by
  intro q hq
  rw [parameterPeak_norm]
  have hpp : 0 < parameterPotential P a p :=
    mul_pos (norm_pos_iff.mpr hp) (Real.exp_pos _)
  have hh := (div_le_one hpp).mpr (hmax hq)
  calc
    _ ≤ 1 * Real.exp (-coordinateEnergy (q-p)) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ ≤ Real.exp (-(dist q p)^2) := by
      rw [one_mul,dist_eq_norm]
      exact Real.exp_le_exp.mpr (neg_le_neg (sq_norm_le_coordinateEnergy _))

theorem exists_parameterPeak_maximizer {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {K : Set (Affine n)} (hK : IsCompact K)
    (hne : ∃ q ∈ K, MvPolynomial.eval q P ≠ 0) :
    ∃ p ∈ K, MvPolynomial.eval p P ≠ 0 ∧ IsMaxOn (parameterPotential P a) K p := by
  have hw : Continuous (parameterPotential P a) :=
    (MvPolynomial.continuous_eval P).norm.mul
      (Real.continuous_exp.comp (coordinateEnergy_continuous.add
        (Complex.continuous_re.comp a.continuous)))
  obtain ⟨q,hq,hqP⟩ := hne
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn ⟨q,hq⟩ hw.continuousOn
  refine ⟨p,hp,?_,hmax⟩
  have hpw : 0 < parameterPotential P a p :=
    (mul_pos (norm_pos_iff.mpr hqP) (Real.exp_pos _)).trans_le (hmax hq)
  intro hzero
  simp [parameterPotential,hzero] at hpw

end Release061

end

end OAI
