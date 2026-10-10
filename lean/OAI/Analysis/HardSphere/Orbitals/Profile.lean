import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Chi2
import OAI.Analysis.HardSphere.Geometry.RealComp

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def profile (h t : ℝ) : ℝ := 1-Real.smoothTransition (t/h-1)

lemma profile_smooth (h : ℝ) : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (profile h) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const h).sub contDiff_const))

lemma profile_bounds (h t : ℝ) : 0 ≤ profile h t ∧ profile h t ≤ 1 := by
  unfold profile
  constructor <;> linarith [Real.smoothTransition.nonneg (t/h-1),Real.smoothTransition.le_one (t/h-1)]

lemma profile_one {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t ≤ h) : profile h t=1 := by
  rw [profile,Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos]; exact (div_le_one hh).mpr ht)]
  ring

lemma profile_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : 2*h ≤ t) : profile h t=0 := by
  rw [profile,Real.smoothTransition.one_of_one_le (by have hd := (le_div_iff₀ hh).mpr ht; linarith)]
  ring

lemma profile_deriv (h t : ℝ) : deriv (profile h) t= -deriv Real.smoothTransition (t/h-1)/h := by
  have hd := (transition_derivative (t/h-1)).comp t (((hasDerivAt_id t).div_const h).sub_const 1)
  have he := hd.const_sub 1
  have heq : (fun x : ℝ ↦ 1 - (Real.smoothTransition ∘ fun x : ℝ ↦ id x / h - 1) x) = profile h := rfl
  rw [heq] at he
  rw [he.deriv]
  ring

lemma profile_deriv_zero {h : ℝ} (hh : 0<h) {t : ℝ} (ht : t∉Icc h (2*h)) :
    deriv (profile h) t=0 := by
  rw [profile_deriv,transition_deriv_eq_zero]
  · simp
  · intro hc
    apply ht
    constructor
    · have hd := hc.1
      have hv : 1 ≤ t/h := by linarith
      exact (one_le_div hh).mp hv
    · have hv : t/h ≤ 2 := by linarith [hc.2]
      exact (div_le_iff₀ hh).mp hv

lemma profile_deriv_bound {h M : ℝ} (hh : 0<h) (_hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (t : ℝ) :
    |deriv (profile h) t| ≤ M/h := by
  rw [profile_deriv,abs_div,abs_neg,abs_of_pos hh]
  exact div_le_div_of_nonneg_right (hb _) hh.le

def cutoff (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ) : SmoothMultiplier n L :=
  (countMultiplier n L δ x).realComp (profile h) (profile_smooth h)

lemma cutoff_apply (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ) (X : Configuration n L) :
    (cutoff n L δ x h).toFun X=(profile h (count L δ x X) : ℂ) := by
  change (profile h ((countMultiplier n L δ x).toFun X).re : ℂ)=_
  rw [countMultiplier_apply,Complex.ofReal_re]

lemma cutoff_real (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ) (X : Configuration n L) :
    conj ((cutoff n L δ x h).toFun X)=(cutoff n L δ x h).toFun X := by
  rw [cutoff_apply,Complex.conj_ofReal]

lemma cutoff_partial (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (h : ℝ)
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (cutoff n L δ x h).toFun p X=
      ((deriv (profile h) (count L δ x X) : ℝ) : ℂ)*coordDerivative n L (countMultiplier n L δ x).toFun p X := by
  rw [cutoff,SmoothMultiplier.partial_realComp _ _ _ (countMultiplier_real n L δ x),
    countMultiplier_apply,Complex.ofReal_re]

lemma cutoff_gradient_le {n : ℕ} {L : Length} {δ h M : ℝ} (hδ : 0<δ) (hh : 0<h) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (cutoff n L δ x h).toFun p X‖^2) ≤
      (2*M^2*(3*(4*(24*Real.pi^2*M^2/(8*δ)^2))))/h := by
  by_cases ht : count L δ x X∈Icc h (2*h)
  · simp_rw [cutoff_partial,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [← Finset.mul_sum]
    have hb2 : (deriv (profile h) (count L δ x X))^2 ≤ (M/h)^2 := by
      rw [← sq_abs (deriv _ _)]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (profile_deriv_bound hh hM hb _)
    calc
      _ ≤ (M/h)^2*((3*(4*(24*Real.pi^2*M^2/(8*δ)^2)))*count L δ x X) :=
        mul_le_mul hb2 (countMultiplier_gradient_le hδ hM hb x X)
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
      _ ≤ (M/h)^2*((3*(4*(24*Real.pi^2*M^2/(8*δ)^2)))*(2*h)) := by gcongr; try exact ht.2
      _ = _ := by field_simp
  · simp_rw [cutoff_partial,profile_deriv_zero hh ht,Complex.ofReal_zero,zero_mul,norm_zero,
      zero_pow (by norm_num : 2≠0),Finset.sum_const_zero]
    positivity

end HardSphere.CellOrbital

end

end OAI
