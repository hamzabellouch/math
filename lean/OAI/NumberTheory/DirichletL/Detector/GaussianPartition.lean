import OAI.NumberTheory.DirichletL.Detector.GaussianCompletion
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))
lemma gaussianAnnulus_compact : HasCompactSupport gaussianAnnulus := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianAnnulus y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianAnnulus_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianAnnulus_large y (le_of_lt (lt_of_not_ge h)))

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

lemma gaussianAnnulus_support_scales (x : ℝ) (K : ℕ)
    (hlo : (2:ℝ)^K≤x) (hhi : x<(2:ℝ)^(K+1)) (j : ℕ) (hj : j∉({K,K+1}:Finset ℕ)) :
    gaussianAnnulus (x/(2:ℝ)^j)=0 := by
  have hp : (0:ℝ)<2^j := by positivity
  have hj' : j≠K ∧ j≠K+1 := by simpa using hj
  by_cases hlt : j<K
  · apply gaussianAnnulus_large
    apply (le_div_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1≤K by omega)
    rw [pow_succ] at h
    linarith
  · apply gaussianAnnulus_small
    apply (div_le_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+2≤j by omega)
    have he : (2:ℝ)^(K+2)=2*((2:ℝ)^(K+1)) := by rw [pow_succ]; ring
    rw [he] at h
    linarith

lemma gaussianAnnulus_partition (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j)) 1 := by
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have h : HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j))
      (∑j∈({K,K+1}:Finset ℕ),gaussianAnnulus (x/(2:ℝ)^j)) :=
    hasSum_sum_of_ne_finset_zero (gaussianAnnulus_support_scales x K hlo hhi)
  convert h using 1
  rw [Finset.sum_pair (by omega : K≠K+1)]
  unfold gaussianAnnulus annularCutoff
  have he : 2*(x/(2:ℝ)^(K+1))=x/(2:ℝ)^K := by rw [pow_succ]; field_simp
  have hh : 2≤2*(x/(2:ℝ)^K) := by
    have hq : 1≤x/(2:ℝ)^K := (one_le_div (by positivity)).mpr hlo
    linarith
  rw [he,gaussianCutoff_small _ ((div_le_one (by positivity)).mpr hhi.le),
    gaussianCutoff_large _ hh]
  ring

lemma gaussianAnnulus_partition_norm (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>‖gaussianAnnulus (x/(2:ℝ)^j)‖) 1 := by
  simpa only [gaussianAnnulus_norm,Complex.one_re] using
    Complex.hasSum_re (gaussianAnnulus_partition x hx)

end SevenEighths.ProbePhysical
end

end OAI
