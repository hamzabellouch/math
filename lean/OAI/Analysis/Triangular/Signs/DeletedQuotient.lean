import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

def deletedSecond (f : ℝ → ℝ) (m s : ℝ) : ℝ :=
  if s=m then iteratedDeriv 2 f m/2 else (f s-f m-deriv f m*(s-m))/(s-m)^2

def deleted (f : ℝ → ℝ) (m : ℝ) (ν : ℕ) (s : ℝ) : ℝ :=
  if ν=0 then f s else deletedSecond f m s

lemma taylor_one_eval {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    taylorWithinEval f 1 (uIcc m s) m s=f m+deriv f m*(s-m) := by
  have he : iteratedDerivWithin 1 f (uIcc m s) m=iteratedDeriv 1 f m :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hms)
      (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)
  rw [show (1:ℕ)=0+1 from rfl,taylorWithinEval_succ,he]
  simp [mul_comm]

lemma deletedSecond_eq_at_mean {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s : ℝ} (hms : m≠s) :
    ∃ c∈uIoo m s,deletedSecond f m s=iteratedDeriv 2 f c/2 := by
  obtain ⟨c,hc,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hms hf.contDiffOn
  refine ⟨c,hc,?_⟩
  rw [taylor_one_eval hf hms] at he
  have hn : s-m≠0 := sub_ne_zero.mpr hms.symm
  rw [deletedSecond,ite_eq_right hms.symm]
  norm_num at he
  apply (div_eq_iff (pow_ne_zero 2 hn)).mpr
  linarith

lemma deletedSecond_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {m s C : ℝ}
    (hb : ∀ t∈uIcc m s,|iteratedDeriv 2 f t|≤C) : |deletedSecond f m s|≤C/2 := by
  by_cases h : m=s
  · subst s
    rw [deletedSecond,ite_eq_left rfl,abs_div,show |(2:ℝ)|=2 by norm_num]
    exact div_le_div_of_nonneg_right (hb m (left_mem_uIcc)) (by norm_num)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf h
    rw [he,abs_div,show |(2:ℝ)|=2 by norm_num]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact hb c (Ioo_subset_Icc_self hc)

lemma deletedSecond_of_jets {f : ℝ → ℝ} {m s : ℝ} (hfm : f m=0) (hdfm : deriv f m=0)
    (hsm : s≠m) : deletedSecond f m s=f s/(s-m)^2 := by
  simp [deletedSecond,hsm,hfm,hdfm]

lemma real_function_nonneg_of_deleted {f : ℝ → ℝ} {m s : ℝ} (hfm : f m=0)
    (hdfm : deriv f m=0) (hb : 0≤deletedSecond f m s) : 0≤f s := by
  by_cases hsm : s=m
  · simp [hsm,hfm]
  · rw [deletedSecond_of_jets hfm hdfm hsm] at hb
    simpa only [zero_mul] using (le_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hsm))).mp hb
end AtomicTriangular.Construction
end

end OAI
