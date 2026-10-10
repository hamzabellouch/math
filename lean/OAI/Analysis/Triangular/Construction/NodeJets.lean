import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators Topology ComplexConjugate
namespace AtomicTriangular.Construction

lemma factor_second_third (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℂ) :
    iteratedDeriv 2 (fun s => (s-n)^2*g s) n = 2*g n ∧
    iteratedDeriv 3 (fun s => (s-n)^2*g s) n = 6*deriv g n := by
  have hp (k : ℕ) : iteratedDeriv k (fun s : ℂ => (s-n)^2) n =
      (2:ℕ).descFactorial k * (n-n)^(2-k) := by
    have hh := congrFun (iteratedDeriv_comp_sub_const k (fun s : ℂ => s^2) n) n
    exact hh.trans (iteratedDeriv_pow 2 k)
  have hpoly : ContDiff ℂ 3 (fun s : ℂ => (s-n)^2) := by fun_prop
  constructor
  · rw [iteratedDeriv_fun_mul (hpoly.of_le (by norm_num)).contDiffAt hg.contDiff.contDiffAt]
    simp [Finset.sum_range_succ,hp,iteratedDeriv_zero]
  · rw [iteratedDeriv_fun_mul hpoly.contDiffAt hg.contDiff.contDiffAt]
    norm_num [Finset.sum_range_succ,hp,iteratedDeriv_one]

lemma P_cBasis (n : Node) : P = fun s => (s-(n.val:ℂ))^2*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,P_node]
  · rw [cBasis_eq n hs]
    field_simp

lemma cBasis_at_node (n : Node) : (cBasis n n.val).re = Q n.val := by
  have hh := (factor_second_third (cBasis n) (differentiable_cBasis n) n.val).1
  rw [← P_cBasis n] at hh
  have he := congrArg Complex.re hh
  rw [← waveDerivative_eq_iterated] at he
  norm_num [Complex.mul_re] at he
  unfold Q
  linarith
lemma cBasis_deriv_at_node (n : Node) : 6*(deriv (cBasis n) n.val).re =
    (waveDerivative 3 n.val).re := by
  have hh := (factor_second_third (cBasis n) (differentiable_cBasis n) n.val).2
  rw [← P_cBasis n,← waveDerivative_eq_iterated] at hh
  have he := congrArg Complex.re hh
  simpa using he.symm

lemma dBasis_cBasis (n : Node) : dBasis n = fun s => (s-(n.val:ℂ))*cBasis n s := by
  funext s
  by_cases hs : s = (n.val:ℂ)
  · simp [hs,dBasis_node]
  · rw [dBasis_eq n hs,cBasis_eq n hs]
    field_simp
lemma deriv_dBasis_at_node (n : Node) : deriv (dBasis n) n.val = cBasis n n.val := by
  have hh := (((hasDerivAt_id (n.val:ℂ)).sub_const (n.val:ℂ)).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  rw [dBasis_cBasis n]
  simpa using! hh

lemma cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : cBasis n m.val = 0 := by
  rw [cBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]
lemma dBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) : dBasis n m.val = 0 := by
  rw [dBasis_eq n (by exact_mod_cast hmn),P_node,zero_div]

lemma deriv_cBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) :
    deriv (cBasis n) m.val = 0 := by
  have hh := ((((hasDerivAt_id (m.val:ℂ)).sub_const (n.val:ℂ)).pow 2).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  change deriv (fun s => (s-(n.val:ℂ))^2*cBasis n s) m.val = _ at hh
  rw [← P_cBasis n,deriv_P_node m,cBasis_other_node hmn] at hh
  have hne : ((m.val:ℂ)-(n.val:ℂ))^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (by exact_mod_cast hmn))
  have hzero : ((m.val:ℂ)-(n.val:ℂ))^2 * deriv (cBasis n) m.val = 0 := by simpa using hh.symm
  exact (mul_eq_zero.mp hzero).resolve_left hne
lemma deriv_dBasis_other_node {m n : Node} (hmn : m.val ≠ n.val) :
    deriv (dBasis n) m.val = 0 := by
  have hh := (((hasDerivAt_id (m.val:ℂ)).sub_const (n.val:ℂ)).mul
    ((differentiable_cBasis n _).hasDerivAt)).deriv
  change deriv (fun s => (s-(n.val:ℂ))*cBasis n s) m.val = _ at hh
  rw [← dBasis_cBasis n,cBasis_other_node hmn,deriv_cBasis_other_node hmn] at hh
  simpa using hh

end AtomicTriangular.Construction
end

end OAI
