import OAI.NumberTheory.Jacobsthal.Probability.RieszKernelBounds

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology

lemma riesz_scale_cpow {n X : ℝ} (hn : 0 < n) (hX : 0 < X) (s : ℂ) :
    ((n/X:ℝ):ℂ)^(-s) = (X:ℂ)^s/(n:ℂ)^s := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hrC : ((n/X:ℝ):ℂ) ≠ 0 := by exact_mod_cast (div_pos hn hX).ne'
  have hl : Complex.log ((n/X:ℝ):ℂ) = Complex.log (n:ℂ)-Complex.log (X:ℂ) := by
    rw [← Complex.ofReal_log (div_pos hn hX).le,Real.log_div hn.ne' hX.ne',
      Complex.ofReal_sub,Complex.ofReal_log hn.le,Complex.ofReal_log hX.le]
  rw [Complex.cpow_def_of_ne_zero hrC,Complex.cpow_def_of_ne_zero hXC,
    Complex.cpow_def_of_ne_zero hnC,← Complex.exp_sub,hl]
  congr 1
  ring

noncomputable def rieszDirichletTerm (f : ℕ → ℂ) (sigma X : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n *
    rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) * (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)

lemma norm_rieszDirichletTerm (f : ℕ → ℂ) (sigma : ℝ) {X : ℝ} (hX : 0 < X)
    (n : ℕ) (t : ℝ) :
    ‖rieszDirichletTerm f sigma X n t‖ =
      ‖LSeries.term f (sigma:ℂ) n‖ * X^sigma * ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
  have ht : ‖LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n‖ = ‖LSeries.term f (sigma:ℂ) n‖ := by
    simp only [LSeries.norm_term_eq,hre,Complex.ofReal_re]
  unfold rieszDirichletTerm
  rw [norm_mul,norm_mul,ht,Complex.norm_cpow_eq_rpow_re_of_pos hX,hre]
  ring

lemma rieszDirichletTerm_eq_scaled (f : ℕ → ℂ) (hf0 : f 0 = 0) (sigma : ℝ)
    {X : ℝ} (hX : 0 < X) (n : ℕ) (t : ℝ) :
    rieszDirichletTerm f sigma X n t = f n *
      (((n:ℝ)/X:ℝ):ℂ)^(-((sigma:ℂ)+(t:ℂ)*Complex.I)) *
        rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) := by
  by_cases hn : n=0
  · simp [rieszDirichletTerm,hn,hf0]
  · unfold rieszDirichletTerm
    rw [LSeries.term_of_ne_zero hn,riesz_scale_cpow (by exact_mod_cast Nat.pos_of_ne_zero hn) hX]
    simp only [div_eq_mul_inv]
    push_cast
    ring

lemma continuous_rieszDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hs : 1/2 ≤ sigma) (hX : 0 < X) (n : ℕ) :
    Continuous (rieszDirichletTerm f sigma X n) := by
  by_cases hn : n=0
  · subst n
    unfold rieszDirichletTerm
    simp only [LSeries.term_zero,zero_mul]
    exact continuous_const
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    have hXC : (X:ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    have hnp : Continuous (fun t:ℝ => (n:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      fun_prop (disch := exact Or.inl hnC)
    have hXp : Continuous (fun t:ℝ => (X:ℂ)^((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
      fun_prop (disch := exact Or.inl hXC)
    have hterm : Continuous (fun t:ℝ => LSeries.term f ((sigma:ℂ)+(t:ℂ)*Complex.I) n) := by
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnp (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
    exact (hterm.mul (continuous_rieszKernel_line hs)).mul hXp

lemma integrable_rieszDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hs : 1/2 ≤ sigma) (hX : 0 < X) (n : ℕ) :
    Integrable (rieszDirichletTerm f sigma X n) := by
  have hg := (integrable_rieszKernel_line hs).norm.const_mul
    (‖LSeries.term f (sigma:ℂ) n‖ * X^sigma)
  apply hg.mono' (continuous_rieszDirichletTerm f hs hX n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (norm_rieszDirichletTerm f sigma hX n t).le)

lemma integral_norm_rieszDirichletTerm (f : ℕ → ℂ) {sigma X : ℝ}
    (hX : 0 < X) (n : ℕ) :
    (∫ t:ℝ, ‖rieszDirichletTerm f sigma X n t‖) =
      ‖LSeries.term f (sigma:ℂ) n‖ * X^sigma *
        ∫ t:ℝ, ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by
  simp_rw [norm_rieszDirichletTerm f sigma hX n]
  exact integral_const_mul _ _

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
