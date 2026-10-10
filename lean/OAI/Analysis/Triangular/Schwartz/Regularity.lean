import OAI.Analysis.Triangular.Schwartz.Gaussian

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma norm_two_sin_le (z : ℂ) : ‖2 * sin z‖ ≤ 2 * Real.exp |z.im| := by
  rw [Complex.two_sin, norm_mul, Complex.norm_I, mul_one]
  calc
    ‖exp (-z * I) - exp (z * I)‖ ≤ ‖exp (-z * I)‖ + ‖exp (z * I)‖ := norm_sub_le _ _
    _ = Real.exp z.im + Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _))
        (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = 2 * Real.exp |z.im| := by ring

def stripBound (R : ℝ) : ℝ := (2 * Real.exp (Real.pi * R / 36))^30

lemma stripBound_nonneg (R : ℝ) : 0 ≤ stripBound R := by unfold stripBound; positivity

lemma P_strip_bound (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) : ‖P s‖ ≤ stripBound R := by
  unfold P sineFactor
  rw [norm_prod]
  calc
    ∏ a : Fin 15, ‖(2 * sin ((kappa : ℂ) * (s-residue a)))^2‖ ≤
        ∏ _a : Fin 15, (2 * Real.exp (Real.pi * R / 36))^2 := by
      apply Finset.prod_le_prod₀ (by intros; positivity)
      intro a _
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      refine (norm_two_sin_le _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      have he : (((kappa : ℂ) * (s-residue a))).im = Real.pi * s.im / 36 := by
        simp [kappa, div_eq_mul_inv]; ring
      rw [he, abs_div, abs_mul, abs_of_pos Real.pi_pos]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 36)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs Real.pi_pos.le) (by norm_num)
    _ = stripBound R := by simp [stripBound, ← pow_mul]

lemma im_le_dist_int (w : ℂ) (n : ℤ) : |w.im| ≤ dist w (n : ℂ) := by
  simpa [dist_eq_norm] using Complex.abs_im_le_norm (w - (n : ℂ))

lemma uniform_basis_bound (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M := by
  let A := max R 2
  let M := stripBound A
  have hM : 0 ≤ M := stripBound_nonneg A
  refine ⟨M,hM,?_⟩
  intro n s hs
  have hmapP : Set.MapsTo P (Metric.ball (n.val : ℂ) 2) (Metric.closedBall (P n.val) M) := by
    intro w hw
    simp only [Metric.mem_closedBall, P_node, dist_zero_right]
    exact P_strip_bound A w ((im_le_dist_int w n.val).trans
      ((Metric.mem_ball.mp hw).le.trans (le_max_right _ _)))
  have hd : ∀ w ∈ Metric.ball (n.val : ℂ) 2, ‖dBasis n w‖ ≤ M/2 := by
    intro w hw
    exact Complex.norm_dslope_le_div_of_mapsTo_ball differentiable_P.differentiableOn hmapP hw
  have hmapD : Set.MapsTo (dBasis n) (Metric.ball (n.val : ℂ) 1)
      (Metric.closedBall (dBasis n n.val) (M/2)) := by
    intro w hw
    simp only [Metric.mem_closedBall, dBasis_node, dist_zero_right]
    apply hd w
    exact (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
  have hc : ∀ w ∈ Metric.ball (n.val : ℂ) 1, ‖cBasis n w‖ ≤ M/2 := by
    intro w hw
    simpa [cBasis] using Complex.norm_dslope_le_div_of_mapsTo_ball
      (differentiable_dBasis n).differentiableOn hmapD hw
  have hPs : ‖P s‖ ≤ M := P_strip_bound A s (hs.trans (le_max_left _ _))
  have hhalf : M/2 ≤ M := by linarith
  by_cases hnear : dist s (n.val : ℂ) < 1
  · exact ⟨(hc s hnear).trans hhalf,
      (hd s (lt_trans hnear (by norm_num : (1 : ℝ) < 2))).trans hhalf⟩
  · have hfar : 1 ≤ ‖s - (n.val : ℂ)‖ := by simpa [dist_eq_norm] using le_of_not_gt hnear
    have hne : s ≠ (n.val : ℂ) := by intro he; norm_num [he] at hfar
    rw [cBasis_eq n hne, dBasis_eq n hne, norm_div, norm_div, norm_pow]
    constructor
    · exact (div_le_self (norm_nonneg _) (one_le_pow₀ hfar)).trans hPs
    · exact (div_le_self (norm_nonneg _) hfar).trans hPs

def spectralBound (S : Fin 31 → ℂ) (R : ℝ) : ℝ :=
  ∑ j : Fin 31, ‖S j‖*Real.exp (|Real.pi*frequency j| *R)
lemma spectralBound_nonneg (S : Fin 31 → ℂ) (R : ℝ) : 0 ≤ spectralBound S R := by
  unfold spectralBound; positivity
lemma finiteSpectral_strip (S : Fin 31 → ℂ) (R : ℝ) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖∑ j : Fin 31, S j*exp (I*Real.pi*frequency j*s)‖ ≤ spectralBound S R := by
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hi : (I*Real.pi*frequency j*s).re = -(Real.pi*frequency j)*s.im := by simp
  rw [hi]
  calc
    -(Real.pi*frequency j)*s.im ≤ |-(Real.pi*frequency j)*s.im| := le_abs_self _
    _ = |Real.pi*frequency j| *|s.im| := by rw [abs_mul,abs_neg]
    _ ≤ |Real.pi*frequency j| *R := mul_le_mul_of_nonneg_left hs (abs_nonneg _)

lemma tail_summand_norm_bound (a : InputCoefficients) {R M : ℝ}
    (hM : ∀ (n : Node) (s : ℂ), |s.im| ≤ R → ‖cBasis n s‖ ≤ M ∧ ‖dBasis n s‖ ≤ M)
    (n : TailNode) (s : ℂ) (hs : |s.im| ≤ R) :
    ‖(a.tailC n:ℂ)*cBasis n.val s+(a.tailD n:ℂ)*dBasis n.val s‖ ≤
      (|a.tailC n|+|a.tailD n|)*M := by
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |a.tailC n| *M+|a.tailD n| *M :=
      add_le_add (mul_le_mul_of_nonneg_left (hM n.val s hs).1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hM n.val s hs).2 (abs_nonneg _))
    _ = _ := by ring

lemma differentiable_tailInput (a : InputCoefficients) : Differentiable ℂ (tailInput a) := by
  intro s
  obtain ⟨M,hM,hB⟩ := uniform_basis_bound (|s.im|+1)
  let U : Set ℂ := {w | |w.im| < |s.im|+1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hs : s ∈ U := by dsimp [U]; linarith
  have hd : DifferentiableOn ℂ
      (fun w => ∑' n : TailNode, ((a.tailC n:ℂ)*cBasis n.val w+(a.tailD n:ℂ)*dBasis n.val w)) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (a.summable.mul_right M)
    · intro n
      exact ((differentiable_cBasis n.val).const_mul _ |>.add
        ((differentiable_dBasis n.val).const_mul _)).differentiableOn
    · exact hU
    · intro n w hw
      exact tail_summand_norm_bound a hB n w (le_of_lt hw)
  exact ((differentiable_P s).const_mul _).add (hd.differentiableAt (hU.mem_nhds hs))

lemma tailInput_strip (a : InputCoefficients) (R : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, |s.im| ≤ R → ‖tailInput a s‖ ≤ M := by
  obtain ⟨M,hM,hB⟩ := uniform_basis_bound R
  refine ⟨|a.C| *stripBound R + ∑' n : TailNode, (|a.tailC n|+|a.tailD n|)*M,?_⟩
  intro s hs
  have hsum := (a.summable.mul_right M).of_norm_bounded
    (fun n => tail_summand_norm_bound a hB n s hs)
  unfold tailInput
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (P_strip_bound R s hs) (abs_nonneg a.C)
  · exact (norm_tsum_le_tsum_norm hsum.norm).trans
      (hsum.norm.tsum_le_tsum (fun n => tail_summand_norm_bound a hB n s hs) (a.summable.mul_right M))

lemma differentiable_finiteInput (a : InputCoefficients) : Differentiable ℂ (finiteInput a) := by
  unfold finiteInput
  apply Differentiable.fun_sum
  intro j _
  exact ((differentiable_finiteC _).const_mul _).add ((differentiable_finiteD _).const_mul _)

lemma finiteInput_strip (a : InputCoefficients) (R : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, |s.im| ≤ R → ‖finiteInput a s‖ ≤ M := by
  refine ⟨∑ j : Fin 11, (|a.finiteC j| *spectralBound (FiniteCertificate.cCoefficient ⟨j.val,by omega⟩) R +
    |a.finiteD j| *spectralBound (FiniteCertificate.dCoefficient ⟨j.val,by omega⟩) R), ?_⟩
  intro s hs
  unfold finiteInput
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [FiniteCertificate.finiteC_fourier,FiniteCertificate.finiteD_fourier]
  exact add_le_add (mul_le_mul_of_nonneg_left (finiteSpectral_strip _ R s hs) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (finiteSpectral_strip _ R s hs) (abs_nonneg _))

def inputSchwartz (a : InputCoefficients) : 𝓢(Plane,ℝ) :=
  Analysis.dampedEntireSchwartz (Real.pi*h*b) (mul_pos (mul_pos Real.pi_pos (by norm_num [h])) b_pos) b
    (tailInput a) (differentiable_tailInput a) (tailInput_strip a 1) +
  Analysis.dampedEntireSchwartz (Real.pi*H*b) (mul_pos (mul_pos Real.pi_pos (by norm_num [H])) b_pos) b
    (finiteInput a) (differentiable_finiteInput a) (finiteInput_strip a 1)

lemma inputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    inputSchwartz a x = Real.exp (-Real.pi*h*radial x)*(tailInput a (radial x)).re +
      Real.exp (-Real.pi*H*radial x)*(finiteInput a (radial x)).re := by
  simp only [inputSchwartz,add_apply,Analysis.dampedEntireSchwartz_apply,radial]
  push_cast
  congr 3 <;> ring

end AtomicTriangular.Construction
end

end OAI
