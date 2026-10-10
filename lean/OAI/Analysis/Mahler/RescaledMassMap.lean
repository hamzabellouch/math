import OAI.Analysis.Mahler.RescaledHolomorphic
import OAI.Analysis.Mahler.MassTarget
import Mathlib.Analysis.Analytic.Polynomial

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology
variable {n N m : ℕ}

noncomputable def leadingComponent (G : Fin N → MvPolynomial (Fin n) ℂ)
    (j : Fin N) (z : Mahler.ComplexEuclidean n) : ℂ :=
  MvPolynomial.eval (fun i => z i) (G j)

lemma leadingComponent_differentiable (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N) :
    Differentiable ℂ (leadingComponent G j) := by
  intro x
  exact (AnalyticAt.aeval_mvPolynomial
    (fun i : Fin n => (EuclideanSpace.proj (𝕜 := ℂ) i).analyticAt x) (G j)).differentiableAt

lemma homogeneous_eval_scale {p : MvPolynomial (Fin n) ℂ} (hp : p.IsHomogeneous m)
    (z : Fin n → ℂ) (c : ℂ) :
    MvPolynomial.eval (fun i => c*z i) p = c^m * MvPolynomial.eval z p := by
  classical
  simp only [MvPolynomial.eval_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,← hp.degree_eq_sum_deg_support hd]
  ring

lemma leadingComponent_scale (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N)
    (hG : (G j).IsHomogeneous m) (ε : ℝ) (z : Mahler.ComplexEuclidean n) :
    leadingComponent G j (ε • z) = (ε^m) • leadingComponent G j z := by
  simpa only [leadingComponent,PiLp.smul_apply,Complex.real_smul,Complex.ofReal_pow] using!
    homogeneous_eval_scale hG (fun i => z i) (ε : ℂ)

lemma leadingComponent_zero (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N)
    (hG : (G j).IsHomogeneous m) (hm : 0 < m) : leadingComponent G j 0 = 0 := by
  simpa only [zero_smul,zero_pow (Nat.ne_of_gt hm)] using leadingComponent_scale G j hG 0 0

noncomputable def taylorRemainder (f : Fin N → Mahler.ComplexEuclidean n → ℂ)
    (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N) (z : Mahler.ComplexEuclidean n) : ℂ :=
  f j z - leadingComponent G j z

lemma source_remainder_bound {U : Set (Mahler.ComplexEuclidean n)}
    {f : Fin N → Mahler.ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    taylorRemainder f G j =O[𝓝[≠] 0] (fun z : Mahler.ComplexEuclidean n => ‖z‖^(m+1)) := by
  have hc := (EuclideanSpace.proj (𝕜 := ℂ) j).isBigO_comp
    (fun z => (WithLp.toLp 2 (fun j => f j z - MvPolynomial.eval (fun i => z i) (G j)) :
      Mahler.ComplexEuclidean N)) (𝓝[≠] (0 : Mahler.ComplexEuclidean n))
  exact hc.trans h.taylor_remainder

lemma source_remainder_zero {U : Set (Mahler.ComplexEuclidean n)}
    {f : Fin N → Mahler.ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) : taylorRemainder f G j 0 = 0 := by
  have hf := (h.isolated_zero 0 h.zero_mem).mpr rfl
  simp only [taylorRemainder,hf j,leadingComponent_zero G j (h.homogeneous j) (by have hm := h.degree_pos; omega),sub_self]

/-- The literal mass hypotheses imply uniform convergence of every remainder
jet through order two on a fixed closed neighborhood of the unit sphere. -/
theorem source_remainder_uniform_C2 {U : Set (Mahler.ComplexEuclidean n)}
    {f : Fin N → Mahler.ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    TendstoUniformlyOn (fun ε : ℝ => rescale (taylorRemainder f G j) m ε) (fun _ => 0)
      (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (rescale (taylorRemainder f G j) m ε))
      (fun _ => 0) (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale (taylorRemainder f G j) m ε)))
      (fun _ => 0) (𝓝[>] 0) (closedBall 0 2) := by
  exact rescaled_holomorphic_remainder_uniform_C2 h.open_domain h.zero_mem
    ((h.holomorphic j).sub (leadingComponent_differentiable G j).differentiableOn)
    (source_remainder_zero h j) (source_remainder_bound h j)

lemma rescaled_source_remainder {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (hG : ∀ j, (G j).IsHomogeneous m)
    {ε : ℝ} (hε : ε ≠ 0) (j : Fin N) :
    rescale (taylorRemainder f G j) m ε =
      fun z => rescale (f j) m ε z - leadingComponent G j z := by
  funext z
  simp only [rescale,taylorRemainder,smul_sub,leadingComponent_scale G j (hG j) ε z,
    inv_smul_smul₀ (pow_ne_zero m hε)]

end MahlerRescaling

end OAI
