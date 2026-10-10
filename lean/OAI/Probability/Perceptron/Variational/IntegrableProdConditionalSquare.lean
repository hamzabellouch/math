import Mathlib
import OAI.Probability.Perceptron.Variational.PiMarkLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma integrable_prod_of_conditional_square {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G : X → ℝ} (hF : Measurable F) (hG : MemLp G 2 μ)
    (K : ℝ) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hb : ∀ x, (∫ y, (F (x,y)-G x)^2 ∂ν) ≤ K) : Integrable F (μ.prod ν) := by
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (hs x).integrable (by norm_num)),?_⟩
  have hi : Integrable (fun x => K+(G x)^2+1) μ :=
    ((integrable_const K).add hG.integrable_sq).add (integrable_const 1)
  apply hi.mono' hF.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
  have hi1 : Integrable (fun y => (F (x,y)-G x)^2) ν :=
    ((hs x).sub (memLp_const (G x))).integrable_sq
  have hi2 : Integrable (fun y => (F (x,y)-G x)^2+(G x)^2) ν := hi1.add (integrable_const _)
  calc
    _ ≤ ∫ y, (F (x,y)-G x)^2+(G x)^2+1 ∂ν := by
      apply integral_mono ((hs x).integrable (by norm_num)).norm
        (hi2.add (integrable_const 1))
      intro y
      change ‖F (x,y)‖ ≤ (F (x,y)-G x)^2+(G x)^2+1
      rw [Real.norm_eq_abs]
      have h1 := sq_nonneg (|F (x,y)-G x|-1)
      have h2 := sq_nonneg (|G x|-1)
      have ht : |F (x,y)| ≤ |F (x,y)-G x|+|G x| := by
        simpa using abs_sub_le (F (x,y)) (G x) 0
      nlinarith [sq_abs (F (x,y)-G x),sq_abs (G x)]
    _ = (∫ y, (F (x,y)-G x)^2 ∂ν)+(G x)^2+1 := by
      rw [integral_add hi2 (integrable_const 1),integral_add hi1 (integrable_const ((G x)^2))]
      simp
    _ ≤ K+(G x)^2+1 := by linarith [hb x]

lemma finiteCascade_terminal_log_second_moment_bound {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X) :
    MemLp (fun η => Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η))) 2 (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ∧
    (∫ η, (Real.log (decoratedTerminalTotal step H n (x,η) /
      decoratedTerminalTotal step (fun _ => 0) n (x,η))-finiteCascadeLogRecursion ν step n z H x)^2
      ∂decoratedCascadeLaw ν n z) ≤ cascadeLogFluctuationConstant n z := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_second_moment_bound ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x)

theorem canonical_coordinate_joint_mean (d : ℕ) (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) :
    let μ := (Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n))
    let F := fun p => canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)
    Integrable F μ ∧ (∫ p, F p ∂μ) = d*canonicalGaussianFreeValue σ n z r b := by
  let ν := decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 r)
  let F := fun p : (Fin d → ℝ)×DecoratedCascade (Fin d → ℝ) n =>
    canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)
  let P := quadraticCascadePrecision σ b n z
  let A := (d : ℝ)*(-Real.log b/2+quadraticCascadeOffset σ b n z)
  let G := fun x : Fin d → ℝ => A+(∑ i, (x i)^2)/(2*P)
  have hG : MemLp G 2 μ := by
    convert (memLp_const A).add ((gaussian_square_sum_memLp_two d r).mul_const (2*P)⁻¹) using 1
    ext x
    simp only [G,div_eq_mul_inv,Pi.add_apply]
  have hF : Measurable F := (canonicalCoordinateLog_measurable d n σ b z).comp
    ((Measurable.of_eval (fun i => Measurable.of_eval (fun _ =>
      (measurable_pi_apply i).comp measurable_fst))).prodMk measurable_snd)
  have hsec : ∀ x, MemLp (fun η => F (x,η)) 2 (ν : Measure _) ∧
      (∫ η, (F (x,η)-G x)^2 ∂ν) ≤ cascadeLogFluctuationConstant n z := by
    intro x
    have he := finiteCascade_terminal_log_second_moment_bound
      (piMarkLaw (fun _ : Fin d => standardGaussianMark)) (canonicalCoordinateStep d σ)
      (canonicalCoordinateStep_measurable d σ) n z hz hz0 hz1
      (canonicalCoordinatePotential_measurable d b) (canonical_coordinate_recursion d σ b n z hz0 hp).2
      (fun i _ => x i)
    rw [(canonical_coordinate_recursion d σ b n z hz0 hp).1 (fun i _ => x i)] at he
    exact he
  have hi : Integrable F (μ.prod ν) := integrable_prod_of_conditional_square μ ν hF hG
    (cascadeLogFluctuationConstant n z) (fun x => (hsec x).1) (fun x => (hsec x).2)
  refine ⟨hi,?_⟩
  change (∫ p, F p ∂μ.prod ν) = _
  rw [integral_prod _ hi]
  have he : ∀ x, (∫ η, F (x,η) ∂ν) = G x := by
    intro x
    exact canonical_coordinate_log_mean d σ b n z hz hz0 hz1 hp (fun i _ => x i)
  simp_rw [he]
  change (∫ x, A+(∑ i, (x i)^2)/(2*P) ∂μ) = _
  rw [integral_add (integrable_const A)
    ((gaussian_square_sum_memLp_two d r).integrable (by norm_num) |>.div_const (2*P)),integral_div]
  change (∫ _ : Fin d → ℝ, A ∂μ)+(∫ x : Fin d → ℝ, ∑ i, (x i)^2 ∂Measure.pi (fun _ => gaussianReal 0 r))/(2*P) = _
  rw [gaussian_square_sum_mean]
  simp only [integral_const,probReal_univ,one_smul]
  dsimp only [A,P,canonicalGaussianFreeValue]
  ring

lemma expected_eventually_gt_of_probability_lower
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hi : ∀ n, Integrable (X n) (μ n))
    (hn : ∀ n, 0 ≤ᵐ[μ n] X n) {c : ℝ}
    (hp : ∀ a : ℝ, a < c →
      Tendsto (fun n => (μ n).real {ω | a ≤ X n ω}) atTop (𝓝 1)) :
    ∀ b : ℝ, b < c → ∀ᶠ n in atTop, b < ∫ ω, X n ω ∂μ n := by
  intro b hb
  by_cases hb0 : b < 0
  · exact Eventually.of_forall fun n => hb0.trans_le (integral_nonneg_of_ae (hn n))
  · obtain ⟨a, hba, hac⟩ := exists_between hb
    have he := (hp a hac).const_mul a
    simp only [mul_one] at he
    have hev : ∀ᶠ n in atTop, b < a*(μ n).real {ω | a ≤ X n ω} :=
      he.eventually (lt_mem_nhds hba)
    filter_upwards [hev] with n hnb
    exact hnb.trans_le (mul_meas_ge_le_integral_of_nonneg (hn n) (hi n) a)

end SphericalPerceptronFreeEnergy

end

end OAI
