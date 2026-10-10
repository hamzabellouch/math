import Mathlib
import OAI.Probability.SphericalField.Cascade.Coordinates

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
theorem canonical_coordinate_converges (σ : ℕ → ℝ) (b : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (r : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ =>
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n)))
        {p | ε*(d : ℝ) ≤ |canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-
          d*canonicalGaussianFreeValue σ n z r b|}) atTop (𝓝 0) := by
  have hd : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun d : ℕ => (ε*(d : ℝ)/2)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      ((hd.const_mul_atTop hε).atTop_div_const (by norm_num))
  have hu : Tendsto (fun d : ℕ => (d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2) atTop atTop :=
    hd.atTop_mul_const (sq_pos_of_pos (mul_pos hε hp))
  have ht0 : Tendsto (fun d : ℕ => cascadeLogFluctuationConstant n z/(ε*(d : ℝ)/2)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hu0 : Tendsto (fun d : ℕ => variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
      ((d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hu
  have hsum : Tendsto (fun d : ℕ => ENNReal.ofReal (cascadeLogFluctuationConstant n z/(ε*(d : ℝ)/2)^2)+
      ENNReal.ofReal (variance (fun y : ℝ => y^2) (gaussianReal 0 r)/
        ((d : ℝ)*(ε*quadraticCascadePrecision σ b n z)^2))) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal ht0).add (ENNReal.tendsto_ofReal hu0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [eventually_gt_atTop 0] with d hdpos
    exact canonical_coordinate_joint_deviation_le d hdpos σ b n z hz hz0 hz1 hp r hε

lemma exponential_ratio_converges {Ω : ℕ → Type} [∀ d, MeasurableSpace (Ω d)] (μ : ∀ d, Measure (Ω d))
    (X Y : ∀ d, Ω d → ℝ) (x y a : ℝ) (hrate : y-x < a)
    (hX : ∀ ε > 0, Tendsto (fun d => μ d {p | ε*(d : ℝ) ≤ |X d p-d*x|}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun d => μ d {p | ε*(d : ℝ) ≤ |Y d p-d*y|}) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun d => μ d {p | ρ ≤ Real.exp (Y d p-X d p-(d : ℝ)*a)}) atTop (𝓝 0) := by
  let ε := (a-(y-x))/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ht : Tendsto (fun d : ℕ => ε*(d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hε
  have he : ∀ᶠ d : ℕ in atTop, -Real.log ρ < ε*(d : ℝ) := ht.eventually (eventually_gt_atTop _)
  have hb : ∀ᶠ d : ℕ in atTop,
      μ d {p | ρ ≤ Real.exp (Y d p-X d p-(d : ℝ)*a)} ≤
        μ d {p | ε*(d : ℝ) ≤ |X d p-d*x|}+μ d {p | ε*(d : ℝ) ≤ |Y d p-d*y|} := by
    filter_upwards [he,eventually_gt_atTop 0] with d hd hdpos
    apply le_trans (measure_mono (t :=
      {p | ε*(d : ℝ) ≤ |X d p-d*x|} ∪ {p | ε*(d : ℝ) ≤ |Y d p-d*y|}) ?_) (measure_union_le _ _)
    intro p hp
    by_contra hh
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_le] at hh
    have hx := (abs_lt.mp hh.1).1
    have hy := (abs_lt.mp hh.2).2
    have hp' : Real.log ρ ≤ Y d p-X d p-(d : ℝ)*a := by
      simpa only [Real.log_exp] using Real.log_le_log hρ hp
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
    have ha : a = y-x+4*ε := by dsimp [ε]; ring
    rw [ha] at hp'
    nlinarith
  have hs := (hX ε hε).add (hY ε hε)
  simp only [add_zero] at hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Eventually.of_forall (fun _ => bot_le)) hb

theorem canonical_ratio_converges (σ : ℕ → ℝ) (b b' a : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z)
    (hp' : 0 < quadraticCascadePrecision σ b' n z) (r : ℝ≥0)
    (hrate : canonicalGaussianFreeValue σ n z r b'-canonicalGaussianFreeValue σ n z r b < a)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun d : ℕ =>
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 r)).prod
        (decoratedCascadeLaw (piMarkLaw (fun _ : Fin d => standardGaussianMark)) n z :
          Measure (DecoratedCascade (Fin d → ℝ) n)))
        {p | ρ ≤ Real.exp
          (canonicalCoordinateLog d n σ b' ((fun i _ => p.1 i),p.2)-
            canonicalCoordinateLog d n σ b ((fun i _ => p.1 i),p.2)-(d : ℝ)*a)}) atTop (𝓝 0) := by
  apply exponential_ratio_converges _ _ _ _ _ _ hrate
  · exact fun ε hε => canonical_coordinate_converges σ b n z hz hz0 hz1 hp r hε
  · exact fun ε hε => canonical_coordinate_converges σ b' n z hz hz0 hz1 hp' r hε
  · exact hρ

lemma canonical_stationary_tail_rates (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (r b : ℝ) (hp : 0 < quadraticCascadePrecision σ b n z)
    (hstat : -1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-
      r/(2*(quadraticCascadePrecision σ b n z)^2) = -1/2)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧
      0 < quadraticCascadePrecision σ (b-δ) n z ∧
      0 < quadraticCascadePrecision σ (b+δ) n z ∧
      canonicalGaussianFreeValue σ n z r (b-δ)-canonicalGaussianFreeValue σ n z r b < δ*(1+ε)/2 ∧
      canonicalGaussianFreeValue σ n z r (b+δ)-canonicalGaussianFreeValue σ n z r b < -δ*(1-ε)/2 := by
  let C := canonicalGaussianFreeValue σ n z r
  have hf : HasDerivAt C (-1/2) b := by
    simpa only [hstat] using canonicalGaussianFreeValue_hasDerivAt σ n z hz r hp
  have hlin := hf.isLittleO.def (by positivity : 0 < ε/4)
  have hpos : ∀ᶠ t in 𝓝 b, 0 < quadraticCascadePrecision σ t n z :=
    (quadraticCascadePrecision_hasDerivAt σ n z b).continuousAt.eventually (eventually_gt_nhds hp)
  obtain ⟨η,hη,hboth⟩ := Metric.eventually_nhds_iff.mp (hlin.and hpos)
  let δ := η/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdη : δ < η := by dsimp [δ]; linarith
  have hleft : dist (b-δ) b < η := by simpa [Real.dist_eq,abs_of_nonneg hδ.le] using hdη
  have hright : dist (b+δ) b < η := by simpa [Real.dist_eq,abs_of_nonneg hδ.le] using hdη
  obtain ⟨hl,hlp⟩ := hboth hleft
  obtain ⟨hr,hrp⟩ := hboth hright
  simp only [Real.norm_eq_abs,smul_eq_mul] at hl hr
  have hdl : b-δ-b = -δ := by ring
  have hdr : b+δ-b = δ := by ring
  rw [hdl,abs_neg,abs_of_pos hδ] at hl
  rw [hdr,abs_of_pos hδ] at hr
  refine ⟨δ,hδ,hlp,hrp,?_,?_⟩
  · have := (abs_le.mp hl).2
    dsimp only [C] at this
    nlinarith [mul_pos hε hδ]
  · have := (abs_le.mp hr).2
    dsimp only [C] at this
    nlinarith [mul_pos hε hδ]

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

end SphericalPerceptron

namespace SphericalPerceptron

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

end SphericalPerceptron
end
end
end

end OAI
