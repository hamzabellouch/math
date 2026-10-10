import Mathlib
import OAI.Probability.LogConcave.LowerBounds.DensityCoefficient
import OAI.Probability.LogConcave.Sampling.Map

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open Polynomial
open scoped BigOperators

namespace LogConcaveSampling.LowerBound
open WithLp
open scoped RealInnerProductSpace

lemma spectrum_iterate_apply {d : ℕ} (j : ℕ) (x : Point d) (k : Fin d) :
    ((spectrumOperator d).toLinearMap^[j]) x k = x k * eigenvalue d k ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change spectrumOperator d (((spectrumOperator d).toLinearMap^[j]) x) k = _
    rw [spectrumOperator_apply,ih,pow_succ]
    ring

lemma orbitHull_in_krylov {d r : ℕ} (a : Fin (r+1) → Point d) {u : Point d}
    (hu : u ∈ orbitHull (spectrumOperator d).toLinearMap r a) :
    ofLp u ∈ krylovSpace (fun k i => a i k) := by
  let coord : Point d →ₗ[ℝ] (Fin d → ℝ) :=
    {toFun := ofLp, map_add' := by intros; rfl, map_smul' := by intros; rfl}
  have h : orbitHull (spectrumOperator d).toLinearMap r a ≤
      (krylovSpace (fun k i => a i k)).comap coord := by
    apply Submodule.span_le.mpr
    rintro v ⟨i,j,hj,rfl⟩
    apply Submodule.subset_span
    refine ⟨i,j,hj,?_⟩
    funext k
    exact spectrum_iterate_apply j (a i) k
  exact h hu

lemma linearReply_eq_quadratic {d : ℕ} (O : Rotations d) (x : Point d) :
    linearReply (spectrumOperator d) O x = firstOrderReply (quadraticPotential O) x := by
  rw [quadratic_firstOrderReply]
  apply Prod.ext
  · change ⟪(rotationIsometry O).symm x, spectrumOperator d ((rotationIsometry O).symm x)⟫ / 2 = _
    have h := (rotationIsometry O).inner_map_map ((rotationIsometry O).symm x)
      (spectrumOperator d ((rotationIsometry O).symm x))
    simpa only [LinearIsometryEquiv.apply_symm_apply, quadraticOperator,
      ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe] using congrArg (fun z : ℝ => z/2) h.symm
  · rfl

lemma linearHistory_eq_quadratic {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (O : Rotations d) (ω : Ω) (n : ℕ) :
    linearHistory A (spectrumOperator d) O ω n = A.history (quadraticPotential O) ω n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [linearHistory,OracleAlgorithm.history,ih,linearReply_eq_quadratic]

def hardEigenOutput {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (p : Ω × Rotations d) : Fin d → ℝ :=
  ofLp ((rotationIsometry p.2).symm (A.run (quadraticPotential p.2) p.1))

lemma measurable_hardEigenOutput {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) : Measurable (hardEigenOutput A) := by
  have hr : Measurable (fun p : Ω × Rotations d => A.run (quadraticPotential p.2) p.1) := by
    simpa only [OracleAlgorithm.run,← linearHistory_eq_quadratic,Function.comp_def] using
      A.output_measurable.comp (measurable_fst.prodMk (measurable_linearHistory A (spectrumOperator d) q))
  have haction : Measurable (fun p : Rotations d × Point d => (rotationIsometry p.1).symm p.2) := by
    have hh := (continuous_rotation_apply (d := d)).measurable.comp
      (f := fun p : Rotations d × Point d => (p.1⁻¹,p.2))
      (measurable_fst.inv.prodMk measurable_snd)
    simpa only [Function.comp_def,rotationIsometry_inv_apply] using hh
  exact (measurable_ofLp 2 _).comp (f := fun p : Ω × Rotations d =>
    (rotationIsometry p.2).symm (A.run (quadraticPotential p.2) p.1))
    (haction.comp (f := fun p : Ω × Rotations d =>
      (p.2,A.run (quadraticPotential p.2) p.1)) (measurable_snd.prodMk hr))

theorem hard_algorithm_separation {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (hd : 2*q+1 ≤ d) (hqd : 4*(q+q)+1 < 2*d) (ht : blockTolerance d (q+q) ≤ 1/2) :
    (μ.prod (rotationHaar d)).real {p | hardEigenOutput A p ∈ separationEvent d (q+q)} ≤ 1/100 := by
  let P := couplingLaw μ d q
  let U : CouplingNoise Ω d q → Fin d → ℝ := fun p =>
    ofLp (finishCoordinate A (by omega) (couplingState A (spectrumOperator d) hd p).1)
  let rows : CouplingNoise Ω d q → Fin d → Fin (q+q+1) → ℝ := fun p k i => couplingColumns p i k
  have hrows : HasLaw rows (gaussianRows d (q+q+1)) P := by
    have he : MeasurePreserving (fun a : Fin (q+q+1) → Point d => fun k i => a i k)
        (Measure.pi (fun _ : Fin (q+q+1) => stdGaussian (Point d))) (gaussianRows d (q+q+1)) :=
      ⟨by fun_prop,gaussianColumns_rows_law d (q+q+1)⟩
    exact (he.comp (couplingColumns_law μ)).hasLaw
  have hU : ∀ᵐ p ∂P, U p ∈ krylovSpace (rows p) := by
    filter_upwards [coupling_output_span μ A (spectrumOperator d) hd] with p hp
    exact orbitHull_in_krylov (couplingColumns p) hp
  have hb := algorithm_span_separation_bound hqd ht hrows U hU
  have he : ∀ᵐ p ∂P, U p = hardEigenOutput A
      (finishComplete A (by omega) (couplingState A (spectrumOperator d) hd p)) := by
    filter_upwards [coupling_output_correct μ A (spectrumOperator d) hd] with p hp
    simpa only [hardEigenOutput,OracleAlgorithm.run,linearHistory_eq_quadratic] using congrArg ofLp hp
  have hmeas : MeasurableSet {p | hardEigenOutput A p ∈ separationEvent d (q+q)} :=
    (separationEvent_measurable d (q+q)).preimage (measurable_hardEigenOutput A)
  rw [← coupling_complete_law μ A (spectrumOperator d) hd,
    Measure.real,Measure.map_apply
      ((measurable_finishComplete A (by omega)).comp (measurable_couplingState A (spectrumOperator d) hd)) hmeas]
  change P.real {p | hardEigenOutput A (finishComplete A (by omega) (couplingState A (spectrumOperator d) hd p)) ∈ separationEvent d (q+q)} ≤ _
  have hs : {p | hardEigenOutput A (finishComplete A (by omega) (couplingState A (spectrumOperator d) hd p)) ∈ separationEvent d (q+q)}
      =ᵐ[P] {p | U p ∈ separationEvent d (q+q)} := by
    filter_upwards [he] with p hp
    exact congrArg (fun z : Fin d → ℝ => z ∈ separationEvent d (q+q)) hp.symm
  rwa [measureReal_congr hs]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma quadratic_gibbs_eigenframe {d : ℕ} (O : Rotations d) :
    (gibbs (quadraticPotential O)).map (fun x => ofLp ((rotationIsometry O).symm x)) =
      targetGaussian d := by
  rw [← quadratic_gibbs_eq_gaussian O,Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply,WithLp.ofLp_toLp]
  exact Measure.map_id

lemma hardEigenOutput_tv {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : OracleAlgorithm Ω d q)
    (h : ∀ O : Rotations d, TVAtMost (μ.map (A.run (quadraticPotential O)))
      (gibbs (quadraticPotential O)) (1/10)) (O : Rotations d) :
    TVAtMost (μ.map (fun ω => hardEigenOutput A (ω,O))) (targetGaussian d) (1/10) := by
  have hr : Measurable (A.run (quadraticPotential O)) := by
    change Measurable (fun ω : Ω => A.output (ω,A.history (quadraticPotential O) ω q))
    simp_rw [← linearHistory_eq_quadratic A O]
    exact A.output_measurable.comp (f := fun ω : Ω =>
      (ω,linearHistory A (spectrumOperator d) O ω q))
      (measurable_id.prodMk ((measurable_linearHistory A (spectrumOperator d) q).comp
        (f := fun ω : Ω => (ω,O)) (measurable_id.prodMk measurable_const)))
  have ht := (h O).map (f := fun x => ofLp ((rotationIsometry O).symm x)) (by fun_prop)
  rwa [quadratic_gibbs_eigenframe,Measure.map_map (by fun_prop) hr] at ht

theorem canSample_target_separation_bound {d q : ℕ}
    (hd : 2*q+1 ≤ d) (hqd : 4*(q+q)+1 < 2*d) (ht : blockTolerance d (q+q) ≤ 1/2)
    (h : CanSample d q) : (targetGaussian d).real (separationEvent d (q+q)) ≤ 11/100 := by
  obtain ⟨Ω,mΩ,μ,hμ,A,hA⟩ := h
  have hTV := hardEigenOutput_tv μ A (fun O => (hA _ (quadraticPotential_admissible O)).2)
  have hevent := hard_algorithm_separation μ A hd hqd ht
  have hm : MeasurableSet {p | hardEigenOutput A p ∈ separationEvent d (q+q)} :=
    (separationEvent_measurable d (q+q)).preimage (measurable_hardEigenOutput A)
  have hlower := prob_prod_event_lower μ (rotationHaar d) hm
    (a := (targetGaussian d).real (separationEvent d (q+q)) - 1/10) (fun O => by
      have hh := hTV O _ (separationEvent_measurable d (q+q))
      have hb : Measurable (fun ω : Ω => hardEigenOutput A (ω,O)) :=
        (measurable_hardEigenOutput A).comp (f := fun ω : Ω => (ω,O))
          (measurable_id.prodMk measurable_const)
      rw [Measure.real,Measure.map_apply hb (separationEvent_measurable d (q+q))] at hh
      have hh' := (abs_le.mp hh).1
      change -(1/10 : ℝ) ≤ μ.real {ω | hardEigenOutput A (ω,O) ∈ separationEvent d (q+q)} - _ at hh'
      change _ ≤ μ.real {ω | hardEigenOutput A (ω,O) ∈ separationEvent d (q+q)}
      linarith)
  linarith

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma spectralDecay_bounds : (1/8 : ℝ) ≤ spectralDecay ∧ spectralDecay ≤ 1/4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h' := Real.sqrt_nonneg (2 : ℝ)
  dsimp [spectralDecay]
  constructor <;> nlinarith

theorem target_mean_lower {d r : ℕ} (hn : 2*r+1 < d) :
    (d : ℝ) / (4 * 8^(2*r+1)) ≤
      |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*r+1) k) u ∂targetGaussian d| := by
  let n := 2*r+1
  let m := ∫ u, diagonalStatistic (fun k : Fin d => weight d (2*r+1) k) u ∂targetGaussian d
  have hr := (lower_target_statistic hn).1
  have hp : 0 < spectralDecay := spectralDecay_pos
  have hb := spectralDecay_bounds
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hp2 : spectralDecay^2 ≤ 1/16 := by nlinarith
  have hpow : spectralDecay^(2*d-n) ≤ spectralDecay^(n+2) :=
    pow_le_pow_of_le_one hp.le spectralDecay_lt_one.le (by dsimp [n]; omega)
  have hrem : Real.sqrt 2 * d * spectralDecay^(2*d-n) / (1-spectralDecay) ≤
      (d : ℝ) * spectralDecay^n / 4 := by
    calc
      _ ≤ 2 * d * spectralDecay^(n+2) / (1/2) := by
        apply div_le_div₀ (by positivity)
        · gcongr
        · norm_num
        · linarith
      _ = 4 * d * spectralDecay^n * spectralDecay^2 := by rw [pow_add]; ring
      _ ≤ (d : ℝ) * spectralDecay^n / 4 := by
        have hh := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hd (pow_nonneg hp.le n))
        nlinarith
  have hlead : (d : ℝ) * spectralDecay^n / 2 ≤ |(d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n| := by
    rw [abs_mul,abs_div,abs_pow,abs_neg,abs_of_nonneg hd,abs_of_pos hs,abs_of_pos hp]
    calc
      _ = ((d : ℝ)/2) * spectralDecay^n := by ring
      _ ≤ _ := by gcongr
  have htri := abs_sub_abs_le_abs_sub ((d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n) m
  rw [abs_sub_comm] at htri
  have hmean : (d : ℝ) * spectralDecay^n / 4 ≤ |m| := by
    change |m - (d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n| ≤ _ at hr
    linarith only [hr,hrem,hlead,htri]
  calc
    _ = (d : ℝ) * (1/8)^n / 4 := by rw [div_pow]; simp only [one_pow]; field_simp; rfl
    _ ≤ (d : ℝ) * spectralDecay^n / 4 := by gcongr; exact hb.1
    _ ≤ _ := hmean

lemma lower_denominator (q : ℕ) : (4 : ℝ) * 8^(2*(q+q)+1) = 2^(12*q+5) := by
  rw [show (4 : ℝ) = 2^2 by norm_num, show (8 : ℝ) = 2^3 by norm_num,
    ← pow_mul,← pow_add]
  congr 1
  omega

lemma polynomial_threshold_le_pow (q : ℕ) :
    160 * ((q+q : ℕ)+1 : ℝ)^2 + 20 ≤ (2 : ℝ)^(2*q+10) := by
  have hq : ((q+q : ℕ)+1 : ℝ) ≤ (2 : ℝ)^(q+1) := by
    have h := (Nat.lt_two_pow_self (n := q)).succ_le
    have hh : (q : ℝ)+1 ≤ (2 : ℝ)^q := by exact_mod_cast h
    push_cast
    rw [pow_succ]
    linarith
  have hp : (1 : ℝ) ≤ 2^(2*q+2) := one_le_pow₀ (by norm_num)
  have hsq : (((q+q : ℕ)+1 : ℝ)^2) ≤ (2 : ℝ)^(2*q+2) := by
    calc
      _ ≤ ((2 : ℝ)^(q+1))^2 := by gcongr
      _ = _ := by rw [← pow_mul]; congr 1; omega
  calc
    _ ≤ 180 * (2 : ℝ)^(2*q+2) := by nlinarith
    _ ≤ 256 * (2 : ℝ)^(2*q+2) := by gcongr; norm_num
    _ = _ := by rw [show 256 = (2:ℝ)^8 by norm_num,← pow_add]; congr 1; omega

lemma sqrt_exponential_lower {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    (2 : ℝ)^(32*(q+1)) ≤ Real.sqrt d := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have hh : (2 : ℝ)^(64*(q+1)) ≤ d := by exact_mod_cast hd
  convert hh using 1
  rw [← pow_mul]
  congr 1
  omega

lemma target_large_mean {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) (hn : 2*(q+q)+1 < d) :
    separationThreshold d (q+q) + 20 * Real.sqrt d ≤
      |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*(q+q)+1) k) u ∂targetGaussian d| := by
  have hm := target_mean_lower hn
  rw [lower_denominator] at hm
  have hs := sqrt_exponential_lower hd
  have hcoeff := polynomial_threshold_le_pow q
  have hp : (2 : ℝ)^(2*q+10) * 2^(12*q+5) ≤ Real.sqrt d := by
    calc
      _ = (2 : ℝ)^(14*q+15) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2^(32*(q+1)) := by apply pow_le_pow_right₀ (by norm_num); omega
      _ ≤ _ := hs
  have hh : (160 * (((q+q : ℕ)+1 : ℝ))^2 + 20) * 2^(12*q+5) ≤ Real.sqrt d :=
    le_trans (mul_le_mul_of_nonneg_right hcoeff (by positivity)) hp
  have hh' := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg (d : ℝ))
  rw [← sq,Real.sq_sqrt (Nat.cast_nonneg d)] at hh'
  calc
    _ = (160 * (((q+q : ℕ)+1 : ℝ))^2 + 20) * Real.sqrt d := by
      unfold separationThreshold
      push_cast
      ring
    _ ≤ (d : ℝ) / 2^(12*q+5) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [hh']
    _ ≤ _ := hm

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

lemma exponential_dimension_bounds {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    100 ≤ d ∧ 2*(q+q)+1 < d ∧ 2*q+1 ≤ d ∧ 4*(q+q)+1 < 2*d := by
  have hlin := (Nat.lt_two_pow_self (n := 64*(q+1))).trans_le hd
  have hexp : 2^64 ≤ 2^(64*(q+1)) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h100 : 100 ≤ d := le_trans (by norm_num : 100 ≤ 2^64) (hexp.trans hd)
  omega

lemma exponential_tolerance {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    blockTolerance d (q+q) ≤ 1/2 := by
  have hpos : 0 < d := by have := (exponential_dimension_bounds hd).1; omega
  have hs := sqrt_exponential_lower hd
  have hcoeff := polynomial_threshold_le_pow q
  have hp : (2 : ℝ)^(2*q+10) ≤ 2^(32*(q+1)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hh : 80 * (((q+q : ℕ)+1 : ℝ))^2 ≤ Real.sqrt d := by
    have hsq := sq_nonneg (((q+q : ℕ)+1 : ℝ))
    linarith
  unfold blockTolerance
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hpos))).mpr
  push_cast at hh ⊢
  linarith

theorem target_event_large {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) :
    9/10 ≤ (targetGaussian d).real (separationEvent d (q+q)) := by
  have hb := exponential_dimension_bounds hd
  have hpos : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hpos
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdr
  have hm := target_large_mean hd hb.2.1
  let m := |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*(q+q)+1) k) u ∂targetGaussian d|
  have hmargin : 20 * Real.sqrt d ≤ m - separationThreshold d (q+q) := by
    dsimp [m]; linarith only [hm]
  have hsep : separationThreshold d (q+q) < m := by linarith
  have htail := target_separation_tail hpos hsep
  have hden : 400 * (d : ℝ) ≤ (m-separationThreshold d (q+q))^2 := by
    calc
      _ = (20 * Real.sqrt (d : ℝ))^2 := by rw [mul_pow,Real.sq_sqrt hdr.le]; ring
      _ ≤ _ := by gcongr
  have h₁ : 2/(d : ℝ) ≤ 1/50 := by
    apply (div_le_iff₀ hdr).mpr
    have hh : (100 : ℝ) ≤ d := by exact_mod_cast hb.1
    linarith
  have h₂ : 2*d/(m-separationThreshold d (q+q))^2 ≤ 1/200 := by
    apply (div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hsep))).mpr
    linarith
  rw [measureReal_compl (separationEvent_measurable d (q+q)),probReal_univ] at htail
  change 1 - (targetGaussian d).real (separationEvent d (q+q)) ≤ 2/(d : ℝ) +
    2*d/(m-separationThreshold d (q+q))^2 at htail
  linarith

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

theorem not_canSample_exponential {d q : ℕ} (hd : 2^(64*(q+1)) ≤ d) : ¬ CanSample d q := by
  intro h
  have hb := exponential_dimension_bounds hd
  have h₁ := canSample_target_separation_bound hb.2.2.1 hb.2.2.2 (exponential_tolerance hd) h
  have h₂ := target_event_large hd
  linarith

lemma exponential_of_small_log {d q : ℕ} (hd : 2^128 ≤ d)
    (hq : (q : ℝ) < (128 * Real.log 2)⁻¹ * Real.log d) : 2^(64*(q+1)) ≤ d := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hdp : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hdp
  have hd' : (2 : ℝ)^128 ≤ d := by exact_mod_cast hd
  have hlog : 128 * Real.log (2 : ℝ) ≤ Real.log d := by
    have hh := Real.log_le_log (by positivity) hd'
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hq' : 128 * Real.log (2 : ℝ) * q < Real.log d := by
    have hh := mul_lt_mul_of_pos_left hq (show 0 < 128 * Real.log (2 : ℝ) by positivity)
    rwa [← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul] at hh
  have hx : Real.log ((2 : ℝ)^(64*(q+1))) ≤ Real.log d := by
    rw [Real.log_pow]
    push_cast
    nlinarith only [hlog,hq']
  have hexp := (Real.log_le_log_iff (by positivity) hdr).mp hx
  exact_mod_cast hexp

theorem source_logarithmic_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ENNReal.ofReal (c * Real.log (d : ℝ)) ≤ (queryComplexity d).toENNReal := by
  refine ⟨(128 * Real.log 2)⁻¹, by positivity, 2^128, by norm_num, ?_⟩
  intro d hd
  have hfeasible : ∀ q : ℕ, CanSample d q → (128 * Real.log 2)⁻¹ * Real.log d ≤ q := by
    intro q hq
    by_contra hh
    exact not_canSample_exponential (exponential_of_small_log hd (lt_of_not_ge hh)) hq
  unfold queryComplexity
  rw [sInf_image]
  simp only [ENat.toENNReal_iInf]
  apply le_iInf
  intro q
  apply le_iInf
  intro hq
  simpa only [ENat.toENNReal_coe,ENNReal.ofReal_natCast] using
    ENNReal.ofReal_le_ofReal (hfeasible q hq)

end LogConcaveSampling.LowerBound

end LowerProof

end

end

end

end OAI
