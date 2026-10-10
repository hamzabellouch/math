import OAI.Probability.RadialTransition.LatticeStability

namespace OAI

universe uX uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem isClosed_cube (L : ℝ) : IsClosed (cube L) := by
  have heq : cube L = ⋂ k : Fin 3, {x : Position | x k ∈ Icc 0 L} := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_iInter, mem_Icc]
  rw [heq]
  exact isClosed_iInter (fun k : Fin 3 =>
    isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k))

theorem measurableSet_cube (L : ℝ) : MeasurableSet (cube L) :=
  (isClosed_cube L).measurableSet

theorem volume_cube (L : ℝ) : volume (cube L) = ENNReal.ofReal L ^ 3 := by
  have heq : cube L = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin 3 => Icc (0 : ℝ) L) := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi (fun _ : Fin 3 => measurableSet_Icc)).nullMeasurableSet]
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem measurableSet_configurationCube (L : ℝ) (N : ℕ) :
    MeasurableSet (configurationCube L N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp only [configurationCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [heq]
  exact MeasurableSet.univ_pi (fun _ : Fin N => measurableSet_cube L)

theorem volume_configurationCube (L : ℝ) (N : ℕ) :
    volume (configurationCube L N) = ENNReal.ofReal L ^ (3 * N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp only [configurationCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [heq, volume_pi]
  rw [Measure.pi_pi]
  simp [volume_cube, ← pow_mul]

theorem continuous_energy {φ : Potential} (hφ : Continuous φ) (N : ℕ) :
    Continuous (energy φ (N := N)) := by
  unfold energy
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _
    (fun j _ => hφ.comp ((continuous_apply i).nndist (continuous_apply j))))

theorem energy_abs_bound {φ : Potential} {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ r : ℝ≥0, |φ r| ≤ M) {N : ℕ} (x : Fin N → Position) :
    |energy φ x| ≤ (N : ℝ) ^ 2 * M := by
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N with i < j, |φ (nndist (x i) (x j))| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, M := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (Finset.sum_le_sum (fun j _ => hφ _))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp; ring

theorem integrableOn_boltzmann {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) (L : ℝ) (N : ℕ) (β : ℝ) :
    IntegrableOn (fun x : Fin N → Position => Real.exp (-β * energy φ x))
      (configurationCube L N) := by
  obtain ⟨M, hM, hφM⟩ := hb
  have hfinite : volume (configurationCube L N) < ⊤ := by
    rw [volume_configurationCube]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  apply IntegrableOn.of_bound hfinite ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_energy hφ N))).stronglyMeasurable.aestronglyMeasurable) (Real.exp (|β| * ((N : ℝ) ^ 2 * M)))
  filter_upwards [] with x
  change |Real.exp (-β * energy φ x)| ≤ _
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β * energy φ x ≤ |-β * energy φ x| := le_abs_self _
    _ = |β| * |energy φ x| := by rw [abs_mul, abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_abs_bound hM hφM x) (abs_nonneg _)

theorem partition_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (β : ℝ) : 0 < partition φ L N β := by
  unfold partition
  apply mul_pos (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))
  apply (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-β * energy φ x)).le))
    (integrableOn_boltzmann hφ hb L N β)).mpr
  have heq : Function.support (fun x : Fin N → Position => Real.exp (-β * energy φ x)) = univ := by
    ext x
    simp [Function.mem_support]
  rw [heq, Measure.restrict_apply_univ]
  rw [volume_configurationCube]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ ((ENNReal.ofReal_pos.mpr hL).ne'))

theorem log_integral_exp_convex_mix {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {F G : X → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (hH : Integrable (fun x => Real.exp (a * F x + b * G x)) μ)
    (hZF : 0 < ∫ x, Real.exp (F x) ∂μ) (hZG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (hZH : 0 < ∫ x, Real.exp (a * F x + b * G x) ∂μ) :
    Real.log (∫ x, Real.exp (a * F x + b * G x) ∂μ) ≤
      a * Real.log (∫ x, Real.exp (F x) ∂μ) + b * Real.log (∫ x, Real.exp (G x) ∂μ) := by
  let c := a * Real.log (∫ x, Real.exp (F x) ∂μ) + b * Real.log (∫ x, Real.exp (G x) ∂μ)
  have hpoint (x : X) : Real.exp (-c) * Real.exp (a * F x + b * G x) ≤
      a * ((∫ x, Real.exp (F x) ∂μ)⁻¹ * Real.exp (F x)) +
      b * ((∫ x, Real.exp (G x) ∂μ)⁻¹ * Real.exp (G x)) := by
    have hh := convexOn_exp.2 (mem_univ (F x - Real.log (∫ x, Real.exp (F x) ∂μ)))
      (mem_univ (G x - Real.log (∫ x, Real.exp (G x) ∂μ))) ha hb hab
    simp only [smul_eq_mul] at hh
    have heq : a * (F x - Real.log (∫ x, Real.exp (F x) ∂μ)) +
        b * (G x - Real.log (∫ x, Real.exp (G x) ∂μ)) = -c + (a * F x + b * G x) := by
      dsimp [c]; ring
    rw [heq, Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log hZF, Real.exp_log hZG] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hi := integral_mono (hH.const_mul _) ((hF.const_mul _).const_mul a |>.add
      ((hG.const_mul _).const_mul b)) hpoint
  simp only [Pi.add_apply, integral_add ((hF.const_mul _).const_mul a) ((hG.const_mul _).const_mul b),
    integral_const_mul, inv_mul_cancel₀ hZF.ne', inv_mul_cancel₀ hZG.ne', mul_one, hab] at hi
  have hexp := Real.log_le_log (mul_pos (Real.exp_pos (-c)) hZH) hi
  rw [Real.log_mul (Real.exp_ne_zero _) hZH.ne', Real.log_exp, Real.log_one] at hexp
  change _ ≤ c
  linarith

theorem integral_const_configurationCube {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (c : ℝ) :
    (∫ _x : Fin N → Position in configurationCube L N, c) = L ^ (3 * N) * c := by
  rw [setIntegral_const, Measure.real, volume_configurationCube, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hL]
  rfl

theorem partition_zero (φ : Potential) (L β : ℝ) : partition φ L 0 β = 1 := by
  have heq : (fun x : Fin 0 → Position => Real.exp (-β * energy φ x)) = fun _ => (1 : ℝ) := by
    funext x
    simp [energy]
  unfold partition
  rw [heq, setIntegral_const, Measure.real, volume_configurationCube]
  simp

theorem partition_nonneg {φ : Potential} (L : ℝ) (N : ℕ) (β : ℝ) :
    0 ≤ partition φ L N β := by
  exact mul_nonneg (by positivity) (integral_nonneg fun x => (Real.exp_pos _).le)

theorem partition_upper_of_energy_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 ≤ L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : ∀ x ∈ configurationCube L N, E ≤ energy φ x) :
    partition φ L N β ≤ (N.factorial : ℝ)⁻¹ * L ^ (3 * N) * Real.exp (-β * E) := by
  have hfinite : volume (configurationCube L N) ≠ ⊤ := by
    simp [volume_configurationCube]
  have hconst : IntegrableOn (fun _ : Fin N → Position => Real.exp (-β * E))
      (configurationCube L N) := integrableOn_const hfinite
  have hc := setIntegral_mono_on (integrableOn_boltzmann hφ hb L N β) hconst
    (measurableSet_configurationCube L N) (fun x hx =>
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hE x hx) (neg_nonpos.mpr hβ)))
  rw [integral_const_configurationCube hL] at hc
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_assoc _ _ _).symm

theorem partition_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (N : ℕ) :
    partition φ L N β ≤ (L ^ 3 * Real.exp (β * B)) ^ N / N.factorial := by
  have hh := partition_upper_of_energy_lower hφ hb hL hβ N (fun x _ => hstable N x)
  have heq : (N.factorial : ℝ)⁻¹ * L ^ (3 * N) * Real.exp (-β * (-(B * N))) =
      (L ^ 3 * Real.exp (β * B)) ^ N / N.factorial := by
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    have he : -β * -(B * (N : ℝ)) = (N : ℝ) * (β * B) := by ring
    rw [he]
    ring
  exact hh.trans_eq heq

theorem log_partition_upper_of_energy_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : ∀ x ∈ configurationCube L N, E ≤ energy φ x) :
    Real.log (partition φ L N β) ≤
      (N : ℝ) * Real.log (L ^ 3) - Real.log (N.factorial : ℝ) - β * E := by
  have hh := Real.log_le_log (partition_pos hφ hb hL N β)
    (partition_upper_of_energy_lower hφ hb hL.le hβ N hE)
  have hfac : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  rw [Real.log_mul (mul_ne_zero (inv_ne_zero hfac) (pow_ne_zero _ hL.ne')) (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hfac) (pow_ne_zero _ hL.ne'), Real.log_inv,
    Real.log_pow, Real.log_exp] at hh
  rw [Real.log_pow]

  push_cast at hh
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

theorem boltzmannIntegral_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (β : ℝ) :
    0 < ∫ x in configurationCube L N, Real.exp (-β * energy φ x) := by
  have hp := partition_pos hφ hb hL N β
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))).mp hp

theorem log_partition_convex_mix {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L a b : ℝ} (hL : 0 < L) (N : ℕ) (β γ : ℝ)
    (ha : 0 ≤ a) (hbb : 0 ≤ b) (hab : a + b = 1) :
    Real.log (partition φ L N (a * β + b * γ)) ≤
      a * Real.log (partition φ L N β) + b * Real.log (partition φ L N γ) := by
  have heq (x : Fin N → Position) : a * (-β * energy φ x) + b * (-γ * energy φ x) =
      -(a * β + b * γ) * energy φ x := by ring
  have hc := log_integral_exp_convex_mix (F := fun x : Fin N → Position => -β * energy φ x)
    (G := fun x => -γ * energy φ x) (μ := volume.restrict (configurationCube L N)) ha hbb hab
    (integrableOn_boltzmann hφ hb L N β) (integrableOn_boltzmann hφ hb L N γ)
    (by simp_rw [heq]; exact integrableOn_boltzmann hφ hb L N _) (boltzmannIntegral_pos hφ hb hL N β)
    (boltzmannIntegral_pos hφ hb hL N γ) (by simp_rw [heq]; exact boltzmannIntegral_pos hφ hb hL N _)
  simp_rw [heq] at hc
  have hfac : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  simp only [partition, Real.log_mul (inv_ne_zero hfac)
    (boltzmannIntegral_pos hφ hb hL N _).ne']
  have haff := congrArg (fun z : ℝ => z * Real.log (N.factorial : ℝ)⁻¹) hab
  nlinarith [haff]

def finiteCanonical (φ : Potential) (t L : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  -Real.log (partition φ L N β) / (t * L ^ 3)

theorem finiteCanonical_concave {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (N : ℕ) :
    ConcaveOn ℝ univ (finiteCanonical φ t L N) := by
  refine ⟨convex_univ, ?_⟩
  intro β _ γ _ a b ha hbb hab
  simp only [finiteCanonical, smul_eq_mul]
  have hh := log_partition_convex_mix hφ hb hL N β γ ha hbb hab
  have hd : 0 < t * L ^ 3 := mul_pos ht (pow_pos hL _)
  apply (le_div_iff₀ hd).mpr
  field_simp
  nlinarith

def grandPartition (φ : Potential) (t L β h : ℝ) : ℝ :=
  ∑' N : ℕ, Real.exp (t * h * N) * partition φ L N β

theorem grandTerm_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) (N : ℕ) :
    Real.exp (t * h * N) * partition φ L N β ≤
      (L ^ 3 * Real.exp (β * B + t * h)) ^ N / N.factorial := by
  have hh := mul_le_mul_of_nonneg_left (partition_stability_upper hφ hb hstable hL hβ N)
    (Real.exp_pos (t * h * N)).le
  apply hh.trans_eq
  rw [Real.exp_add, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul (β * B) N,
    ← Real.exp_nat_mul (t * h) N]
  have he : t * h * (N : ℝ) = (N : ℝ) * (t * h) := by ring
  rw [he]
  ring

theorem grandPartition_summable {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ L N β) :=
  Summable.of_nonneg_of_le
    (fun N => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
    (grandTerm_stability_upper hφ hb hstable hL hβ t h)
    (Real.summable_pow_div_factorial _)

theorem grandPartition_bounds {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) :
    1 ≤ grandPartition φ t L β h ∧
      grandPartition φ t L β h ≤ Real.exp (L ^ 3 * Real.exp (β * B + t * h)) := by
  have hs := grandPartition_summable hφ hb hstable hL hβ t h
  constructor
  · have hh := hs.le_tsum 0 (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
    convert hh using 1 <;> first | rfl | norm_num [partition_zero]
  · have hh := hs.tsum_le_tsum (grandTerm_stability_upper hφ hb hstable hL hβ t h)
      (Real.summable_pow_div_factorial _)
    have he : (∑' N : ℕ, (L ^ 3 * Real.exp (β * B + t * h)) ^ N / N.factorial) =
        Real.exp (L ^ 3 * Real.exp (β * B + t * h)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact hh.trans_eq he

theorem log_tsum_convex_mix {T U V : ℕ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hT : Summable T) (hU : Summable U) (hV : Summable V)
    (hpT : ∀ n, 0 < T n) (hpU : ∀ n, 0 < U n) (hpV : ∀ n, 0 < V n)
    (hlog : ∀ n, Real.log (T n) ≤ a * Real.log (U n) + b * Real.log (V n)) :
    Real.log (∑' n, T n) ≤ a * Real.log (∑' n, U n) + b * Real.log (∑' n, V n) := by
  have hsT : 0 < ∑' n, T n := lt_of_lt_of_le (hpT 0) (hT.le_tsum 0 (fun n _ => (hpT n).le))
  have hsU : 0 < ∑' n, U n := lt_of_lt_of_le (hpU 0) (hU.le_tsum 0 (fun n _ => (hpU n).le))
  have hsV : 0 < ∑' n, V n := lt_of_lt_of_le (hpV 0) (hV.le_tsum 0 (fun n _ => (hpV n).le))
  let c := a * Real.log (∑' n, U n) + b * Real.log (∑' n, V n)
  have hpoint (n : ℕ) : Real.exp (-c) * T n ≤
      a * ((∑' n, U n)⁻¹ * U n) + b * ((∑' n, V n)⁻¹ * V n) := by
    have hcv := convexOn_exp.2 (mem_univ (Real.log (U n) - Real.log (∑' n, U n)))
      (mem_univ (Real.log (V n) - Real.log (∑' n, V n))) ha hb hab
    simp only [smul_eq_mul] at hcv
    have he : a * (Real.log (U n) - Real.log (∑' n, U n)) +
        b * (Real.log (V n) - Real.log (∑' n, V n)) =
        -c + (a * Real.log (U n) + b * Real.log (V n)) := by dsimp [c]; ring
    rw [he, Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log (hpU n),
      Real.exp_log (hpV n), Real.exp_log hsU, Real.exp_log hsV] at hcv
    have hh := Real.exp_le_exp.mpr (hlog n)
    rw [Real.exp_log (hpT n)] at hh
    apply (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans
    simpa only [div_eq_mul_inv, mul_comm] using hcv
  have hh := (hT.mul_left (Real.exp (-c))).tsum_le_tsum hpoint
    ((hU.mul_left _).mul_left a |>.add ((hV.mul_left _).mul_left b))
  rw [Summable.tsum_add ((hU.mul_left _).mul_left a) ((hV.mul_left _).mul_left b)] at hh
  simp only [tsum_mul_left, inv_mul_cancel₀ hsU.ne', inv_mul_cancel₀ hsV.ne', mul_one, hab] at hh
  have hh' := Real.log_le_log (mul_pos (Real.exp_pos (-c)) hsT) hh
  rw [Real.log_mul (Real.exp_ne_zero _) hsT.ne', Real.log_exp, Real.log_one] at hh'
  change _ ≤ c
  linarith

def cubeProbability (L : ℝ) : Measure Position :=
  (ENNReal.ofReal (L ^ 3))⁻¹ • volume.restrict (cube L)

theorem cubeProbability_isProbability {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (cubeProbability L) := by
  constructor
  simp only [cubeProbability, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    volume_cube, ENNReal.ofReal_pow hL.le]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hL).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem measure_pi_smul {ι : Type uIndex} [Fintype ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := by
    intro i
    rw [← ENNReal.coe_toNNReal (hc i)]
    change SigmaFinite ((c i).toNNReal • μ i)
    infer_instance
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

theorem cubeProbability_pi {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Measure.pi (fun _ : Fin N => cubeProbability L) =
      (ENNReal.ofReal (L ^ (3 * N)))⁻¹ • volume.restrict (configurationCube L N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp [configurationCube, Set.mem_pi]
  rw [heq, volume_pi, Measure.restrict_pi_pi]
  unfold cubeProbability
  rw [measure_pi_smul _ _ (fun _ => ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr (pow_pos hL _)).ne')]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.inv_pow, ← ENNReal.ofReal_pow (pow_nonneg hL.le 3),
    ← pow_mul]

theorem measurePreserving_pair_eval {ι : Type uIndex} {X : Type uX} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x : ι → X => (x i, x j))
      (Measure.pi (fun _ : ι => μ)) (μ.prod μ) := by
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : ι => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _), ?_⟩
  have hp := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable
  simpa only [id_eq, (measurePreserving_eval (fun _ : ι => μ) i).map_eq,
    (measurePreserving_eval (fun _ : ι => μ) j).map_eq] using hp

theorem probability_pair_kernel_bound {L M : ℝ} (hL : 0 < L) {K : Position → ℝ}
    (hK : Continuous K) (hKM : ∀ z, |K z| ≤ M) (hKi : Integrable K)
    (hK0 : ∀ z, 0 ≤ K z) :
    (∫ z : Position × Position, K (z.1 - z.2) ∂(cubeProbability L).prod (cubeProbability L)) ≤
      (L ^ 3)⁻¹ * ∫ z, K z := by
  let := cubeProbability_isProbability hL
  have hi : Integrable (fun z : Position × Position => K (z.1 - z.2))
      ((cubeProbability L).prod (cubeProbability L)) :=
    Integrable.of_bound (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable M
      (Eventually.of_forall (fun z => hKM (z.1 - z.2)))
  rw [integral_prod _ hi]
  have hh (x : Position) : (∫ y, K (x - y) ∂cubeProbability L) ≤ (L ^ 3)⁻¹ * ∫ z, K z := by
    simp only [cubeProbability, integral_smul_measure, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (pow_nonneg hL.le 3), smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hL.le _))
    exact (setIntegral_le_integral (hKi.comp_sub_left x)
      (Eventually.of_forall (fun y => hK0 (x - y)))).trans_eq (integral_sub_left_eq_self K volume x)
  have hh' := integral_mono hi.integral_prod_left (integrable_const _) hh
  simpa [integral_const, Measure.real] using hh'

theorem probability_energy_upper {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L M : ℝ} (hL : 0 < L) (N : ℕ) {K : Position → ℝ}
    (hK : Continuous K) (hKM : ∀ z, |K z| ≤ M) (hKi : Integrable K)
    (hK0 : ∀ z, 0 ≤ K z) (hφK : ∀ x y, φ (nndist x y) ≤ K (x - y)) :
    (∫ x : Fin N → Position, energy φ x ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤
      (N : ℝ) ^ 2 * ((L ^ 3)⁻¹ * ∫ z, K z) := by
  classical
  let := cubeProbability_isProbability hL
  obtain ⟨Mφ, hMφ, hφM⟩ := hb
  have hipair (i j : Fin N) : Integrable
      (fun x : Fin N → Position => φ (nndist (x i) (x j)))
      (Measure.pi (fun _ : Fin N => cubeProbability L)) :=
    Integrable.of_bound (hφ.comp ((continuous_apply i).nndist (continuous_apply j))).aestronglyMeasurable
      Mφ (Eventually.of_forall (fun x => hφM _))
  have hik (i j : Fin N) : Integrable
      (fun x : Fin N → Position => K (x i - x j))
      (Measure.pi (fun _ : Fin N => cubeProbability L)) :=
    Integrable.of_bound (hK.comp ((continuous_apply i).sub (continuous_apply j))).aestronglyMeasurable
      M (Eventually.of_forall (fun x => hKM _))
  simp only [energy, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hipair i j))]
  have hbound (i j : Fin N) (hij : i < j) :
      (∫ x : Fin N → Position, φ (nndist (x i) (x j))
        ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ (L ^ 3)⁻¹ * ∫ z, K z := by
    apply (integral_mono (hipair i j) (hik i j) (fun x => hφK (x i) (x j))).trans
    have hp := measurePreserving_pair_eval (cubeProbability L) hij.ne
    have hmap := integral_map (μ := Measure.pi (fun _ : Fin N => cubeProbability L)) hp.measurable.aemeasurable
      (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    rw [hp.map_eq] at hmap
    simp only [Function.comp_apply, Pi.sub_apply] at hmap
    rw [← hmap]
    exact probability_pair_kernel_bound hL hK hKM hKi hK0
  have hconst : 0 ≤ (L ^ 3)⁻¹ * ∫ z, K z :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le _)) (integral_nonneg hK0)
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N with i < j,
        ∫ x : Fin N → Position, φ (nndist (x i) (x j))
          ∂Measure.pi (fun _ : Fin N => cubeProbability L) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hipair i j)]
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (L ^ 3)⁻¹ * ∫ z, K z := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.sum_le_sum (fun j hj => hbound i j (Finset.mem_filter.mp hj).2)).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hconst)
    _ = _ := by simp; ring

theorem integral_cubeProbability_pi {L : ℝ} (hL : 0 < L) (N : ℕ)
    (F : (Fin N → Position) → ℝ) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin N => cubeProbability L)) =
      (L ^ (3 * N))⁻¹ * ∫ x in configurationCube L N, F x := by
  rw [cubeProbability_pi hL N, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg hL.le _), smul_eq_mul]

theorem log_partition_lower_of_energy_mean {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : (∫ x : Fin N → Position, energy φ x
      ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ E) :
    (3 * N : ℝ) * Real.log L - Real.log (N.factorial : ℝ) - β * E ≤
      Real.log (partition φ L N β) := by
  let := cubeProbability_isProbability hL
  let μ := Measure.pi (fun _ : Fin N => cubeProbability L)
  obtain ⟨M, hM, hφM⟩ := hb
  have hi : Integrable (fun x : Fin N → Position => energy φ x) μ :=
    Integrable.of_bound (continuous_energy hφ N).aestronglyMeasurable
      ((N : ℝ)^2 * M) (Eventually.of_forall (energy_abs_bound hM hφM))
  have he : Integrable (fun x : Fin N → Position => Real.exp (-β * energy φ x)) μ := by
    apply Integrable.of_bound ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_energy hφ N))).aestronglyMeasurable)
      (Real.exp (|β| * ((N : ℝ)^2 * M)))
    filter_upwards [] with x
    change |Real.exp _| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      -β * energy φ x ≤ |-β * energy φ x| := le_abs_self _
      _ = |β| * |energy φ x| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left (energy_abs_bound hM hφM x) (abs_nonneg β)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun x : Fin N → Position => mem_univ (-β * energy φ x)))
    (hi.const_mul (-β)) he
  rw [integral_const_mul] at hj
  have hlow := (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hE (neg_nonpos.mpr hβ))).trans hj
  have hp : 0 < ∫ x : Fin N → Position, Real.exp (-β * energy φ x) ∂μ :=
    lt_of_lt_of_le (Real.exp_pos _) hlow
  have hl := Real.log_le_log (Real.exp_pos (-β * E)) hlow
  rw [Real.log_exp] at hl
  have hpint : 0 < ∫ x in configurationCube L N, Real.exp (-β * energy φ x) := by
    have h := partition_pos hφ ⟨M, hM, hφM⟩ hL N β
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))).mp h
  change -β * E ≤ Real.log (∫ x, Real.exp (-β * energy φ x)
    ∂Measure.pi (fun _ : Fin N => cubeProbability L)) at hl
  rw [integral_cubeProbability_pi hL N, Real.log_mul (inv_ne_zero (pow_ne_zero _ hL.ne')) hpint.ne',
    Real.log_inv, Real.log_pow] at hl
  rw [partition, Real.log_mul (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero N)) hpint.ne',
    Real.log_inv]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hl
  linarith

end RadialTransition

end

end OAI
