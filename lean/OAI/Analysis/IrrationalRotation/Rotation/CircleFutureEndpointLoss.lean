import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingLaw
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitEnergy
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterConsequences
import OAI.Analysis.IrrationalRotation.Analysis.EndpointIntervalBounds

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
open InvariantRotation.EndpointIntervalBounds

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coordinateLaw_raw_endpoint_le (j i : ℕ) (hi : 1 ≤ i) (side : Bool) :
    (coordinateLaw p j i).map (endpoint side) ≤ (10 : ℝ≥0∞) • baseLaw := by
  have hs := p.blockIndex_pos hp.m_pos hi
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by
      have := hp.m_ge_200 _ hs
      omega)
  have hk := CircleParameterLaws.coupling_kappa_bounds (p.blockIndex i) hs
  have ha := hp.coupling_a_bounds (p.blockIndex i) hs
  have hb := hp.coupling_b_bounds (p.blockIndex i) hs
  have ht := tag_bounds j (p.blockIndex i)
  rw [coordinateLaw, ite_eq_right (show i ≠ 0 by omega),
    rawLaw_map_endpoint hk.1 hk.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side]
  apply withDensity_le_smul_of_ae_le
  exact Eventually.of_forall (fun x =>
    (ENNReal.ofReal_le_ofReal
      (CircleDigitCoupling.marginalDensity_bounds hk.1 hk.2 hm ha.1 ha.2 hb.1 hb.2
        ht.1 ht.2 side x).2.2.le).trans_eq (by norm_num))

theorem law_raw_endpoint_le (j i : ℕ) (hi : 1 ≤ i) (side : Bool) :
    (law p j).map (fun ω => endpoint side (ω i)) ≤ (10 : ℝ≥0∞) • baseLaw := by
  let := coordinateLaw_isProbabilityMeasure hp j
  have he : Measurable (endpoint side) := by
    cases side
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  change (law p j).map (endpoint side ∘ (fun ω : Sample => ω i)) ≤ _
  rw [← Measure.map_map he (measurable_pi_apply i)]
  change ((Measure.infinitePi (coordinateLaw p j)).map (fun ω => ω i)).map _ ≤ _
  rw [Measure.infinitePi_map_eval]
  exact coordinateLaw_raw_endpoint_le hp j i hi side

theorem raw_endpoint_pair_loss_le (j i : ℕ) (hi : 1 ≤ i) (d : ℝ) (hd : 0 ≤ d) :
    (law p j).real {ω | 1 - d ≤ (ω i).2.1 ∨ (ω i).2.2 ≤ d} ≤ 20 * d := by
  have hx : Measurable (fun ω : Sample => (ω i).2.1) := by fun_prop
  have hy : Measurable (fun ω : Sample => (ω i).2.2) := by fun_prop
  have h := endpoint_pair_loss_le (law p j) hx hy (by norm_num : (0 : ℝ) ≤ 10) hd
    (by simpa only [endpoint, Bool.false_eq_true, ite_false, baseLaw_eq_restrict,
      ENNReal.ofReal_ofNat] using
      law_raw_endpoint_le hp j i hi false)
    (by simpa only [endpoint, ite_true, baseLaw_eq_restrict, ENNReal.ofReal_ofNat] using
      law_raw_endpoint_le hp j i hi true)
  norm_num only [show (2 : ℝ) * 10 = 20 by norm_num] at h
  exact h

def futureBadEvent (p : CircleParameterData) (j : ℕ) : Set Sample :=
  ⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
    {ω | 1 - 3 * (p.K j : ℝ) / p.N (j + 1 + n) ≤ (ω i).2.1 ∨
      (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N (j + 1 + n)}

omit hp in
theorem futureBadEvent_measurable (p : CircleParameterData) (j : ℕ) :
    MeasurableSet (futureBadEvent p j) := by
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.biUnion (p.block (j + 1 + n)).countable_toSet
  intro i _
  have hx : Measurable (fun ω : Sample => (ω i).2.1) := by fun_prop
  have hy : Measurable (fun ω : Sample => (ω i).2.2) := by fun_prop
  exact (measurableSet_le measurable_const hx).union
    (measurableSet_le hy measurable_const)

theorem future_block_loss_le (j s : ℕ) (hs : 1 ≤ s) :
    (law p j).real (⋃ i ∈ p.block s,
      {ω | 1 - 3 * (p.K j : ℝ) / p.N s ≤ (ω i).2.1 ∨
        (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N s}) ≤
      60 * (p.K j : ℝ) * (1 / (p.K s : ℝ)) := by
  let := law_isProbabilityMeasure hp j
  have hm : (0 : ℝ) < p.m s := by exact_mod_cast hp.m_pos s hs
  have hK : (0 : ℝ) < p.K s := by exact_mod_cast hp.K_pos s hs
  have hd : 0 ≤ 3 * (p.K j : ℝ) / p.N s := by
    unfold CircleParameterData.N
    positivity
  calc
    _ ≤ ∑ i ∈ p.block s, (law p j).real
        {ω | 1 - 3 * (p.K j : ℝ) / p.N s ≤ (ω i).2.1 ∨
          (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N s} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ p.block s, 20 * (3 * (p.K j : ℝ) / p.N s) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (p.mem_block_iff s i).mp hi
      exact raw_endpoint_pair_loss_le hp j i (by omega) _ hd
    _ = _ := by
      rw [Finset.sum_const, p.card_block s hs, nsmul_eq_mul]
      unfold CircleParameterData.N
      field_simp
      ring

theorem futureBadEvent_mass_le (j : ℕ) (hj : 1 ≤ j) :
    (law p j).real (futureBadEvent p j) ≤
      60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) := by
  let := law_isProbabilityMeasure hp j
  have hs : Summable (fun n : ℕ => 1 / (p.K (j + 1 + n) : ℝ)) := by
    have h := (summable_nat_add_iff j).mpr hp.summable_reciprocal
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have h := measureReal_iUnion_le_tsum_budget (law p j)
    (fun n => ⋃ i ∈ p.block (j + 1 + n),
      {ω | 1 - 3 * (p.K j : ℝ) / p.N (j + 1 + n) ≤ (ω i).2.1 ∨
        (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N (j + 1 + n)})
    (b := fun n => 60 * (p.K j : ℝ) * (1 / (p.K (j + 1 + n) : ℝ)))
    (fun n => by positivity) (hs.mul_left (60 * (p.K j : ℝ)))
    (fun n => future_block_loss_le hp j (j + 1 + n) (by omega))
  simpa only [futureBadEvent, tsum_mul_left] using h

theorem futureBadEvent_mass_le_ratio (j : ℕ) (hj : 1 ≤ j) :
    (law p j).real (futureBadEvent p j) ≤
      120 * (p.K j : ℝ) / (p.K (j + 1) : ℝ) := by
  calc
    _ ≤ 60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) :=
      futureBadEvent_mass_le hp j hj
    _ ≤ 60 * (p.K j : ℝ) * (2 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound j hj) (by positivity)
    _ = _ := by ring

omit hp in

theorem not_mem_futureBadEvent_iff (p : CircleParameterData) (j : ℕ) (ω : Sample) :
    ω ∉ futureBadEvent p j ↔ ∀ s : ℕ, j < s → ∀ i ∈ p.block s,
      (ω i).2.1 < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < (ω i).2.2 := by
  simp only [futureBadEvent, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
    not_or, not_le]
  constructor
  · intro h s hs i hi
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ s by omega)
    subst s
    exact h n i hi
  · intro h n i hi
    exact h (j + 1 + n) (by omega) i hi

end Invariant233.CircleCoupling

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem cutoff_le_sampling_horizon (j : ℕ) (hj : 1 ≤ j) :
    (p.K j : ℝ) ≤ p.Q j := by
  have hm : (200 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_200 j hj
  have hKm : (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j hj
  apply hKm.trans
  unfold CircleParameterData.Q
  have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ p.m j by linarith)
    (show (1 : ℝ) ≤ (7 / 10 : ℝ) * p.m j by linarith)
  simpa only [Real.rpow_one] using h

theorem tendsto_successive_cutoff_ratio :
    Tendsto (fun n : ℕ => (p.K (n + 1) : ℝ) / (p.K (n + 2) : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero _ _ hp.tendsto_sampling_horizon
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro n
    exact div_le_div_of_nonneg_right (hp.cutoff_le_sampling_horizon (n + 1) (by omega))
      (Nat.cast_nonneg _)

end Invariant233.CircleParameterLaws

namespace Invariant233.CircleCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem tendsto_futureBadEvent_mass :
    Tendsto (fun n : ℕ => (law p (n + 1)).real (futureBadEvent p (n + 1)))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ =>
      120 * (p.K (n + 1) : ℝ) / (p.K (n + 2) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hp.tendsto_successive_cutoff_ratio.const_mul 120
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  simpa only [Nat.add_assoc] using futureBadEvent_mass_le_ratio hp (n + 1) (by omega)

end Invariant233.CircleCoupling

end

end OAI
