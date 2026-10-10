import OAI.NumberTheory.Jacobsthal.Probability.MarkedBeginningKernel

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.KernelPotential

instance markedClock_pow_isMarkovKernel (n : ℕ) : IsMarkovKernel (markedClockKernel ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel ℝ ℝ); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsMarkovKernel (markedClockKernel ∘ₖ (markedClockKernel ^ n))
    infer_instance

lemma markedClock_cumulative_lintegral (n : ℕ) (x : ℝ) {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂(markedClockKernel ^ n) x) = ∫⁻ G, H (x+G) ∂convPow markedSpacingLaw n := by
  induction n generalizing x with
  | zero =>
    change (∫⁻ y, H y ∂Measure.dirac x) = _
    rw [lintegral_dirac' x hH,convPow_zero,
      lintegral_dirac' 0 (f := fun G : ℝ => H (x+G)) (hH.comp (measurable_const.add measurable_id)),add_zero]
  | succ n ih =>
    have hp : markedClockKernel ^ (n+1) = (markedClockKernel ^ n) ∘ₖ markedClockKernel := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ hH]
    simp_rw [ih]
    have hF : Measurable (fun y : ℝ => ∫⁻ G, H (y+G) ∂convPow markedSpacingLaw n) :=
      (hH.comp measurable_add).lintegral_prod_right'
    rw [markedClockKernel_apply,lintegral_map (g := fun G : ℝ => x+G) hF (measurable_const.add measurable_id),
      convPow_succ',Measure.lintegral_conv (f := fun G : ℝ => H (x+G))
        (hH.comp (measurable_const.add measurable_id))]
    apply lintegral_congr
    intro t
    apply lintegral_congr
    intro G
    congr 1
    ring

lemma markedClock_cumulative_law (n : ℕ) (x : ℝ) :
    (markedClockKernel ^ n) x = (convPow markedSpacingLaw n).map (fun G => x+G) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [markedClock_cumulative_lintegral n x hH,
    lintegral_map (g := fun G : ℝ => x+G) hH (measurable_const.add measurable_id)]

lemma markedClock_zero_law (n : ℕ) : (markedClockKernel ^ n) 0 = convPow markedSpacingLaw n := by
  rw [markedClock_cumulative_law]
  simp only [zero_add]
  exact Measure.map_id

lemma markedClock_renewal :
    (potential (Kernel.id : Kernel ℝ ℝ) markedClockKernel) 0 = renewalMeasure markedSpacingLaw := by
  rw [potential,Kernel.sum_apply,renewalMeasure]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.id_comp,markedClock_zero_law]

lemma markedClock_increment_lower (x : ℝ) :
    ∀ᵐ y ∂markedClockKernel x, x+Real.log (4/3) ≤ y := by
  rw [markedClockKernel_apply]
  apply (ae_map_iff (measurable_const.add measurable_id).aemeasurable measurableSet_Ici).mpr
  filter_upwards [markedSpacing_cost_lower] with G hG
  change x+Real.log (4/3) ≤ x+G
  linarith

lemma markedClock_minimum_pos : (0:ℝ) < Real.log (4/3) := Real.log_pos (by norm_num)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal
open NumberTheoryLean.KernelPotential

noncomputable def clockBelow (v : ℝ) : Kernel ℝ ℝ := markedClockKernel.restrict (s := Iio v) measurableSet_Iio
noncomputable def clockOver (v H : ℝ) : Kernel ℝ ℝ := markedClockKernel.restrict (s := Ioi (v+H)) measurableSet_Ioi

instance clockBelow_isFiniteKernel (v : ℝ) : IsFiniteKernel (clockBelow v) := by unfold clockBelow; infer_instance
instance clockOver_isFiniteKernel (v H : ℝ) : IsFiniteKernel (clockOver v H) := by unfold clockOver; infer_instance

instance clockBelow_pow_isFiniteKernel (v : ℝ) (n : ℕ) : IsFiniteKernel (clockBelow v ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel ℝ ℝ); infer_instance
  | succ n ih => rw [pow_succ']; change IsFiniteKernel (clockBelow v ∘ₖ (clockBelow v ^ n)); infer_instance

noncomputable def clockOverReward (v H : ℝ) : Kernel ℝ ℝ := by
  classical
  exact Kernel.piecewise (s := Iio v) measurableSet_Iio (clockOver v H) 0

instance clockOverReward_isFiniteKernel (v H : ℝ) : IsFiniteKernel (clockOverReward v H) := by
  classical
  unfold clockOverReward
  infer_instance

noncomputable def clockOvershoot (v H : ℝ) : ℝ≥0∞ := (potential (clockOver v H) (clockBelow v)) 0 univ

lemma clockBelow_le (v : ℝ) : clockBelow v ≤ markedClockKernel := by
  intro x
  rw [clockBelow,Kernel.restrict_apply]
  exact Measure.restrict_le_self

lemma clockBelow_ae_lt (v x : ℝ) : ∀ᵐ y ∂clockBelow v x, y < v := by
  rw [clockBelow,Kernel.restrict_apply]
  exact ae_restrict_mem measurableSet_Iio

lemma clockBelow_pow_ae_lt {v : ℝ} (hv : 0 < v) (n : ℕ) : ∀ᵐ y ∂(clockBelow v ^ n) 0, y < v := by
  cases n with
  | zero => change ∀ᵐ y ∂Measure.dirac (0:ℝ), y < v; exact (ae_dirac_iff measurableSet_Iio).mpr hv
  | succ n =>
    rw [pow_succ']
    change ∀ᵐ y ∂(clockBelow v ∘ₖ (clockBelow v ^ n)) 0, y < v
    exact Kernel.ae_comp_of_ae_ae measurableSet_Iio (Eventually.of_forall (clockBelow_ae_lt v))

lemma clockOver_mass (v H x : ℝ) : clockOver v H x univ = markedSpacingLaw (Ioi (v+H-x)) := by
  rw [clockOver,Kernel.restrict_apply,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    markedClockKernel_apply,Measure.map_apply (f := fun G : ℝ => x+G)
      (measurable_const.add measurable_id) measurableSet_Ioi]
  congr 1
  ext G
  simp only [mem_preimage,mem_Ioi]
  constructor <;> intro h <;> linarith

lemma clockOverReward_mass (v H x : ℝ) : clockOverReward v H x univ =
    if x < v then markedSpacingLaw (Ioi (v+H-x)) else 0 := by
  classical
  rw [clockOverReward,Kernel.piecewise_apply]
  by_cases hx : x < v <;> simp [hx,clockOver_mass]

lemma clock_compose_mono_right {K L : Kernel ℝ ℝ} (h : K ≤ L) (B : Kernel ℝ ℝ) :
    B ∘ₖ K ≤ B ∘ₖ L := by
  intro x
  apply Measure.le_iff.mpr
  intro S hS
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.comp_apply' _ _ _ hS]
  exact lintegral_mono' (h x) le_rfl

lemma clock_potential_mono_step {K L : Kernel ℝ ℝ} (h : K ≤ L) (B : Kernel ℝ ℝ) :
    potential B K ≤ potential B L := by
  apply potential_le_of_super B K (potential B L)
  calc
    _ ≤ B+(potential B L) ∘ₖ L := fun x => add_le_add le_rfl ((clock_compose_mono_right h _) x)
    _ = _ := (potential_unfold B L).symm

lemma clockOvershoot_guarded {v : ℝ} (hv : 0 < v) (H : ℝ) :
    (potential (clockOver v H) (clockBelow v)) 0 =
      (potential (clockOverReward v H) (clockBelow v)) 0 := by
  classical
  ext B hB
  unfold potential
  rw [Kernel.sum_apply' _ _ hB,Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
  apply lintegral_congr_ae
  filter_upwards [clockBelow_pow_ae_lt hv n] with x hx
  rw [clockOverReward,Kernel.piecewise_apply,ite_eq_left (show x ∈ Iio v from hx)]

lemma clockReward_potential_integral (v H : ℝ) :
    (potential (clockOverReward v H) markedClockKernel) 0 univ =
      ∫⁻ x, clockOverReward v H x univ ∂renewalMeasure markedSpacingLaw := by
  rw [potential,Kernel.sum_apply' _ _ MeasurableSet.univ,renewalMeasure,lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ,markedClock_zero_law]

lemma clockOvershoot_le_reward {v : ℝ} (hv : 0 < v) (H : ℝ) :
    clockOvershoot v H ≤ ∫⁻ x, clockOverReward v H x univ ∂renewalMeasure markedSpacingLaw := by
  rw [clockOvershoot,clockOvershoot_guarded hv H]
  exact ((clock_potential_mono_step (clockBelow_le v) (clockOverReward v H)) 0 univ).trans_eq
    (clockReward_potential_integral v H)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open AbsorptionCutoff.Renewal

noncomputable def clockTailPiece (v H : ℝ) (j : ℕ) : ℝ → ℝ≥0∞ :=
  (Icc (v-(j:ℝ)-1) (v-j)).indicator (fun _ => markedSpacingLaw (Ioi (H+j)))

lemma clockTailPiece_measurable (v H : ℝ) (j : ℕ) : Measurable (clockTailPiece v H j) :=
  measurable_const.indicator measurableSet_Icc

lemma clockReward_le_tail_pieces (v H x : ℝ) :
    clockOverReward v H x univ ≤ ∑' j : ℕ, clockTailPiece v H j x := by
  classical
  rw [clockOverReward_mass]
  by_cases hx : x < v
  · rw [ite_eq_left hx]
    let j : ℕ := ⌊v-x⌋₊
    have hjlo : (j:ℝ) ≤ v-x := Nat.floor_le (by linarith)
    have hjhi : v-x < (j:ℝ)+1 := Nat.lt_floor_add_one _
    have hmem : x ∈ Icc (v-(j:ℝ)-1) (v-j) := ⟨by linarith,by linarith⟩
    calc
      _ ≤ markedSpacingLaw (Ioi (H+j)) := measure_mono (fun t ht => by
        change H+(j:ℝ) < t
        change v+H-x < t at ht
        linarith)
      _ = clockTailPiece v H j x := by rw [clockTailPiece,indicator_of_mem hmem]
      _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ => clockTailPiece v H k x) j
  · rw [ite_eq_right hx]
    exact zero_le

lemma clockTailPiece_integral (v H : ℝ) (j : ℕ) :
    (∫⁻ x, clockTailPiece v H j x ∂renewalMeasure markedSpacingLaw) =
      markedSpacingLaw (Ioi (H+j))*renewalMeasure markedSpacingLaw (Icc (v-(j:ℝ)-1) (v-j)) := by
  rw [clockTailPiece,lintegral_indicator measurableSet_Icc]
  simp [lintegral_const]

theorem clock_renewal_reward_tail_bound : ∃ C : ℝ, 0 < C ∧ ∀ v H : ℝ,
    (∫⁻ x, clockOverReward v H x univ ∂renewalMeasure markedSpacingLaw) ≤
      ENNReal.ofReal C*(∑' j : ℕ, markedSpacingLaw (Ioi (H+j))) := by
  obtain ⟨C,hC,hcell⟩ := marked_renewal_cell_bound 1
  refine ⟨C,hC,?_⟩
  intro v H
  calc
    _ ≤ ∫⁻ x, ∑' j : ℕ, clockTailPiece v H j x ∂renewalMeasure markedSpacingLaw :=
      lintegral_mono (clockReward_le_tail_pieces v H)
    _ = ∑' j : ℕ, ∫⁻ x, clockTailPiece v H j x ∂renewalMeasure markedSpacingLaw :=
      lintegral_tsum (fun j => (clockTailPiece_measurable v H j).aemeasurable)
    _ ≤ ∑' j : ℕ, ENNReal.ofReal C*markedSpacingLaw (Ioi (H+j)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      rw [clockTailPiece_integral]
      have he := hcell (v-(j:ℝ)-1)
      rw [show v-(j:ℝ)-1+1=v-j by ring] at he
      have hm := mul_le_mul_right he (markedSpacingLaw (Ioi (H+j)))
      simpa only [mul_comm] using hm
    _ = _ := ENNReal.tsum_mul_left

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
