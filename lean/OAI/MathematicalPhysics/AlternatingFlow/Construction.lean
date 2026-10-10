import OAI.MathematicalPhysics.AlternatingFlow.LocalRules
import OAI.MathematicalPhysics.AlternatingFlow.SpatialCurls
import OAI.MathematicalPhysics.AlternatingFlow.TimeGlue

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Construction

def donorIndex (n : ℕ) : Fin 3 :=
  letI := neZeroThree
  if n % 2 = 0 then 1 else 2

def receiverIndex (n : ℕ) : Fin 3 :=
  letI := neZeroThree
  if n % 2 = 0 then 2 else 1

lemma indices_distinct (n : ℕ) : receiverIndex n ≠ 0 ∧ donorIndex n ≠ receiverIndex n ∧
    donorIndex n ≠ 0 := by
  unfold donorIndex receiverIndex
  split_ifs <;> decide

noncomputable def slot (M : Machine) (N n : ℕ) : Space → Space :=
  letI := neZeroThree
  Spatial.localizedShear (donorIndex n) (receiverIndex n) 0
    (LocalRule.write M N n) (LocalRule.signal M N n)

noncomputable def loading (M : Machine) (w : List ℕ) : Space → Space :=
  letI := neZeroThree
  Spatial.localizedShear 2 1 0
    (fun _ => Scales.ε M.base w.length 0 * M.recordedBlock w 0)
    (fun _ => 1 - Scales.ε M.base w.length 0)

noncomputable def piece (M : Machine) (w : List ℕ) : ℕ → Space → Space :=
  fun n => Nat.casesOn n (loading M w) (fun k => slot M w.length k)

noncomputable def velocity (M : Machine) (w : List ℕ) : Velocity :=
  TimeGlue.glue Profiles.pulse (piece M w)

lemma slot_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (slot M N n) :=
  Spatial.localizedShear_smooth _ _ _ _ _ (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n)

lemma loading_smooth (M : Machine) (w : List ℕ) : ContDiff ℝ ∞ (loading M w) :=
  Spatial.localizedShear_smooth _ _ _ _ _ contDiff_const contDiff_const

lemma piece_smooth (M : Machine) (w : List ℕ) (n : ℕ) : ContDiff ℝ ∞ (piece M w n) := by
  cases n with
  | zero => exact loading_smooth M w
  | succ n => exact slot_smooth M w.length n

lemma piece_support (M : Machine) (w : List ℕ) (n : ℕ) :
    tsupport (piece M w n) ⊆ Spatial.box := by
  cases n <;> exact Spatial.localizedShear_support _ _ _ _ _

lemma piece_div (M : Machine) (w : List ℕ) (n : ℕ) (x : Space) :
    (∑ i : Fin 3, Spatial.d i (piece M w n) x i) = 0 := by
  cases n with
  | zero => exact Spatial.localizedShear_div _ _ _ _ _ contDiff_const contDiff_const x
  | succ n =>
    exact Spatial.localizedShear_div _ _ _ _ _ (LocalRule.write_smooth M w.length n)
      (LocalRule.signal_smooth M w.length n) x

lemma velocity_smooth (M : Machine) (w : List ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (velocity M w)) :=
  TimeGlue.smooth Profiles.pulse Profiles.pulse_zero_left Profiles.pulse_smooth
    (piece M w) (piece_smooth M w)

lemma velocity_supported (M : Machine) (w : List ℕ) (t : ℝ) :
    Function.support (velocity M w t) ⊆ Spatial.box := by
  intro x hx
  by_contra hn
  have hz (k : ℕ) : piece M w k x = 0 := by
    by_contra hk
    exact hn (piece_support M w k (subset_closure hk))
  exact hx (by simp [velocity, TimeGlue.glue, hz])

lemma velocity_rest (M : Machine) (w : List ℕ) (x : Space) : velocity M w 0 x = 0 := by
  rw [velocity, TimeGlue.pulse_slot _ 0 0 (by norm_num) x]
  simp [Profiles.pulse_zero_left]

lemma velocity_div (M : Machine) (w : List ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    div (velocity M w) t x = 0 := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  have heq : velocity M w t = (fun x => Profiles.pulse (t - k) • piece M w k x) :=
    funext (TimeGlue.pulse_slot _ k t hk)
  unfold div dx
  rw [heq]
  have hd := (piece_smooth M w k).differentiable (by simp) x
  change (∑ i : Fin 3, (fderiv ℝ (Profiles.pulse (t - k) • piece M w k) x (e i)) i) = 0
  simp only [fderiv_const_smul hd, smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  change Profiles.pulse (t - k) * (∑ i : Fin 3, Spatial.d i (piece M w k) x i) = 0
  rw [piece_div, mul_zero]

lemma slot_plateau (M : Machine) (N n : ℕ) (x : Space) (hx : x ∈ Spatial.plateau) :
    slot M N n x = LocalRule.write M N n (x (donorIndex n)) • e (receiverIndex n) +
      LocalRule.signal M N n (x (donorIndex n)) • e 0 :=
  Spatial.localizedShear_plateau _ _ _ (indices_distinct n).1 (indices_distinct n).2.1
    (indices_distinct n).2.2 _ _ (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n) x hx

lemma loading_plateau (M : Machine) (w : List ℕ) (x : Space) (hx : x ∈ Spatial.plateau) :
    loading M w x = (Scales.ε M.base w.length 0 * M.recordedBlock w 0) • e 1 +
      (1 - Scales.ε M.base w.length 0) • e 0 :=
  Spatial.localizedShear_plateau 2 1 0 (by decide) (by decide) (by decide)
    _ _ contDiff_const contDiff_const x hx

end Construction
end AlternatingNS

namespace AlternatingNS
namespace Construction

lemma donorIndex_succ (n : ℕ) : donorIndex (n + 1) = receiverIndex n := by
  unfold donorIndex receiverIndex
  split_ifs <;> omega

lemma donorIndex_eq (j n : ℕ) : donorIndex j = donorIndex n ↔ j % 2 = n % 2 := by
  unfold donorIndex
  split_ifs <;> norm_num <;> omega

noncomputable def memory (M : Machine) (w : List ℕ) (n : ℕ) : Space :=
  ∑ j ∈ Finset.range (n + 1),
    (Scales.ε M.base w.length j * M.recordedBlock w j) • e (donorIndex j)

noncomputable def history (M : Machine) (w : List ℕ) (n : ℕ) : Space :=
  memory M w n + Detector.signal M.base w.length (fun j => M.isHalting (M.run w j)) n • e 0

noncomputable def displacement (M : Machine) (w : List ℕ) : ℕ → Space
  | 0 => (Scales.ε M.base w.length 0 * M.recordedBlock w 0) • e 1 +
      (1 - Scales.ε M.base w.length 0) • e 0
  | n + 1 => (Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1)) •
      e (receiverIndex n) +
      Detector.increment M.base w.length (fun j => M.isHalting (M.run w j)) n • e 0

noncomputable def node (M : Machine) (w : List ℕ) : ℕ → Space
  | 0 => observedParticle
  | n + 1 => history M w n

noncomputable def path (M : Machine) (w : List ℕ) (t : ℝ) : Space :=
  observedParticle + TimeGlue.glue Profiles.clock (fun k (_ : Unit) => displacement M w k) t ()

lemma memory_zero_coord (M : Machine) (w : List ℕ) (n : ℕ) : memory M w n 0 = 0 := by
  have h0 (j : ℕ) : (0 : Fin 3) ≠ donorIndex j := (indices_distinct j).2.2.symm
  simp [memory, WithLp.ofLp_sum, Finset.sum_apply, Spatial.e_apply, h0]

lemma memory_donor (M : Machine) (w : List ℕ) (n : ℕ) :
    memory M w n (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  simp only [memory, Encoding.donor, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Spatial.e_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [donorIndex_eq, eq_comm (a := n % 2) (b := j % 2), mul_ite, mul_one, mul_zero]

lemma memory_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    memory M w (n + 1) = memory M w n +
      (Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1)) • e (receiverIndex n) := by
  simp only [memory, Finset.sum_range_succ (n := n + 1), donorIndex_succ]

lemma history_zero_coord (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w n 0 = Detector.signal M.base w.length (fun j => M.isHalting (M.run w j)) n := by
  simp [history, PiLp.add_apply, memory_zero_coord, PiLp.smul_apply, Spatial.e_apply]

lemma history_donor (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w n (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  simp [history, PiLp.add_apply, memory_donor, PiLp.smul_apply, Spatial.e_apply, (indices_distinct n).2.2]

lemma history_succ (M : Machine) (w : List ℕ) (n : ℕ) :
    history M w (n + 1) = history M w n + displacement M w (n + 1) := by
  simp only [history, memory_succ, Detector.signal, displacement, add_smul]
  abel

lemma observedParticle_eq : observedParticle = -e 0 := by
  ext i
  fin_cases i <;> norm_num [observedParticle, e, PiLp.single_apply, PiLp.neg_apply,
    EuclideanSpace.single, EuclideanSpace.equiv]

lemma node_succ (M : Machine) (w : List ℕ) (k : ℕ) :
    node M w (k + 1) = node M w k + displacement M w k := by
  cases k with
  | zero =>
    simp only [node, history, memory, Nat.zero_add, Finset.sum_range_one, donorIndex, Nat.zero_mod,
      ite_true, Detector.signal, displacement, observedParticle_eq, sub_smul, one_smul, neg_smul]
    abel
  | succ n => exact history_succ M w n

lemma node_sum (M : Machine) (w : List ℕ) (k : ℕ) :
    node M w k = observedParticle + ∑ j ∈ Finset.range k, displacement M w j := by
  induction k with
  | zero => simp [node]
  | succ k ih => rw [node_succ, ih, Finset.sum_range_succ, add_assoc]

lemma path_slot (M : Machine) (w : List ℕ) (k : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) :
    path M w t = node M w k + Profiles.clock (t - k) • displacement M w k := by
  rw [path, TimeGlue.clock_slot _ k t ht (), ← add_assoc, ← node_sum]

lemma path_node (M : Machine) (w : List ℕ) (k : ℕ) : path M w k = node M w k := by
  rw [path_slot M w k k (by constructor <;> linarith)]
  simp [Profiles.clock_zero]

lemma memory_bound (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (n : ℕ) (i : Fin 3) : 0 ≤ memory M w n i ∧ memory M w n i < 1 / 4 := by
  have hb := M.base_ge_four
  have he (j : ℕ) := Scales.ε_nonneg M.base w.length j (by omega)
  have hC (j : ℕ) := M.recordedBlock_mem hM w hw j
  have hm := Encoding.tailMax_lt_one M.base (by omega)
  have hterm (j : ℕ) : 0 ≤ ((Scales.ε M.base w.length j * M.recordedBlock w j) •
      e (donorIndex j)) i ∧
      ((Scales.ε M.base w.length j * M.recordedBlock w j) • e (donorIndex j)) i ≤
        Scales.ε M.base w.length j := by
    simp only [PiLp.smul_apply, Spatial.e_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact ⟨mul_nonneg (he j) (hC j).1, mul_le_of_le_one_right (he j) ((hC j).2.trans hm.le)⟩
    · simp only [mul_zero]
      exact ⟨le_rfl, he j⟩
  simp only [memory, WithLp.ofLp_sum, Finset.sum_apply]
  refine ⟨Finset.sum_nonneg (fun j _ => (hterm j).1), ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), Scales.ε M.base w.length j :=
      Finset.sum_le_sum (fun j _ => (hterm j).2)
    _ ≤ ∑' j, Scales.ε M.base w.length j :=
      (Scales.summable_ε M.base w.length (by omega)).sum_le_tsum _ (fun j _ => he j)
    _ ≤ 2 * Scales.ε M.base w.length 0 := Scales.total_memory_le _ _ (by omega)
    _ < 1 / 4 := Scales.initial_memory_small _ _ hb

lemma node_plateau (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (k : ℕ) : node M w k ∈ Spatial.plateau := by
  have hb := M.base_ge_four
  intro i
  cases k with
  | zero =>
    simp only [node, observedParticle_eq, PiLp.neg_apply, Spatial.e_apply]
    split_ifs <;> norm_num
  | succ n =>
    change |history M w n i| < 2
    by_cases hi : i = 0
    · rw [hi, history_zero_coord]
      have hp := Detector.signal_in_plateau M.base w.length hb
        (fun j => M.isHalting (M.run w j)) n
      exact (abs_lt.2 hp).trans (by norm_num)
    · simp only [history, PiLp.add_apply, PiLp.smul_apply, Spatial.e_apply,
        ite_eq_right hi, smul_eq_mul, mul_zero, add_zero]
      rw [abs_of_nonneg (memory_bound M hM w hw n i).1]
      exact (memory_bound M hM w hw n i).2.trans (by norm_num)

lemma segment_plateau (a b : Space) (ha : a ∈ Spatial.plateau) (hb : b ∈ Spatial.plateau)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) : (1 - θ) • a + θ • b ∈ Spatial.plateau := by
  intro i
  have hai := abs_lt.mp (ha i)
  have hbi := abs_lt.mp (hb i)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  apply abs_lt.mpr
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (le_of_lt (sub_pos.mpr hai.2)),
    mul_nonneg hθ.1 (le_of_lt (sub_pos.mpr hbi.2)),
    mul_nonneg (sub_nonneg.mpr hθ.2) (le_of_lt (sub_pos.mpr hai.1)),
    mul_nonneg hθ.1 (le_of_lt (sub_pos.mpr hbi.1))]

lemma path_plateau (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (t : ℝ) (ht : 0 ≤ t) : path M w t ∈ Spatial.plateau := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [path_slot M w k t hk]
  have heq : node M w k + Profiles.clock (t - k) • displacement M w k =
      (1 - Profiles.clock (t - k)) • node M w k + Profiles.clock (t - k) • node M w (k + 1) := by
    rw [node_succ, smul_add, sub_smul, one_smul]
    abel
  rw [heq]
  exact segment_plateau _ _ (node_plateau M hM w hw k) (node_plateau M hM w hw (k + 1))
    _ (Profiles.clock_mem _)

end Construction
end AlternatingNS

namespace AlternatingNS
namespace Construction

lemma path_donor (M : Machine) (w : List ℕ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc ((n : ℝ) + 1) (n + 1 + 1)) :
    path M w t (donorIndex n) = Encoding.donor M.base w.length (M.recordedBlock w) n := by
  have ht' : t ∈ Set.Icc ((n + 1 : ℕ) : ℝ) ((n + 1 : ℕ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  rw [path_slot M w (n + 1) t ht']
  simp only [node, PiLp.add_apply, PiLp.smul_apply, history_donor, displacement,
    Spatial.e_apply, (indices_distinct n).2.1, (indices_distinct n).2.2,
    ite_false, smul_eq_mul, mul_zero, add_zero]

lemma piece_path (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (k : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (k : ℝ) (k + 1)) :
    piece M w k (path M w t) = displacement M w k := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg k) ht.1
  have hp := path_plateau M hM w hw t ht0
  cases k with
  | zero => exact loading_plateau M w _ hp
  | succ n =>
    change slot M w.length n (path M w t) = _
    rw [slot_plateau M w.length n _ hp,
      path_donor M w n t (by simpa only [Nat.cast_add, Nat.cast_one] using ht),
      LocalRule.write_run M hM w hw, LocalRule.signal_run M hM w hw]
    rfl

lemma velocity_path (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w)
    (t : ℝ) (ht : 0 ≤ t) :
    velocity M w t (path M w t) =
      TimeGlue.glue Profiles.pulse (fun k (_ : Unit) => displacement M w k) t () := by
  let k := ⌊t⌋₊
  have hk : t ∈ Set.Icc (k : ℝ) (k + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [velocity, TimeGlue.pulse_slot _ k t hk, TimeGlue.pulse_slot _ k t hk,
    piece_path M hM w hw k t hk]

theorem path_isTrajectory (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) :
    IsTrajectory (velocity M w) observedParticle (path M w) := by
  refine ⟨by simpa only [Nat.cast_zero, node] using path_node M w 0, ?_⟩
  intro t ht
  rw [velocity_path M hM w hw t ht]
  exact ((TimeGlue.hasDerivAt Profiles.clock Profiles.pulse
    (fun s hs => Profiles.clock_zero s (by linarith)) Profiles.pulse_zero_left
    Profiles.clock_hasDeriv (fun k (_ : Unit) => displacement M w k) t ()).const_add
      observedParticle).hasDerivWithinAt

lemma path_loading_coord (M : Machine) (w : List ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    path M w t 0 = Detector.loading M.base w.length (Profiles.clock t) := by
  rw [path_slot M w 0 t (by simpa using ht)]
  simp [node, observedParticle_eq, displacement, PiLp.add_apply, PiLp.smul_apply,
    PiLp.neg_apply, Spatial.e_apply, Detector.loading]

lemma path_slot_coord (M : Machine) (w : List ℕ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc ((n : ℝ) + 1) (n + 1 + 1)) :
    path M w t 0 = Detector.during M.base w.length (fun j => M.isHalting (M.run w j)) n
      (Profiles.clock (t - (n + 1))) := by
  rw [path_slot M w (n + 1) t (by simpa only [Nat.cast_add, Nat.cast_one] using ht)]
  simp [node, displacement, PiLp.add_apply, PiLp.smul_apply, Spatial.e_apply,
    (indices_distinct n).1.symm, Detector.during, history_zero_coord]

theorem path_reachability (M : Machine) (w : List ℕ) :
    (∃ t : ℝ, 0 ≤ t ∧ 0 < path M w t 0) ↔ M.Halts w := by
  have hb := M.base_ge_four
  constructor
  · rintro ⟨t, ht, hp⟩
    have hk : t ∈ Set.Icc (⌊t⌋₊ : ℝ) (⌊t⌋₊ + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
    generalize hfloor : ⌊t⌋₊ = k at hk
    cases k with
    | zero =>
      have ht' : t ∈ Set.Icc 0 1 := by simpa using hk
      rw [path_loading_coord M w t ht'] at hp
      exact False.elim ((Detector.loading_negative M.base w.length (by omega) _
        (Profiles.clock_mem t)).not_gt hp)
    | succ n =>
      rw [path_slot_coord M w n t (by simpa only [Nat.cast_add, Nat.cast_one] using hk)] at hp
      exact (Detector.machine_scalar_reachability M.base (by omega) M w).mp
        ⟨n, _, Profiles.clock_mem _, hp⟩
  · intro h
    let n := Nat.find h
    have hn : M.isHalting (M.run w n) = true := Nat.find_spec h
    have hprev : ∀ j < n, M.isHalting (M.run w j) = false :=
      fun j hj => Bool.eq_false_iff.2 (Nat.find_min h hj)
    refine ⟨((n + 1 + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [path_node]
    change 0 < history M w (n + 1) 0
    rw [history_zero_coord, Detector.signal_first_halt M.base w.length _ n hprev hn]
    exact Scales.ε_pos M.base w.length (n + 1) (by omega)

end Construction
end AlternatingNS

end OAI
