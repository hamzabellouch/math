import OAI.Geometry.IsometricImmersion.Coordinates.RoundDisk
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyFinite

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def accumulatingScale (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

def accumulatingCenter (n : ℕ) : Coord := ![accumulatingScale n, 0]

def accumulatingRadius (n : ℕ) : ℝ := accumulatingScale n / 8

def accumulatingDisk (n : ℕ) : Set Coord :=
  roundClosedDisk (accumulatingCenter n) (accumulatingRadius n)

def enlargedAccumulatingDisk (n : ℕ) : Set Coord :=
  roundClosedDisk (accumulatingCenter n) (2 * accumulatingRadius n)

theorem accumulatingScale_pos (n : ℕ) : 0 < accumulatingScale n := by
  exact pow_pos (by norm_num) _

theorem accumulatingScale_le_half (n : ℕ) : accumulatingScale n ≤ (1 / 2 : ℝ) := by
  exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero n)

theorem accumulatingScale_succ (n : ℕ) :
    accumulatingScale (n + 1) = accumulatingScale n / 2 := by
  simp only [accumulatingScale, pow_succ]
  ring

theorem accumulatingScale_antitone : Antitone accumulatingScale := by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hmn 1)

theorem accumulatingScale_le_half_of_lt {m n : ℕ} (hmn : m < n) :
    accumulatingScale n ≤ accumulatingScale m / 2 := by
  rw [← accumulatingScale_succ]
  exact accumulatingScale_antitone (Nat.succ_le_of_lt hmn)

theorem accumulatingRadius_pos (n : ℕ) : 0 < accumulatingRadius n :=
  div_pos (accumulatingScale_pos n) (by norm_num)

theorem roundClosedDisk_coord_abs_le (c : Coord) {r : ℝ} (hr : 0 ≤ r)
    {p : Coord} (hp : p ∈ roundClosedDisk c r) (i : Fin 2) : |p i - c i| ≤ r := by
  have hsq : (p i - c i) ^ 2 ≤ r ^ 2 := by
    change (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 ≤ r ^ 2 at hp
    fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
    · nlinarith [sq_nonneg (p 1 - c 1)]
    · nlinarith [sq_nonneg (p 0 - c 0)]
  apply (sq_le_sq₀ (abs_nonneg _) hr).mp
  simpa only [sq_abs] using hsq

theorem accumulatingDisk_subset_enlarged (n : ℕ) :
    accumulatingDisk n ⊆ enlargedAccumulatingDisk n := by
  intro p hp
  change roundRadiusSq (accumulatingCenter n) p ≤ (accumulatingRadius n) ^ 2 at hp
  change roundRadiusSq (accumulatingCenter n) p ≤ (2 * accumulatingRadius n) ^ 2
  nlinarith [sq_nonneg (accumulatingRadius n)]

theorem accumulatingDisk_subset_enlarged_open (n : ℕ) :
    accumulatingDisk n ⊆ roundOpenDisk (accumulatingCenter n) (2 * accumulatingRadius n) := by
  intro p hp
  change roundRadiusSq (accumulatingCenter n) p ≤ (accumulatingRadius n) ^ 2 at hp
  change roundRadiusSq (accumulatingCenter n) p < (2 * accumulatingRadius n) ^ 2
  nlinarith [sq_pos_of_pos (accumulatingRadius_pos n)]

theorem enlargedAccumulatingDisk_bounds (n : ℕ) {p : Coord}
    (hp : p ∈ enlargedAccumulatingDisk n) :
    (3 / 4 : ℝ) * accumulatingScale n ≤ p 0 ∧
      p 0 ≤ (5 / 4 : ℝ) * accumulatingScale n ∧
      |p 1| ≤ accumulatingScale n / 4 := by
  have hr : 0 ≤ 2 * accumulatingRadius n :=
    (mul_pos (by norm_num) (accumulatingRadius_pos n)).le
  have hx := roundClosedDisk_coord_abs_le (accumulatingCenter n) hr hp 0
  have hy := roundClosedDisk_coord_abs_le (accumulatingCenter n) hr hp 1
  simp only [accumulatingCenter, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_zero, accumulatingRadius] at hx hy
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem enlargedAccumulatingDisk_disjoint_of_lt {m n : ℕ} (hmn : m < n) :
    Disjoint (enlargedAccumulatingDisk m) (enlargedAccumulatingDisk n) := by
  apply Set.disjoint_left.mpr
  intro p hpm hpn
  have hm := enlargedAccumulatingDisk_bounds m hpm
  have hn := enlargedAccumulatingDisk_bounds n hpn
  have hscale := accumulatingScale_le_half_of_lt hmn
  have hpos := accumulatingScale_pos m
  linarith

theorem enlargedAccumulatingDisks_pairwise_disjoint :
    Pairwise (fun m n => Disjoint (enlargedAccumulatingDisk m) (enlargedAccumulatingDisk n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact enlargedAccumulatingDisk_disjoint_of_lt hlt
  · exact (enlargedAccumulatingDisk_disjoint_of_lt hgt).symm

theorem accumulatingDisks_pairwise_disjoint :
    Pairwise (fun m n => Disjoint (accumulatingDisk m) (accumulatingDisk n)) := by
  intro m n hmn
  exact (enlargedAccumulatingDisks_pairwise_disjoint hmn).mono
    (accumulatingDisk_subset_enlarged m) (accumulatingDisk_subset_enlarged n)

theorem enlargedAccumulatingDisk_subset_square (n : ℕ) : enlargedAccumulatingDisk n ⊆ square := by
  intro p hp i
  have hb := enlargedAccumulatingDisk_bounds n hp
  have hpos := accumulatingScale_pos n
  have hhalf := accumulatingScale_le_half n
  fin_cases i
  · change -1 < p 0 ∧ p 0 < 1
    constructor <;> linarith
  · change -1 < p 1 ∧ p 1 < 1
    obtain ⟨hylo, hyhi⟩ := abs_le.mp hb.2.2
    constructor <;> linarith

theorem accumulatingDisk_subset_square (n : ℕ) : accumulatingDisk n ⊆ square :=
  (accumulatingDisk_subset_enlarged n).trans (enlargedAccumulatingDisk_subset_square n)

theorem zero_not_mem_enlargedAccumulatingDisk (n : ℕ) :
    (0 : Coord) ∉ enlargedAccumulatingDisk n := by
  intro h0
  have hb := (enlargedAccumulatingDisk_bounds n h0).1
  have hpos := accumulatingScale_pos n
  change (3 / 4 : ℝ) * accumulatingScale n ≤ 0 at hb
  linarith

theorem zero_not_mem_accumulatingDisk (n : ℕ) : (0 : Coord) ∉ accumulatingDisk n :=
  fun h => zero_not_mem_enlargedAccumulatingDisk n (accumulatingDisk_subset_enlarged n h)

theorem accumulatingDisk_isCompact (n : ℕ) : IsCompact (accumulatingDisk n) :=
  isCompact_roundClosedDisk (accumulatingCenter n) (accumulatingRadius_pos n)

theorem enlargedAccumulatingDisk_isCompact (n : ℕ) : IsCompact (enlargedAccumulatingDisk n) :=
  isCompact_roundClosedDisk (accumulatingCenter n) (mul_pos (by norm_num) (accumulatingRadius_pos n))

theorem accumulatingDisk_interior_nonempty (n : ℕ) : (interior (accumulatingDisk n)).Nonempty :=
  interior_roundClosedDisk_nonempty (accumulatingCenter n) (accumulatingRadius_pos n)

theorem tendsto_accumulatingScale : Tendsto accumulatingScale atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  convert hpow.mul (tendsto_const_nhds (x := (1 / 2 : ℝ))) using 1 <;>
    first | rfl | simp only [zero_mul]

theorem tendsto_accumulatingCenter : Tendsto accumulatingCenter atTop (𝓝 (0 : Coord)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · change Tendsto accumulatingScale atTop (𝓝 (0 : ℝ))
    exact tendsto_accumulatingScale
  · change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)
    exact tendsto_const_nhds

theorem enlargedAccumulatingDisk_norm_le (n : ℕ) {p : Coord}
    (hp : p ∈ enlargedAccumulatingDisk n) : ‖p‖ ≤ (5 / 4 : ℝ) * accumulatingScale n := by
  have hb := enlargedAccumulatingDisk_bounds n hp
  have hpos := accumulatingScale_pos n
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |p 0| ≤ (5 / 4 : ℝ) * accumulatingScale n
    rw [abs_of_nonneg (by linarith : 0 ≤ p 0)]
    exact hb.2.1
  · change |p 1| ≤ (5 / 4 : ℝ) * accumulatingScale n
    linarith [hb.2.2]

theorem eventually_enlargedAccumulatingDisk_subset {V : Set Coord} (hV : V ∈ 𝓝 (0 : Coord)) :
    ∀ᶠ n in atTop, enlargedAccumulatingDisk n ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have ht : Tendsto (fun n => (5 / 4 : ℝ) * accumulatingScale n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := (5 / 4 : ℝ))).mul tendsto_accumulatingScale
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn
  intro p hp
  apply hball
  change dist p (0 : Coord) < ε
  simpa only [dist_zero_right] using lt_of_le_of_lt (enlargedAccumulatingDisk_norm_le n hp) hn

theorem eventually_accumulatingDisk_subset {V : Set Coord} (hV : V ∈ 𝓝 (0 : Coord)) :
    ∀ᶠ n in atTop, accumulatingDisk n ⊆ V :=
  (eventually_enlargedAccumulatingDisk_subset hV).mono
    (fun n hn => (accumulatingDisk_subset_enlarged n).trans hn)

theorem eventually_all_accumulatingDisks_in_open {V : Set Coord}
    (hV : IsOpen V) (h0 : (0 : Coord) ∈ V) :
    ∃ N : ℕ, ∀ n ≥ N, accumulatingDisk n ⊆ V :=
  eventually_atTop.mp (eventually_accumulatingDisk_subset (hV.mem_nhds h0))

theorem enlargedAccumulatingDisks_locallyFinite_away_zero {p : Coord} (hp : p ≠ 0) :
    ∃ W : Set Coord, IsOpen W ∧ p ∈ W ∧
      {n : ℕ | (enlargedAccumulatingDisk n ∩ W).Nonempty}.Finite := by
  obtain ⟨W, V, hWo, hVo, hpW, h0V, hdisj⟩ := t2_separation hp
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_enlargedAccumulatingDisk_subset (hVo.mem_nhds h0V))
  refine ⟨W, hWo, hpW, (Finset.range N).finite_toSet.subset ?_⟩
  intro n hn
  change n ∈ Finset.range N
  rw [Finset.mem_range]
  by_contra hlt
  obtain ⟨q, hqD, hqW⟩ := hn
  exact (Set.disjoint_left.mp hdisj) hqW (hN n (Nat.le_of_not_gt hlt) hqD)

theorem enlargedAccumulatingDisks_locallyFinite_punctured :
    LocallyFinite (fun n : ℕ =>
      {p : {p : Coord // p ≠ 0} | p.val ∈ enlargedAccumulatingDisk n}) := by
  intro p
  obtain ⟨W, hWo, hpW, hfin⟩ := enlargedAccumulatingDisks_locallyFinite_away_zero p.property
  refine ⟨Subtype.val ⁻¹' W,
    (hWo.preimage continuous_subtype_val).mem_nhds hpW, hfin.subset ?_⟩
  intro n hn
  obtain ⟨q, hqD, hqW⟩ := hn
  exact ⟨q.val, hqD, hqW⟩

theorem accumulatingDisks_locallyFinite_punctured :
    LocallyFinite (fun n : ℕ =>
      {p : {p : Coord // p ≠ 0} | p.val ∈ accumulatingDisk n}) :=
  enlargedAccumulatingDisks_locallyFinite_punctured.subset
    (fun index _ hp => accumulatingDisk_subset_enlarged index hp)

end SmoothLocal.Geometry

end

end OAI
