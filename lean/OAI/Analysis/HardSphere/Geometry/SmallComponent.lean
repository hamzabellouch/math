import Mathlib
import OAI.Analysis.HardSphere.Geometry.FilledRegion

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

def SmallComponent (h : ℝ) (C : Finset Vertex) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, ∀ j, h * |(u j : ℝ) - v j| ≤ 1

lemma small_fill_coordinate {h : ℝ} (hh : 0 ≤ h) {C : Finset Vertex}
    (hC : SmallComponent h C) {z c : Vertex} (hz : z ∈ fill C) (hc : c ∈ C)
    (i : Fin 3) : h * |(z i : ℝ) - c i| ≤ 1 := by
  obtain ⟨⟨u, hu, huz⟩, ⟨v, hv, hzv⟩⟩ := fill_subset_coordinateBox C hz i
  have hu' : (u i : ℝ) ≤ z i := by exact_mod_cast huz
  have hv' : (z i : ℝ) ≤ v i := by exact_mod_cast hzv
  have huc := hC u hu c hc i
  have hvc := hC v hv c hc i
  have huv := le_abs_self ((u i : ℝ) - c i)
  have hcu := neg_abs_le ((u i : ℝ) - c i)
  have hvv := le_abs_self ((v i : ℝ) - c i)
  rw [show h * |(z i : ℝ) - c i| = |h * ((z i : ℝ) - c i)| by
    rw [abs_mul, abs_of_nonneg hh], abs_le]
  have hm₁ := mul_le_mul_of_nonneg_left hu' hh
  have hm₂ := mul_le_mul_of_nonneg_left hv' hh
  have hm₃ := mul_le_mul_of_nonneg_left hcu hh
  have hm₄ := mul_le_mul_of_nonneg_left hvv hh
  constructor <;> nlinarith

def microColumn (L : Length) (h : ℝ) (z : Vertex) : Set (Torus L) :=
  Set.univ.pi fun j ↦ Metric.closedBall
    ((h * (z j : ℝ) + h/2 - 1/2 : ℝ) : AddCircle L.val)
    (if j = 0 then 1 + h/2 else h/2)

lemma small_fill_subset_columns {L : Length} {h : ℝ} (hh : 0 ≤ h)
    {C : Finset Vertex} (hC : SmallComponent h C) :
    filledRegion L h C ⊆ ⋃ c ∈ C, microColumn L h c := by
  intro x hx
  obtain ⟨z, hz, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨c, hc, hcol⟩ := fill_column_meets C hz 0
  refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
  obtain ⟨u, hu, rfl⟩ := hx
  intro j _
  apply (coordinate_dist_lift_le L (u j) (h * (c j : ℝ) + h/2 - 1/2)).trans
  have hl := hu.1 j
  have hr := hu.2 j
  change h * (z j : ℝ) - 1/2 ≤ u j at hl
  change u j ≤ h * ((z j : ℝ)+1) - 1/2 at hr
  by_cases hj : j = 0
  · subst j
    simp only [ite_true]
    have hb := small_fill_coordinate hh hC hz hc 0
    have hb' : |h * ((z 0 : ℝ) - c 0)| ≤ 1 := by
      simpa only [abs_mul, abs_of_nonneg hh] using hb
    obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb'
    apply abs_le.mpr
    constructor <;> nlinarith
  · simp only [ite_eq_right hj]
    have he := hcol j hj
    rw [← he] at hl hr
    apply abs_le.mpr
    constructor <;> nlinarith

lemma volume_microColumn_le (L : Length) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (z : Vertex) :
    (volume : Measure (Torus L)) (microColumn L h z) ≤ ENNReal.ofReal (3*h^2) := by
  unfold microColumn
  rw [volume_pi_pi]
  simp only [AddCircle.volume_closedBall]
  have hb (j : Fin 3) : ENNReal.ofReal (min L.val
      (2 * (if j = 0 then 1 + h/2 else h/2))) ≤
      (if j = 0 then ENNReal.ofReal 3 else ENNReal.ofReal h) := by
    split_ifs with hj
    · apply ENNReal.ofReal_le_ofReal
      exact (min_le_right _ _).trans (by linarith)
    · apply ENNReal.ofReal_le_ofReal
      exact (min_le_right _ _).trans (by linarith)
  calc
    _ ≤ ∏ j : Fin 3, (if j = 0 then ENNReal.ofReal 3 else ENNReal.ofReal h) :=
      Finset.prod_le_prod fun j _ ↦ hb j
    _ = ENNReal.ofReal (3*h^2) := by
      simp [Fin.prod_univ_succ, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
        ENNReal.ofReal_mul hh, pow_two]

lemma microColumn_eq_of_projection {L : Length} {J : ℕ} {h : ℝ}
    (hperiod : L.val = h * J) {w z : Vertex}
    (he : torusProjection J w = torusProjection J z) :
    microColumn L h w = microColumn L h z := by
  have hc (j : Fin 3) :
      ((h * (w j : ℝ) + h/2 - 1/2 : ℝ) : AddCircle L.val) =
      ((h * (z j : ℝ) + h/2 - 1/2 : ℝ) : AddCircle L.val) := by
    have hj := congrFun he j
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w j) (z j) J).mp hj
    have hkr : (z j : ℝ) - w j = (J : ℝ) * k := by exact_mod_cast hk
    have hr : h * (z j : ℝ) + h/2 - 1/2 =
        (h * (w j : ℝ) + h/2 - 1/2) + (k : ℝ) * L.val := by
      rw [hperiod]
      linear_combination h * hkr
    rw [hr, AddCircle.coe_add]
    have hk0 : (((k : ℝ) * L.val : ℝ) : AddCircle L.val) = 0 := by
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    rw [hk0, add_zero]
  simp only [microColumn, hc]

def bathWitnessCover {n : ℕ} {L : Length} (h : ℝ) (Y : Configuration n L) : Finset Vertex :=
  Finset.univ.biUnion fun i ↦ witnessBox h
    (fun j ↦ (AddCircle.equivIco L.val 0 (Y i j)).val)

lemma card_bathWitnessCover_le {n : ℕ} {L : Length} (h : ℝ) (Y : Configuration n L) :
    (bathWitnessCover h Y).card ≤ 343 * n := by
  apply Finset.card_biUnion_le.trans
  simp only [card_witnessBox, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  omega

lemma bad_has_bathWitness {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ} (hh : 0 < h)
    (hperiod : L.val = h * J) (hr : r ≤ 2*h) (Y : Configuration n L)
    {z : Vertex} (hz : z ∈ bad h r Y) :
    ∃ w ∈ bathWitnessCover h Y, torusProjection J w = torusProjection J z := by
  obtain ⟨x, hx, i, hi⟩ := hz
  let c : Point := fun j ↦ (AddCircle.equivIco L.val 0 (Y i j)).val
  have hc : liftPoint L c = Y i := by ext j; exact AddCircle.coe_equivIco
  obtain ⟨w, hw, he⟩ := ball_microCube_witness hh hperiod hr c hx (by simpa [hc] using hi)
  exact ⟨w, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩, he⟩

def smallFills {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) : Set (Torus L) :=
  {x | ∃ C, IsBadComponent (bad h r Y) C ∧ SmallComponent h C ∧ x ∈ filledRegion L h C}

theorem volume_smallFills_le {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hperiod : L.val = h * J) (hr : r ≤ 2*h)
    (Y : Configuration n L) :
    (volume : Measure (Torus L)) (smallFills h r Y) ≤ ENNReal.ofReal (1029*h^2*n) := by
  have hsub : smallFills h r Y ⊆ ⋃ w ∈ bathWitnessCover h Y, microColumn L h w := by
    rintro x ⟨C, hC, hs, hx⟩
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (small_fill_subset_columns hh.le hs hx)
    obtain ⟨w, hw, he⟩ := bad_has_bathWitness hh hperiod hr Y (hC.subset hc)
    refine Set.mem_iUnion₂.mpr ⟨w, hw, ?_⟩
    rwa [microColumn_eq_of_projection hperiod he]
  calc
    _ ≤ volume (⋃ w ∈ bathWitnessCover h Y, microColumn L h w) := measure_mono hsub
    _ ≤ ∑ w ∈ bathWitnessCover h Y, volume (microColumn L h w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ bathWitnessCover h Y, ENNReal.ofReal (3*h^2) :=
      Finset.sum_le_sum fun w _ ↦ volume_microColumn_le L hh.le hh1 w
    _ = ENNReal.ofReal (((bathWitnessCover h Y).card : ℝ) * (3*h^2)) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : ((bathWitnessCover h Y).card : ℝ) ≤ 343*n := by
        exact_mod_cast card_bathWitnessCover_le h Y
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg h)]

end HardSphere.BathSlice

end

end OAI
