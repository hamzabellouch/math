import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Chi
import OAI.Analysis.HardSphere.Geometry.DiscreteTorus
import OAI.Analysis.HardSphere.Geometry.BadComponent

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma coordinate_dist_lift_le (L : Length) (u v : ℝ) :
    dist (u : AddCircle L.val) (v : AddCircle L.val) ≤ |u - v| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma volume_microCube_le (L : Length) {h : ℝ} (hh : 0 ≤ h) (z : Vertex) :
    (volume : Measure (Torus L)) (microCube L h z) ≤ ENNReal.ofReal (h^3) := by
  let c : Point := fun j ↦ h * (z j : ℝ) + h / 2 - 1/2
  have hsub : microCube L h z ⊆
      Set.univ.pi (fun j ↦ Metric.closedBall ((c j : ℝ) : AddCircle L.val) (h/2)) := by
    rintro x ⟨y, hy, rfl⟩ j _
    apply (coordinate_dist_lift_le L (y j) (c j)).trans
    apply abs_le.mpr
    have hl := hy.1 j
    have hu := hy.2 j
    constructor <;> dsimp [c] at * <;> linarith
  calc
    _ ≤ volume (Set.univ.pi (fun j ↦
        Metric.closedBall ((c j : ℝ) : AddCircle L.val) (h/2))) := measure_mono hsub
    _ = ∏ j : Fin 3, ENNReal.ofReal (min L.val (2 * (h/2))) := by
      rw [volume_pi_pi]
      simp only [AddCircle.volume_closedBall]
    _ ≤ ∏ _j : Fin 3, ENNReal.ofReal h := by
      apply Finset.prod_le_prod
      intro j _
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
        (min_le_right L.val (2 * (h / 2)))
    _ = ENNReal.ofReal (h^3) := by simp [ENNReal.ofReal_pow hh]

def filledRegion (L : Length) (h : ℝ) (C : Finset Vertex) : Set (Torus L) :=
  ⋃ z ∈ fill C, microCube L h z

lemma volume_finite_microCubes_le (L : Length) {h : ℝ} (hh : 0 ≤ h)
    (S : Finset Vertex) :
    (volume : Measure (Torus L)) (⋃ z ∈ S, microCube L h z) ≤
      ENNReal.ofReal ((S.card : ℝ) * h^3) := by
  calc
    _ ≤ ∑ z ∈ S, volume (microCube L h z) := measure_biUnion_finset_le S _
    _ ≤ ∑ _z ∈ S, ENNReal.ofReal (h^3) :=
      Finset.sum_le_sum fun z _ ↦ volume_microCube_le L hh z
    _ = _ := by simp [ENNReal.ofReal_mul, nsmul_eq_mul]

lemma volume_filledRegion_le_columns (L : Length) {h : ℝ} (hh : 0 ≤ h)
    (C : Finset Vertex) (i : Fin 3) (lo hi : ℤ)
    (hb : ∀ c ∈ C, lo ≤ c i ∧ c i ≤ hi) :
    (volume : Measure (Torus L)) (filledRegion L h C) ≤
      ENNReal.ofReal ((C.card : ℝ) * ((hi - lo + 1).toNat : ℝ) * h^3) := by
  have hsub : filledRegion L h C ⊆
      ⋃ z ∈ columnCover C i lo hi, microCube L h z := by
    intro x hx
    obtain ⟨z, hz, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨z, fill_subset_columnCover C i lo hi hb hz, hx⟩
  calc
    _ ≤ volume (⋃ z ∈ columnCover C i lo hi, microCube L h z) := measure_mono hsub
    _ ≤ ENNReal.ofReal (((columnCover C i lo hi).card : ℝ) * h^3) :=
      volume_finite_microCubes_le L hh _
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hh 3)
      exact_mod_cast card_columnCover_le C i lo hi

theorem volume_small_filledRegion (L : Length) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (C : Finset Vertex) (i : Fin 3) (lo hi : ℤ) (hlh : lo ≤ hi)
    (hb : ∀ c ∈ C, lo ≤ c i ∧ c i ≤ hi)
    (hspan : h * ((hi : ℝ) - lo) ≤ 1) :
    (volume : Measure (Torus L)) (filledRegion L h C) ≤
      ENNReal.ofReal (3 * h^2 * C.card) := by
  apply (volume_filledRegion_le_columns L hh C i lo hi hb).trans
  apply ENNReal.ofReal_le_ofReal
  have hw : ((hi - lo + 1).toNat : ℝ) = (hi : ℝ) - lo + 1 := by
    have ht : ((hi - lo + 1).toNat : ℤ) = hi - lo + 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast ht
  rw [hw]
  have hs : h * ((hi : ℝ) - lo + 1) ≤ 3 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg h)
  have hc := mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ C.card by positivity)
  nlinarith

def witnessBox (h : ℝ) (c : Point) : Finset Vertex :=
  Finset.Icc (fun j ↦ ⌊(c j + 1/2) / h⌋ - 3)
    (fun j ↦ ⌊(c j + 1/2) / h⌋ + 3)

lemma card_witnessBox (h : ℝ) (c : Point) : (witnessBox h c).card = 343 := by
  unfold witnessBox
  rw [Pi.card_Icc]
  have hc (j : Fin 3) :
      (Finset.Icc (⌊(c j + 1/2) / h⌋ - 3) (⌊(c j + 1/2) / h⌋ + 3)).card = 7 := by
    rw [Int.card_Icc]
    omega
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

lemma interval_ball_witness {h r c u : ℝ} {z : ℤ}
    (hh : 0 < h) (hr : r ≤ 2*h)
    (hul : h * z - 1/2 ≤ u) (huu : u ≤ h * ((z : ℝ)+1) - 1/2)
    (hud : |u - c| ≤ r) :
    ⌊(c + 1/2) / h⌋ - 3 ≤ z ∧ z ≤ ⌊(c + 1/2) / h⌋ + 3 := by
  have hl := (le_div_iff₀ hh).mp (Int.floor_le ((c + 1/2) / h))
  have hu := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((c + 1/2) / h))
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hud
  constructor
  · have he : ((⌊(c + 1/2) / h⌋ : ℤ) : ℝ) - 3 ≤ z := by nlinarith
    exact_mod_cast he
  · have he : (z : ℝ) ≤ (⌊(c + 1/2) / h⌋ : ℝ) + 3 := by nlinarith
    exact_mod_cast he

lemma ball_microCube_witness {L : Length} {J : ℕ} {h r : ℝ} (hh : 0 < h)
    (hperiod : L.val = h * J) (hr : r ≤ 2*h)
    (c : Point) {z : Vertex} {x : Torus L}
    (hx : x ∈ microCube L h z) (hd : torusDistance L x (liftPoint L c) ≤ r) :
    ∃ w ∈ witnessBox h c, torusProjection J w = torusProjection J z := by
  obtain ⟨u, hu, rfl⟩ := hx
  let k : Vertex := fun j ↦ round (L.val⁻¹ * (u j - c j))
  let w : Vertex := fun j ↦ z j - k j * (J : ℤ)
  refine ⟨w, ?_, ?_⟩
  · apply Finset.mem_Icc.mpr
    have hb (j : Fin 3) :
        ⌊(c j + 1/2) / h⌋ - 3 ≤ w j ∧ w j ≤ ⌊(c j + 1/2) / h⌋ + 3 := by
      have hdj := (CellOrbital.dist_coord_le_torusDistance L
        (liftPoint L u) (liftPoint L c) j).trans hd
      change dist (u j : AddCircle L.val) (c j : AddCircle L.val) ≤ r at hdj
      rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hdj
      have hk : |(u j - (k j : ℝ) * L.val) - c j| ≤ r := by
        convert hdj using 1
        dsimp [k]
        ring_nf
      apply interval_ball_witness hh hr (u := u j - (k j : ℝ) * L.val)
      · have hl := hu.1 j
        change h * (z j : ℝ) - 1/2 ≤ u j at hl
        dsimp [w]
        push_cast
        rw [hperiod]
        nlinarith
      · have hl := hu.2 j
        change u j ≤ h * ((z j : ℝ)+1) - 1/2 at hl
        dsimp [w]
        push_cast
        rw [hperiod]
        nlinarith
      · exact hk
    exact ⟨fun j ↦ (hb j).1, fun j ↦ (hb j).2⟩
  · ext j
    simp [torusProjection, w]

theorem ncard_ball_bad_sites_le {L : Length} {J : ℕ} {h r : ℝ} (hh : 0 < h)
    (hperiod : L.val = h * J) (hr : r ≤ 2*h) (y : Torus L) :
    (torusProjection J '' {z | ∃ x ∈ microCube L h z,
      torusDistance L x y ≤ r}).ncard ≤ 343 := by
  let c : Point := fun j ↦ (AddCircle.equivIco L.val 0 (y j)).val
  have hc : liftPoint L c = y := by ext j; exact AddCircle.coe_equivIco
  have hsub : torusProjection J '' {z | ∃ x ∈ microCube L h z,
      torusDistance L x y ≤ r} ⊆ ↑((witnessBox h c).image (torusProjection J)) := by
    rintro v ⟨z, ⟨x, hx, hd⟩, rfl⟩
    obtain ⟨w, hw, he⟩ := ball_microCube_witness hh hperiod hr c hx (by simpa [hc] using hd)
    exact Finset.mem_image.mpr ⟨w, hw, he⟩
  calc
    _ ≤ (↑((witnessBox h c).image (torusProjection J)) : Set (DiscreteTorus J)).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((witnessBox h c).image (torusProjection J)).card := Set.ncard_coe_finset _
    _ ≤ (witnessBox h c).card := Finset.card_image_le
    _ = 343 := card_witnessBox h c

end HardSphere.BathSlice

end

end OAI
