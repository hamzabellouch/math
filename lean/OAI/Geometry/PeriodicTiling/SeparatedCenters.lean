import OAI.Geometry.PeriodicTiling.EuclideanBasic
import OAI.Geometry.PeriodicTiling.ClosedBoxRounding
import OAI.Geometry.PeriodicTiling.VoxelMeasure
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Set MeasureTheory
open scoped Classical

def RigidDifferences (m : ℕ) (S : Finset (Lattice 3)) : Prop :=
  ∀ d : Lattice 3, (∀ i, |d i| ≤ (m : ℤ)) → (∃ i, ¬ (m : ℤ) ∣ d i) →
    ∃ t ∈ S, ∃ t' ∈ S, t - t' = d

theorem TypedAETiles.aedisjoint {d : ℕ} {Ω0 Ω1 C C1 : Set (Space d)}
    (h : TypedAETiles Ω0 Ω1 C C1) {c c' : C} (hne : c ≠ c') :
    AEDisjoint volume
      {x | x - (c : Space d) ∈ if (c : Space d) ∈ C1 then Ω1 else Ω0}
      {x | x - (c' : Space d) ∈ if (c' : Space d) ∈ C1 then Ω1 else Ω0} := by
  apply measure_mono_null ?_ (ae_iff.mp h)
  rintro x ⟨hx, hx'⟩ ⟨a, _ha, huniq⟩
  exact hne ((huniq c hx).trans (huniq c' hx').symm)

theorem AETiles.aedisjoint {d : ℕ} {Ω A : Set (Space d)}
    (h : AETiles Ω A) {a a' : A} (hne : a ≠ a') :
    AEDisjoint volume {x | x - (a : Space d) ∈ Ω}
      {x | x - (a' : Space d) ∈ Ω} := by
  apply measure_mono_null ?_ (ae_iff.mp h)
  rintro x ⟨hx, hx'⟩ ⟨c, _hc, huniq⟩
  exact hne ((huniq a hx).trans (huniq a' hx').symm)

theorem common_unitVoxel_subset_piece {d : ℕ}
    {S0 S1 S : Finset (Lattice d)} (h0 : S ⊆ S0) (h1 : S ⊆ S1)
    (C1 : Set (Space d)) (c : Space d) {t : Lattice d} (ht : t ∈ S) :
    unitVoxel (c + castLattice t) ⊆
      {x | x - c ∈ if c ∈ C1 then Thickening S1 else Thickening S0} := by
  intro x hx
  have hcube : (x - c) - castLattice t ∈ unitCube d := by
    simpa only [mem_unitVoxel, sub_add_eq_sub_sub] using hx
  by_cases hc : c ∈ C1
  · simp only [hc, ite_eq_left, mem_ofPred_eq]
    exact ⟨t, h1 ht, hcube⟩
  · simp only [hc, mem_ofPred_eq]
    exact ⟨t, h0 ht, hcube⟩

theorem typed_nearby_centers_mem_scaledGrid
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    {C C1 : Set (Space 3)} (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1)
    {c c' : C} (hne : c ≠ c') (hclose : ‖(c' : Space 3) - (c : Space 3)‖ ≤ (m : ℝ)) :
    (c' : Space 3) - (c : Space 3) ∈ scaledGrid m := by
  by_contra hnot
  have hcoords : ∀ i, |((c' : Space 3) - (c : Space 3)) i| ≤ (m : ℝ) := by
    intro i
    have hcoord : |((c' : Space 3) - (c : Space 3)) i| ≤
        ‖(c' : Space 3) - (c : Space 3)‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm ((c' : Space 3) - (c : Space 3)) i
    exact hcoord.trans hclose
  obtain ⟨d, hd, hdiv, hround⟩ :=
    closed_box_rounding m hm ((c' : Space 3) - (c : Space 3)) hcoords hnot
  obtain ⟨t, ht, t', ht', htd⟩ := hdiff d hd hdiv
  have hcorners : ∀ i,
      |((c' : Space 3) + castLattice t') i - ((c : Space 3) + castLattice t) i| < 1 := by
    intro i
    have hid : ((c' : Space 3) + castLattice t') i -
        ((c : Space 3) + castLattice t) i =
        (((c' : Space 3) - (c : Space 3)) i - (d i : ℝ)) := by
      rw [← htd]
      simp only [Pi.add_apply, Pi.sub_apply, castLattice_apply, Int.cast_sub]
      ring
    rw [hid]
    exact hround i
  have hpos := unitVoxel_inter_volume_pos
    ((c : Space 3) + castLattice t) ((c' : Space 3) + castLattice t') hcorners
  have hnull := (htile.aedisjoint hne).mono
    (common_unitVoxel_subset_piece h0 h1 C1 c ht)
    (common_unitVoxel_subset_piece h0 h1 C1 c' ht')
  exact (ne_of_gt hpos) hnull

theorem scaledGrid_eq_zero_of_norm_lt {m : ℕ} (hm : 0 < m)
    {x : Space 3} (hx : x ∈ scaledGrid m) (hnorm : ‖x‖ < (m : ℝ)) : x = 0 := by
  obtain ⟨z, rfl⟩ := mem_scaledGrid.mp hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : z = 0 := by
    funext i
    have hi : |(m : ℝ) * (z i : ℝ)| < (m : ℝ) := by
      have hle := norm_le_pi_norm ((m : ℝ) • castLattice z) i
      have hle' : |(m : ℝ) * (z i : ℝ)| ≤ ‖(m : ℝ) • castLattice z‖ := by
        simpa only [Pi.smul_apply, smul_eq_mul, castLattice_apply,
          Real.norm_eq_abs] using hle
      exact hle'.trans_lt hnorm
    rw [abs_mul, abs_of_nonneg hmR.le] at hi
    have hzi : |(z i : ℝ)| < 1 := by
      exact (mul_lt_mul_iff_right₀ hmR).mp (by simpa only [mul_one] using hi)
    rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at hzi
    exact Int.abs_lt_one_iff.mp hzi
  simp [hz]

theorem typed_centers_separated
    {m : ℕ} (hm : 2 ≤ m) {S0 S1 S : Finset (Lattice 3)}
    (h0 : S ⊆ S0) (h1 : S ⊆ S1) (hdiff : RigidDifferences m S)
    {C C1 : Set (Space 3)} (htile : TypedAETiles (Thickening S0) (Thickening S1) C C1)
    {c c' : C} (hne : c ≠ c') : (m : ℝ) ≤ ‖(c' : Space 3) - (c : Space 3)‖ := by
  by_contra h
  have hsmall := lt_of_not_ge h
  have hgrid := typed_nearby_centers_mem_scaledGrid hm h0 h1 hdiff htile hne hsmall.le
  have hzero := scaledGrid_eq_zero_of_norm_lt
    (lt_of_lt_of_le (by decide : 0 < 2) hm) hgrid hsmall
  exact hne (Subtype.ext (sub_eq_zero.mp hzero).symm)

end PeriodicTilingThree

end

end OAI
