import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationTaskSpace
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordWidthBounds

namespace OAI

/-! # Full mutable reader snapshots fit the replay buffer

Immutable leaf arrays are shared. A snapshot copies the tournament, its
cached occurrences and cursor fields. This bound holds for every reader
state, prefix and residue, independently of the resource event.
-/

noncomputable section

namespace LowSpaceSubsetSum

theorem guarded_power_rate {n : ℕ} {u : ℝ} (hu : 0 < u)
    (hlog : Real.logb 2 u ≤ (n : ℝ) / 1000000000) (k : ℕ) :
    u ^ k ≤ (2 : ℝ) ^ (((k : ℝ) / 1000000000) * n) := by
  have hp : u ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 u) := by
    have hh := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (Real.logb 2 u) k
    rw [Real.rpow_logb (by norm_num) (by norm_num) hu] at hh
    simpa only [mul_comm] using hh.symm
  rw [hp]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k (α := ℝ))
  nlinarith only [hm]

theorem representationBufferCapacity_lower (n : ℕ) :
    (2 : ℝ) ^ ((19 / 100 : ℝ) * n - 1) ≤ representationBufferCapacity n := by
  have hfloor : 19 * n < 100 * (19 * n / 100 + 1) := by omega
  have hfloorR : (19 : ℝ) * n < 100 * ((19 * n / 100 : ℕ) + 1 : ℝ) := by
    exact_mod_cast hfloor
  have he : (19 / 100 : ℝ) * n - 1 ≤ (19 * n / 100 : ℕ) := by linarith
  simpa only [representationBufferCapacity, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

def snapshotCells (s : D.State) : ℕ := (12 * n + 32) * (Tournament.nodes s.tree + 1)

end RepresentationPairData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem schedule_snapshotCells_le_buffer (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) (child : Fin 2) :
    let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
    ∀ s : D.State, D.snapshotCells s ≤ representationBufferCapacity n := by
  dsimp only
  let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
  intro s
  let u := inputScale R.input
  let A := (2 : ℝ) ^ ((37 / 200 : ℝ) * n)
  have hnu : n ≤ u := by unfold u inputScale; omega
  have huN : 10000 ≤ u := hn.trans hnu
  have hu : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hs := R.schedule_pair_storage h r hn hlog hscale q hq z side P child
  have ht : (Tournament.nodes s.tree : ℝ) + 1 ≤ 4 * ((D.leftArray.size : ℝ) + 1) := by
    exact_mod_cast Tournament.padded_nodes_le D.leftArray.size s.tree
  have hA : 1 ≤ A := Real.one_le_rpow (by norm_num) (by positivity)
  have hnodes : (Tournament.nodes s.tree : ℝ) + 1 ≤ 8 * A := by
    have hsL : (D.leftArray.size : ℝ) ≤ A := hs.1
    linarith only [ht, hsL, hA]
  have hcoef : (12 * n + 32 : ℕ) ≤ 44 * u := by omega
  have hsmall : (D.snapshotCells s : ℝ) ≤ (352 * (u : ℝ)) * A := by
    have hc : ((12 * n + 32 : ℕ) : ℝ) ≤ 44 * (u : ℝ) := by exact_mod_cast hcoef
    have hm := mul_le_mul hc hnodes (by positivity) (by positivity)
    simp only [RepresentationPairData.snapshotCells, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat] at hm ⊢
    nlinarith only [hm]
  have huR : (10000 : ℝ) ≤ u := by exact_mod_cast huN
  have hcoef3 : 352 * (u : ℝ) ≤ (u : ℝ) ^ 3 := by
    have hsq : (352 : ℝ) ≤ (u : ℝ) ^ 2 := by nlinarith only [huR]
    calc
      _ ≤ (u : ℝ) ^ 2 * u := mul_le_mul_of_nonneg_right hsq hu.le
      _ = _ := by ring
  have hp := guarded_power_rate hu hscale 3
  have hfull : (D.snapshotCells s : ℝ) ≤
      (2 : ℝ) ^ (((3 / 1000000000 : ℝ) + 37 / 200) * n) := by
    calc
      _ ≤ (u : ℝ) ^ 3 * A := hsmall.trans (mul_le_mul_of_nonneg_right hcoef3 (by positivity))
      _ ≤ (2 : ℝ) ^ ((3 / 1000000000 : ℝ) * n) * A :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by unfold A; rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have he : ((3 / 1000000000 : ℝ) + 37 / 200) * n ≤ (19 / 100 : ℝ) * n - 1 := by linarith
  exact_mod_cast hfull.trans ((Real.rpow_le_rpow_of_exponent_le (by norm_num) he).trans
    (representationBufferCapacity_lower n))

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
