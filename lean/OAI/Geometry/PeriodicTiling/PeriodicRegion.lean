import OAI.Geometry.PeriodicTiling.TilesRegion
import OAI.Geometry.PeriodicTiling.FiniteCylinder
import OAI.Geometry.PeriodicTiling.PlaneLattices
import Mathlib.Tactic.NormNum

namespace OAI

namespace PeriodicTilingThree

namespace PeriodicRegion

def residue (m : ℕ) (hm : 0 < m) (x : ℤ) : Fin m :=
  ⟨(x % (m : ℤ)).toNat, by
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
    have hlo := Int.emod_nonneg x (ne_of_gt hmZ)
    have hhi := Int.emod_lt_of_pos x hmZ
    omega⟩

theorem residue_cast (m : ℕ) (hm : 0 < m) (x : ℤ) :
    ((residue m hm x : ℕ) : ℤ) = x % (m : ℤ) := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hlo := Int.emod_nonneg x (ne_of_gt hmZ)
  dsimp [residue]
  omega

theorem residue_add (m : ℕ) (hm : 0 < m) (x : ℤ) :
    residue m hm (x + m) = residue m hm x := by
  apply Fin.ext
  simp [residue]

private theorem coordinate_sub (T : Plane ≃+ Plane) (x y : ℤ) (f : Plane) :
    T (x, y) - f = T (x - (T.symm f).1, y - (T.symm f).2) := by
  calc
    T (x, y) - f = T (x, y) - T (T.symm f) := by rw [T.apply_symm_apply]
    _ = T ((x, y) - T.symm f) := (map_sub T (x, y) (T.symm f)).symm
    _ = T (x - (T.symm f).1, y - (T.symm f).2) := rfl

private theorem target_phase {E : Set Plane} (T : Plane ≃+ Plane) (q : ℕ)
    (hE : Period E (T (0, (q : ℤ)))) (x y y' : ℤ)
    (hphase : (q : ℤ) ∣ y' - y) :
    T (x, y') ∈ E ↔ T (x, y) ∈ E := by
  obtain ⟨c, hc⟩ := hphase
  have hv := hE.zsmul c
  have heq : T (x, y) + c • T (0, (q : ℤ)) = T (x, y') := by
    rw [← map_zsmul, ← map_add]
    congr 1
    apply Prod.ext
    · simp
    · simp
      nlinarith
  simpa only [heq] using hv (T (x, y))

end PeriodicRegion

theorem periodic_region_replacement {F : Finset Plane} {D E : Set Plane}
    (htile : TilesRegion F D E)
    (hperiod : ∃ h : Plane, h ≠ 0 ∧ Period D h)
    (htarget : FullyPeriodic E) :
    ∃ D' : Set Plane, TilesRegion F D' E ∧ FullyPeriodic D' := by
  classical
  obtain ⟨h, hh, hD⟩ := hperiod
  obtain ⟨m, hm, T, hT⟩ := exists_primitive_coordinates hh
  have hDcoord : Period D (T ((m : ℤ), 0)) := hT.symm ▸ hD
  obtain ⟨q, hq, hEcoord⟩ := htarget.exists_coordinate_period T
  let row : ℤ → (Fin m → Bool) := fun n r => decide (T ((r : ℕ), n) ∈ D)
  have row_iff (x n : ℤ) :
      row n (PeriodicRegion.residue m hm x) = true ↔ T (x, n) ∈ D := by
    change decide (T (((PeriodicRegion.residue m hm x : ℕ) : ℤ), n) ∈ D) = true ↔
      T (x, n) ∈ D
    rw [decide_eq_true_eq, PeriodicRegion.residue_cast]
    exact (hDcoord.mem_coordinate_mod x n).symm
  let R : ℕ := F.sup (fun f => (T.symm f).2.natAbs)
  have offset_bounds (f : ↥F) :
      0 ≤ (R : ℤ) - (T.symm (f : Plane)).2 ∧
      (R : ℤ) - (T.symm (f : Plane)).2 ≤ (2 * R : ℕ) := by
    have habs : (T.symm (f : Plane)).2.natAbs ≤ R :=
      Finset.le_sup (f := fun f : Plane => (T.symm f).2.natAbs) f.property
    have habsZ : ((T.symm (f : Plane)).2.natAbs : ℤ) ≤ R := by
      exact_mod_cast habs
    have hupper : (T.symm (f : Plane)).2 ≤
        ((T.symm (f : Plane)).2.natAbs : ℤ) := Int.le_natAbs
    have hlower : -(T.symm (f : Plane)).2 ≤
        ((T.symm (f : Plane)).2.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using
        (Int.le_natAbs (a := -(T.symm (f : Plane)).2))
    have htwo : ((2 * R : ℕ) : ℤ) = 2 * (R : ℤ) := by simp
    rw [htwo]
    omega
  obtain ⟨b, L, hL, hqL, hbperiod, hwindows⟩ :=
    FiniteCylinder.exists_periodic_windows row q (2 * R) hq
  let D' : Set Plane := {z | b (T.symm z).2
    (PeriodicRegion.residue m hm (T.symm z).1) = true}
  have mem_new (x y : ℤ) :
      T (x, y) ∈ D' ↔ b y (PeriodicRegion.residue m hm x) = true := by
    simp only [D', Set.mem_ofPred_eq, T.symm_apply_apply]
  have htiles : TilesRegion F D' E := by
    apply htile.of_local_copy
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective z
    obtain ⟨t, htphase, hwindow⟩ := hwindows (y - R)
    refine ⟨T (x, t + R), ?_, ?_⟩
    · apply PeriodicRegion.target_phase T q hEcoord
      have heq : t + (R : ℤ) - y = t - (y - (R : ℤ)) := by omega
      simpa only [heq] using htphase
    · intro f
      obtain ⟨hk0, hkH⟩ := offset_bounds f
      have hrow := hwindow ((R : ℤ) - (T.symm (f : Plane)).2) hk0 hkH
      have hind : y - (R : ℤ) + ((R : ℤ) - (T.symm (f : Plane)).2) =
          y - (T.symm (f : Plane)).2 := by omega
      rw [hind] at hrow
      rw [PeriodicRegion.coordinate_sub T x y f,
        PeriodicRegion.coordinate_sub T x (t + R) f, mem_new, hrow]
      have heq : t + (R : ℤ) - (T.symm (f : Plane)).2 =
          t + ((R : ℤ) - (T.symm (f : Plane)).2) := by omega
      rw [heq]
      exact row_iff (x - (T.symm (f : Plane)).1)
        (t + ((R : ℤ) - (T.symm (f : Plane)).2))
  have hx : Period D' (T ((m : ℤ), 0)) := by
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective z
    have heq : T (x, y) + T ((m : ℤ), 0) = T (x + m, y) := by
      rw [← map_add]
      change T (x + (m : ℤ), y + 0) = T (x + (m : ℤ), y)
      rw [add_zero]
    rw [heq, mem_new, mem_new, PeriodicRegion.residue_add]
  have hy : Period D' (T (0, L)) := by
    intro z
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective z
    have heq : T (x, y) + T (0, L) = T (x, y + L) := by
      rw [← map_add]
      change T (x + 0, y + L) = T (x, y + L)
      rw [add_zero]
    rw [heq, mem_new, mem_new, hbperiod]
  have hLn : 0 < L.toNat := by omega
  have hLcast : (L.toNat : ℤ) = L := by omega
  refine ⟨D', htiles, fullyPeriodic_of_coordinate_periods T m L.toNat hm hLn hx ?_⟩
  simpa only [hLcast] using hy

end PeriodicTilingThree

end OAI
