import OAI.Probability.ContinuumTransition.MaskedReference

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem volume_real_gridBox {u : ℝ} (hu : 0 ≤ u) (k : Lattice) :
    volume.real (gridBox u k) = u^3 := by
  rw [measureReal_def, volume_gridBox hu, ENNReal.toReal_ofReal (pow_nonneg hu 3)]

theorem gridBox_union_volume {u : ℝ} (hu : 0 < u) (s : Finset Lattice) :
    volume.real (⋃ k ∈ s, gridBox u k) = s.card*u^3 := by
  rw [measureReal_biUnion_finset (fun _ _ _ _ hkl => gridBox_disjoint hu hkl)
    (fun _ _ => measurableSet_gridBox _ _) (fun k _ => by
      rw [volume_gridBox hu.le]; exact ENNReal.ofReal_ne_top)]
  simp only [volume_real_gridBox hu.le, Finset.sum_const, nsmul_eq_mul]

theorem norm_le_cube {x : Space} {D : ℝ} (h : ‖x‖ ≤ D) : x ∈ cube (2*D) := by
  intro i
  have hc : |x i| ≤ D := (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i :
    |x i| ≤ ‖x‖).trans h
  rw [abs_le] at hc
  dsimp only [mem_Icc]
  constructor <;> linarith [hc.1, hc.2]

theorem card_grid_near_bound {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D) (c : Space)
    (s : Finset Lattice) (hs : ∀ k ∈ s, ‖gridCenter u k-c‖ ≤ D) :
    (s.card : ℝ)*u^3 ≤ (2*(D+2*u))^3 := by
  have hsub : (⋃ k ∈ s, gridBox u k) ⊆ (fun x : Space => x-c) ⁻¹' cube (2*(D+2*u)) := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp hx
    apply norm_le_cube
    calc
      ‖x-c‖ ≤ ‖x-gridCenter u k‖+‖gridCenter u k-c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2*u+D := add_le_add (gridBox_center_distance hu hx) (hs k hk)
      _ = D+2*u := add_comm _ _
  have hm : volume ((fun x : Space => x-c) ⁻¹' cube (2*(D+2*u))) =
      ENNReal.ofReal ((2*(D+2*u))^3) := by
    rw [show (fun x : Space => x-c) = (fun x => x+(-c)) by funext; rw [sub_eq_add_neg],
      measure_preimage_add_right, volume_cube, ENNReal.ofReal_pow (by positivity)]
  have hh := measureReal_mono hsub (by rw [hm]; exact ENNReal.ofReal_ne_top)
  rw [gridBox_union_volume hu, measureReal_def, hm,
    ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

end ContinuumTemperature
end

end OAI
