import OAI.Geometry.NodalSets.Elliptic.RescaledCoordinates
import OAI.Geometry.NodalSets.Waves.GaussianTailBound

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section

lemma rescaling_displacement_bound {N s R : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s)
    {x v : Coord} (hv : ‖v‖ ≤ R) :
    N*‖(x+(N*s)⁻¹ • v)-x‖ ≤ R := by
  obtain ⟨hr0,_,hNr⟩ := rescaling_radius_bound hN hs
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
  calc
    _ = (N*(N*s)⁻¹)*‖v‖ := by ring
    _ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right hNr (norm_nonneg _)
    _ ≤ R := by simpa using hv

lemma shifted_center_distance {x y z : Coord} {r : ℝ}
    (hfar : r < sourceEuclideanNorm (x-y)) (hshift : ‖z-x‖ ≤ r/4) :
    r/4 < sourceEuclideanNorm (z-y) := by
  have ht : ‖x-y‖ ≤ ‖z-x‖+‖z-y‖ := by
    calc
      _ = ‖(x-z)+(z-y)‖ := by congr 1; abel
      _ ≤ ‖x-z‖+‖z-y‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev x z]
  have he := sourceEuclideanNorm_le (x-y)
  have hn := norm_le_sourceEuclideanNorm (z-y)
  linarith

lemma main_radius_times_frequency {N : ℝ} (hN : 0 < N) :
    N*N^(-5/12:ℝ) = N^(7/12:ℝ) := by
  calc
    _ = N^(1:ℝ)*N^(-5/12:ℝ) := by rw [Real.rpow_one]
    _ = N^((1:ℝ)+(-5/12)) := (Real.rpow_add hN _ _).symm
    _ = _ := by norm_num

theorem eventually_shifted_center_distance (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℝ), 1 ≤ s → ∀ (x y v : Coord), ‖v‖ ≤ R →
      (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-y) →
      (n:ℝ)^(-5/12:ℝ)/4 < sourceEuclideanNorm (x+((n:ℝ)*s)⁻¹ • v-y) := by
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)^(7/12:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7/12)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (4*R)),eventually_gt_atTop (0:ℕ)]
    with n hn hnpos
  intro s hs x y v hv hfar
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hd := rescaling_displacement_bound (x := x) hn1 hs hv
  rw [← main_radius_times_frequency hn0] at hn
  apply shifted_center_distance hfar
  nlinarith

end
end Yau.Geometry

end OAI
