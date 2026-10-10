import OAI.NumberTheory.TotientAsymptotic.FixedCoordinateCenters
import OAI.NumberTheory.TotientAsymptotic.CoordinateBoxError
import OAI.NumberTheory.TotientAsymptotic.CoordinateGridConcentration
import OAI.NumberTheory.TotientAsymptotic.CoordinateGridPrefactor
import OAI.NumberTheory.TotientAsymptotic.FordUnbandedMass

namespace OAI

/-! Concentration for the actual enlarged prime-prefix grid, at a fixed
terminal truncation and the fixed tolerance used by the application. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem fixed_coordinate_grid_bound (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ K : Finset (Fin (N+2) → ℕ),
    (∀ b∈K,∃ u∈unitGridCell b,
      u∈enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (u i < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < u i)) →
    (K.card:ℝ) ≤ C*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨C,c,hC,hc,hconc⟩ := coordinate_grid_concentration
  obtain ⟨A,hA,hpref⟩ := fixed_coordinate_grid_prefactor
  refine ⟨C*A,c,mul_pos hC hA,hc,?_⟩
  filter_upwards [fixed_coordinate_centers_close H,coordinateEnlargement_close,
    coordinate_box_error_small (show (0:ℝ) < 2 by norm_num),
    eventually_ge_atTop (H+3)] with P hcent hclose herr hP
  filter_upwards [hcent,herr,hpref,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hcent herr hpref hB
  intro N hN i hi K hK
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m x-r)
  let κ := coordinateEnlargement (m x) (N+2)
  have hβ (r : ℕ) : 1 ≤ β r :=
    le_add_of_nonneg_right (simplexBoxError_nonneg (by norm_num) _)
  have hκ (j : Fin (N+2)) : 1 ≤ κ j := coordinateEnlargement_one_le _ _ _
  have hκ2 : κ i ≤ 2 := (hclose _ _ i hi).trans (by norm_num)
  have him : i.val+1 < m x := by have := i.isLt; omega
  have hiN : i.val < N := by have := i.isLt; omega
  have hS : 0 < fordBandScale x (i.val+1) := fordBandScale_pos hB him
  have hcent' := hcent N hN i hi
  have herr' := herr (N+2) i (by omega) hi (κ i) (zero_le_one.trans (hκ i)) hκ2
  have hgrid := hconc N (B x) (β 0) (fordBandScale x (i.val+1))
    (fun j => β (j.val+1)) κ i hiN hB (zero_lt_one.trans_le (hβ 0)) hS
    (fun j => zero_lt_one.trans_le (hβ _)) hκ (enlargementScale_top hβ)
    (enlargementScale_step hβ) hcent'.1 hcent'.2 herr' K (by
      intro b hb
      obtain ⟨u,hu,hs,hbad⟩ := hK b hb
      refine ⟨u,hu,?_,hbad⟩
      simpa only [β,xi_eq_simplexBoxError,Nat.sub_zero] using hs)
  have hvolume := hpref (N+2) (by omega) (by omega)
  have hnon : 0 ≤ C*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hvolume hnon
  apply hgrid.trans
  convert hh using 1 <;> ring

end TotientAsymptotic

end

end OAI
