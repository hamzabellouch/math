import OAI.NumberTheory.TotientAsymptotic.CoordinateCenters
import OAI.NumberTheory.TotientAsymptotic.EnlargementTail

namespace OAI

/-! Away from the terminal coordinates, the diagonal enlargement is uniformly
close to one. At fixed truncation the additive budget correction vanishes. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def coordinateEnlargement (M N : ℕ) : Fin N → ℝ :=
  enlargementScale (fun r => 1+simplexBoxError 0 (M-r))

lemma coordinateEnlargement_one_le (M N : ℕ) (i : Fin N) :
    1 ≤ coordinateEnlargement M N i := by
  have hb (r : ℕ) : 1 ≤ 1+simplexBoxError 0 (M-r) :=
    le_add_of_nonneg_right (simplexBoxError_nonneg (by norm_num) _)
  exact (hb 0).trans (enlargementScale_top hb i)

theorem coordinateEnlargement_close : ∀ᶠ P : ℕ in atTop,
    ∀ (M N : ℕ) (i : Fin N),P ≤ M-(i.val+1) →
      coordinateEnlargement M N i ≤ (1001/1000:ℝ) := by
  have ht : Tendsto (fun P => Real.exp (simplexBoxTail 0 P)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp (simplexBoxTail_tendsto 0)
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (1:ℝ) < 1001/1000)),
    eventually_ge_atTop (1:ℕ)] with P hP hP1
  intro M N i hi
  apply le_trans _ hP
  rw [simplexBoxTail_eq_tsum]
  exact reverse_enlargement_coordinate (by omega : P ≤ M) (simplexBoxError 0)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 0) i
    (by omega)

theorem fixed_coordinate_budget_small (H : ℕ) : ∀ᶠ x : ℝ in atTop,
    0 ≤ prefixCubeCost (m x-H)/B x ∧
    prefixCubeCost (m x-H)/B x ≤ (1/1000:ℝ) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  have ht : Tendsto (fun x : ℝ => m x-H) atTop atTop :=
    (tendsto_sub_atTop_nat H).comp m_tendsto
  filter_upwards [hcost,B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    (tendsto_natCast_atTop_atTop.comp ht).eventually (eventually_ge_atTop (1000*A)),
    ht.eventually (eventually_ge_atTop 1)] with x hx hB hN hN1
  have hn : (0:ℝ) < ((m x-H:ℕ):ℝ) := by exact_mod_cast (show 0 < m x-H by omega)
  have hnn : 0 ≤ prefixCubeCost (m x-H)/B x :=
    div_nonneg (prefixCubeCost_nonneg _) hB.le
  refine ⟨hnn,?_⟩
  have hh := (hx (m x-H) (Nat.sub_le _ _)).trans
    (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hquot : prefixCubeCost (m x-H)/B x ≤ A/((m x-H:ℕ):ℝ) := by
    apply (le_div_iff₀ hn).mpr
    convert hh using 1; ring
  apply hquot.trans
  apply (div_le_iff₀ hn).mpr
  dsimp only [Function.comp_def] at hN
  linarith only [hN]

end TotientAsymptotic

end

end OAI
