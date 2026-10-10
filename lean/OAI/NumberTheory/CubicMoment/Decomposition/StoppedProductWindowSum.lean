import OAI.NumberTheory.CubicMoment.Estimates.SharpHeightPartition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Exact infinite summation of the smooth height windows. The full
complement is obtained by dominated convergence, without a frequency cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace CubicFirstMoment

theorem height_window_complement_bound (F : ℝ → ℂ) (hF : Integrable F)
    {S K : ℝ} (hS : 0 < S) (hK : 0 ≤ K)
    (hwindow : ∀ n : ℕ,
      ‖∫ t : ℝ, heightWindow (S*(3/2:ℝ)^n) t*F t‖ ≤ K/(S*(3/2:ℝ)^n)) :
    ‖∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*F t‖ ≤ 3*K/S := by
  let G := fun (n : ℕ) (t : ℝ) =>
    ((heightPartitionBump (t/(S*(3/2:ℝ)^n))-
      heightPartitionBump (t/S):ℝ):ℂ)*F t
  have hfactor (n : ℕ) (t : ℝ) :
      ‖((heightPartitionBump (t/(S*(3/2:ℝ)^n))-
        heightPartitionBump (t/S):ℝ):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith [heightPartitionBump.nonneg (x := t/(S*(3/2:ℝ)^n)),
      heightPartitionBump.le_one (x := t/(S*(3/2:ℝ)^n)),
      heightPartitionBump.nonneg (x := t/S),heightPartitionBump.le_one (x := t/S)]
  have hconv : Tendsto (fun n => ∫ t : ℝ, G n t) atTop
      (𝓝 (∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*F t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => ‖F t‖)
    · intro n
      exact ((Complex.continuous_ofReal.comp
        ((heightPartitionBump.continuous.comp (continuous_id.div_const _)).sub
          (heightPartitionBump.continuous.comp (continuous_id.div_const _)))).aestronglyMeasurable).mul
        hF.aestronglyMeasurable
    · exact hF.norm
    · intro n
      filter_upwards with t
      exact (norm_mul _ _).le.trans (mul_le_of_le_one_left (_root_.norm_nonneg _) (hfactor n t))
    · filter_upwards with t
      have hp : Tendsto (fun n : ℕ => S*(3/2:ℝ)^n) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hS (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
      apply tendsto_const_nhds.congr'
      filter_upwards [hp.eventually (eventually_ge_atTop |t|)] with n hn
      have hd : 0 < S*(3/2:ℝ)^n := by positivity
      have hb : heightPartitionBump (t/(S*(3/2:ℝ)^n)) = 1 := by
        apply heightPartitionBump_one
        rw [abs_div,abs_of_pos hd]
        exact (div_le_one hd).mpr hn
      simp only [G,hb,Complex.ofReal_sub,Complex.ofReal_one]
  have hpartial (n : ℕ) : ‖∫ t : ℝ, G n t‖ ≤ 3*K/S := by
    have hi (j : ℕ) : Integrable (fun t => heightWindow (S*(3/2:ℝ)^j) t*F t) := by
      apply hF.bdd_mul
      · exact (heightWindow_smooth _).continuous.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (heightWindow_norm_le _)
    have he : (∫ t : ℝ, G n t) =
        ∑ j ∈ Finset.range n, ∫ t : ℝ, heightWindow (S*(3/2:ℝ)^j) t*F t := by
      rw [←integral_finsetSum _ (fun j _ => hi j)]
      apply integral_congr_ae
      filter_upwards with t
      rw [←Finset.sum_mul,heightWindow_telescope]
    rw [he]
    apply (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hwindow j)).trans ?_)
    have hgeom : (∑ j ∈ Finset.range n, (2/3:ℝ)^j) ≤ 3 := by
      have hg := geom_sum_mul_neg (2/3:ℝ) n
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2/3) n]
    calc
      _ = (K/S)*(∑ j ∈ Finset.range n, (2/3:ℝ)^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_eq_mul_inv (K) (S*(3/2:ℝ)^j),mul_inv_rev,←inv_pow]
        norm_num
        ring
      _ ≤ (K/S)*3 := mul_le_mul_of_nonneg_left hgeom (div_nonneg hK hS.le)
      _ = _ := by ring
  exact le_of_tendsto hconv.norm (Filter.Eventually.of_forall hpartial)

end CubicFirstMoment

end

end OAI
