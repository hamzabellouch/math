import Mathlib
import OAI.Probability.SKGap.Localization.FixedTimeQuenched
import OAI.Probability.SKGap.Localization.OperatorQuenched
import OAI.Probability.SKGap.Localization.GridSteps
import OAI.Probability.SKGap.Localization.QuenchedHelpers

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set ObservationBridge GaussianHistory
open scoped Topology BigOperators ENNReal
noncomputable section

def gridFailure (n : ℕ) (j A K ε c ρ T : ℝ) (g : Disorder n) : ℝ :=
  ∑k∈Finset.range (gridSteps n+1),fixedTimeFailure n j A K ε c ρ ((k:ℝ)*gridStep T n) g

lemma gridFailure_nonneg (n : ℕ) (j A K ε c ρ T : ℝ) (g : Disorder n) :
    0≤gridFailure n j A K ε c ρ T g :=
  Finset.sum_nonneg (fun step _=>fixedTimeFailure_nonneg n j A K ε c ρ ((step:ℝ)*gridStep T n) g)

lemma weighted_gridFailure_integrable (β : ℝ) (n : ℕ) (A K ε c ρ T : ℝ) :
    Integrable (fun g=>partitionSizeBias β n g*gridFailure n (β^2) A K ε c ρ T g) (disorderLaw β n) := by
  simp only [gridFailure,Finset.mul_sum]
  exact integrable_finsetSum _ (fun k _=>weighted_fixedTimeFailure_integrable _ _ _ _ _ _ _ _ _)

lemma grid_time_mem {T : ℝ} (hT : 0≤T) {n k : ℕ} (hk : k≤gridSteps n) :
    (k:ℝ)*gridStep T n∈Icc 0 T := by
  have ht:=gridStep_nonneg hT n
  refine ⟨mul_nonneg (Nat.cast_nonneg _) ht,?_⟩
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ht).trans_eq (grid_total T n)

theorem quenched_grid_root_stability {β T : ℝ} (hβ : 0<β) (hβ1 : β<1) (hT : 0<T) :
    ∃A K ε c ρ a : ℝ,1<A ∧ 2*β<K ∧ β*A<1 ∧ 0<ε ∧ 0<c ∧ 0<ρ ∧ 0<a ∧
      Whp β (fun n g=>operatorBound K (coupling g) ∧
        gridFailure n (β^2) A K ε c ρ T g≤exp (-a*(n:ℝ))) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hs,hε,hc,hρ,ha,N,hN,hann⟩:=
    annealed_fixed_time_root_stability hβ hβ1 hT
  have hsum : ∀ᶠ n:ℕ in atTop,
      (∫g,partitionSizeBias β n g*gridFailure n (β^2) A K ε c ρ T g ∂disorderLaw β n)≤
        exp (-(a/2)*(n:ℝ)) := by
    filter_upwards [eventually_ge_atTop N,grid_exp_absorb ha] with n hn he
    simp only [gridFailure,Finset.mul_sum]
    rw [integral_finsetSum _ (fun k _=>weighted_fixedTimeFailure_integrable _ _ _ _ _ _ _ _ _)]
    have he' : (∑_k∈Finset.range (gridSteps n+1),exp (-a*(n:ℝ)))≤exp (-(a/2)*(n:ℝ)) := by
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using he
    apply le_trans (Finset.sum_le_sum (fun k hk=>?_)) he'
    have hk' : k≤gridSteps n:=by have:=Finset.mem_range.mp hk;omega
    exact weighted_fixedTimeFailure_integral_bound β n A K ε c ρ ((k:ℝ)*gridStep T n) _
      (exp_pos _).le (hann n hn _ (grid_time_mem hT.le hk'))
  have hp : Whp β (fun n g=>gridFailure n (β^2) A K ε c ρ T g≤exp (-((a/2)/4)*(n:ℝ))) := by
    apply (whp_iff_real _ _).mpr
    simp only [not_le]
    apply exponential_size_bias_transfer (C:=1) (disorderLaw β) (partitionSizeBias β)
      (fun n=>gridFailure n (β^2) A K ε c ρ T)
      (fun n g=>(partitionSizeBias_pos β n g).le)
      (fun n g=>gridFailure_nonneg _ _ _ _ _ _ _ _ _) (fun n=>weighted_gridFailure_integrable _ _ _ _ _ _ _ _)
      (half_pos ha) zero_le_one
    · exact disorder_partition_lower_tail hβ hβ1 (by positivity)
    · simpa only [one_mul] using hsum
  have hop : Whp β (fun n g=>operatorBound K (coupling g)):=
    (whp_iff_real _ _).mpr (quenched_operator_bound hβ hK)
  exact ⟨A,K,ε,c,ρ,(a/2)/4,hA,hK,hs,hε,hc,hρ,by positivity,hop.and hp⟩

end
end SKGap.FullMain

end OAI
