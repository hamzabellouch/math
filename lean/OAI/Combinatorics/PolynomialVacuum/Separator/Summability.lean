import OAI.Combinatorics.PolynomialVacuum.Separator.CenteredPartition
import OAI.Combinatorics.PolynomialVacuum.Separator.Degree

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra Filter
open scoped Topology

noncomputable def positiveSystemWeight {n : ℕ} (S : System n) : ℝ :=
  2^S.val.card*PolynomialVacuumBridge.Corridor.criticalActivity^(∑P∈S.val,P.vertices.card)

theorem positiveSystemWeight_nonneg {n : ℕ} (S : System n) : 0≤positiveSystemWeight S := by
  exact mul_nonneg (by positivity) (pow_nonneg PolynomialVacuumBridge.Corridor.criticalActivity_pos.le _)

theorem systemWeight_two {n : ℕ} (S : System n) :
    systemWeight 2 S=(positiveSystemWeight S : ℂ) := by
  simp only [systemWeight,positiveSystemWeight,criticalActivity_xStar,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]

theorem finiteSeparatorSystems_tendsto (n : ℕ) [NeZero (2*n)] :
    Tendsto (fun H=>finiteSeparatorSystems n (centeredEdges (2*n) H)) atTop atTop := by
  apply tendsto_atTop.2
  intro u
  change ∀ᶠ H : ℕ in atTop,∀S∈u,S∈finiteSeparatorSystems n (centeredEdges (2*n) H)
  rw [Filter.eventually_all_finset]
  exact fun S _=>eventually_mem_finiteSeparatorSystems n S

 

theorem positiveSystemWeight_summable (n : ℕ) (hn : 1≤n) : Summable (positiveSystemWeight (n:=n)) := by
  have : NeZero (2*n):=⟨by omega⟩
  let L := ∑s : Fin (2*n-1+1) → Spin,
    AnalyticVacuum.normalizedVacuum (2*n-1+1) (fun _=>1) s*physicalCutDiagonal (2*n-1) n 1 s*
      AnalyticVacuum.normalizedVacuum (2*n-1+1) (fun _=>1) s
  have ht : Tendsto (fun H=>(finitePhysicalContraction (2*n-1) n H 1).re) atTop (nhds L.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp (finitePhysicalContraction_tendsto (2*n-1) n 1)
  have hb : ∀ᶠ H : ℕ in atTop,(finitePhysicalContraction (2*n-1) n H 1).re<L.re+1 :=
    ht.eventually (gt_mem_nhds (lt_add_one _))
  apply summable_of_sum_le positiveSystemWeight_nonneg (c:=L.re+1)
  intro u
  have hu : ∀ᶠ H : ℕ in atTop,u⊆finiteSeparatorSystems n (centeredEdges (2*n) H) :=
    (tendsto_atTop.1 (finiteSeparatorSystems_tendsto n)) u
  obtain ⟨H,hH,hbound⟩:=(hu.and hb).exists
  have hm := Finset.sum_le_sum_of_subset_of_nonneg hH (fun S _ _=>positiveSystemWeight_nonneg S)
  have hsum : (∑S∈finiteSeparatorSystems n (centeredEdges (2*n) H),positiveSystemWeight S)=
      (finitePhysicalContraction (2*n-1) n H 1).re := by
    rw [centered_partition_identity n hn H 1 one_ne_zero]
    simp only [inv_one,one_add_one_eq_two,systemWeight_two,Complex.re_sum,Complex.ofReal_re]
  exact hm.trans (hsum.trans_le hbound.le)

theorem systemWeight_norm_bound (n : ℕ) (η : ℂ) (S : System n) :
    ‖systemWeight η S‖≤(max 1 ‖η‖)^n*positiveSystemWeight S := by
  have hcard:=separated_system_card_le n S
  have ha : 1 ≤ max 1 ‖η‖:=le_max_left _ _
  have hp : ‖η‖^S.val.card≤(max 1 ‖η‖)^n :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans (pow_le_pow_right₀ ha hcard)
  have htwo : 1≤(2 : ℝ)^S.val.card:=one_le_pow₀ (by norm_num)
  have hpp : ‖η‖^S.val.card≤(max 1 ‖η‖)^n*2^S.val.card :=
    hp.trans (le_mul_of_one_le_right (pow_nonneg (le_trans zero_le_one ha) _) htwo)
  rw [systemWeight,norm_mul,norm_pow,norm_pow,norm_xStar]
  calc
    _ ≤ ((max 1 ‖η‖)^n*2^S.val.card)*PolynomialVacuumBridge.Corridor.criticalActivity^(∑P∈S.val,P.vertices.card) :=
      mul_le_mul_of_nonneg_right hpp (pow_nonneg PolynomialVacuumBridge.Corridor.criticalActivity_pos.le _)
    _ = _ := by simp only [positiveSystemWeight,mul_assoc]

theorem separator_systems_summable (n : ℕ) (hn : 1≤n) (η : ℂ) : Summable (systemWeight (n:=n) η) :=
  ((positiveSystemWeight_summable n hn).mul_left ((max 1 ‖η‖)^n)).of_norm_bounded
    (systemWeight_norm_bound n η)

theorem finite_separator_sums_tendsto (n : ℕ) [NeZero (2*n)] (hn : 1≤n) (η : ℂ) :
    Tendsto (fun H=>∑S∈finiteSeparatorSystems n (centeredEdges (2*n) H),systemWeight η S)
      atTop (nhds (separatorPolynomial n η)) :=
  (separator_systems_summable n hn η).hasSum.comp (finiteSeparatorSystems_tendsto n)

theorem physical_limit_equals_separator (n : ℕ) (hn : 1≤n) (κ : ℂ) (hκ : κ≠0) :
    (∑s : Fin (2*n-1+1) → Spin,
      AnalyticVacuum.normalizedVacuum (2*n-1+1) (fun _=>1) s*physicalCutDiagonal (2*n-1) n κ s*
        AnalyticVacuum.normalizedVacuum (2*n-1+1) (fun _=>1) s)=separatorPolynomial n (κ+κ⁻¹) := by
  have : NeZero (2*n):=⟨by omega⟩
  apply tendsto_nhds_unique (finitePhysicalContraction_tendsto (2*n-1) n κ)
  simpa only [centered_partition_identity n hn _ κ hκ] using
    finite_separator_sums_tendsto n hn (κ+κ⁻¹)

end PolynomialVacuumCylinder

end OAI
