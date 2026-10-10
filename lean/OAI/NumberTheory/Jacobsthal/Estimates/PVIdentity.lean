/-
This file has been adapted from an external source.
An attribution header has been generated because the source file did not contain a copyright header.
The applicable license information is stated below.
-/

/-
Generated attribution header: the source file did not contain a copyright header.
This file is adapted from PrimeNumberTheoremAnd.IEANTN.PVIdentity.
Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/PVIdentity.lean
License: Apache License 2.0.

This code has been modified.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.Harmonic.GammaDeriv

namespace OAI

namespace Erdos970

section

open Real Set MeasureTheory Filter Topology Finset
open scoped NNReal ENNReal

lemma integral_exp_div_neg_eq {ε : ℝ} (hε : 0 < ε) :
    ∫ u in (-1/ε)..(-ε), exp u / u = -(∫ t in ε..(1/ε), exp (-t) / t) := by
  have _ := hε
  have h_subst : ∫ u in (-1 / ε)..(-ε), Real.exp u / u = ∫ t in (ε : ℝ)..1 / ε, Real.exp (-t) / (-t) := by
    have h_sub : ∀ a b : ℝ, ∫ u in a..b, Real.exp u / u = ∫ t in (-b)..(-a), Real.exp (-t) / (-t) := by
      norm_num [ ← intervalIntegral.integral_comp_neg ]
    grind;
  simpa [ div_neg ] using h_subst

lemma integral_exp_div_split {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in a..b, exp u / u = (∫ u in a..b, (exp u - 1) / u) + (log b - log a) := by
  simp +decide [ sub_div ];
  rw [ intervalIntegral.integral_sub ];
  · rw [ integral_inv_of_pos, Real.log_div ] <;> linarith;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id <| by linarith [ Set.mem_Icc.mp <| by simpa [ hab ] using hu ] ) ..;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ continuousAt_id ( by cases Set.mem_uIcc.mp hx <;> linarith )

lemma integrableOn_one_sub_exp_neg_div :
    IntegrableOn (fun t => (1 - exp (-t)) / t) (Ioc 0 1) := by

  have h_bound : ∀ t ∈ Set.Ioc 0 1, (1 - Real.exp (-t)) / t ≤ 1 := by
    exact fun t ht => by rw [ div_le_iff₀ ht.1 ] ; linarith [ Real.add_one_le_exp ( -t ) ] ;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun t => 1, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( measurable_const.sub ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ) measurable_id' ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun t ht => by rw [ Real.norm_of_nonneg ( div_nonneg ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith [ ht.1, ht.2 ] ) ht.1.le ) ] ; exact h_bound t ht ]

lemma integrableOn_exp_neg_div_Ioi :
    IntegrableOn (fun t => exp (-t) / t) (Ioi 1) := by

  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 1) := by
    exact MeasureTheory.IntegrableOn.mono_set ( by exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) ( Set.Ioi_subset_Ioi zero_le_one );
  refine' h_integrable.mono' _ _;
  · exact ContinuousOn.aestronglyMeasurable ( fun t ht => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.div ( ContinuousAt.rexp ( continuousAt_id.neg ) ) continuousAt_id ( by linarith [ ht.out ] ) ) ) measurableSet_Ioi;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.exp_pos _ |> le_of_lt ) ( by linarith [ hx.out ] ) ) ] ; exact div_le_self ( Real.exp_pos _ |> le_of_lt ) ( by linarith [ hx.out ] ) ;

lemma integrableOn_exp_sub_one_div {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun u => (exp u - 1) / u) (Ioc 0 y) := by
  have _ := hy
  have h_bounded : ∀ u ∈ Set.Ioc 0 y, |(Real.exp u - 1) / u| ≤ Real.exp y := by
    norm_num [ abs_div ];
    intro u hu huy; rw [ abs_of_nonneg ( sub_nonneg_of_le ( Real.one_le_exp hu.le ) ), abs_of_nonneg hu.le ] ; rw [ div_le_iff₀ hu ] ; nlinarith [ Real.exp_pos u, Real.exp_le_exp.2 huy, Real.exp_neg u, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos u ) ), Real.add_one_le_exp u, Real.add_one_le_exp ( -u ) ] ;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun u => Real.exp y, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( Real.continuous_exp.measurable.sub measurable_const ) measurable_id' ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun u hu => h_bounded u hu ]

lemma tendsto_integral_one_sub_exp_neg_div :
    Tendsto (fun ε => ∫ t in ε..1, (1 - exp (-t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t)) := by

  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioc 0 1) := by
    exact integrableOn_one_sub_exp_neg_div;

  have h_cont : ContinuousOn (fun ε => ∫ t in (ε)..1, (1 - Real.exp (-t)) / t) (Set.Icc 0 1) := by
    have h_cont : ContinuousOn (fun ε => ∫ t in (1 : ℝ)..ε, (1 - Real.exp (-t)) / t) (Set.Icc 0 1) := by
      intro ε hε; apply_rules [ intervalIntegral.continuousWithinAt_primitive ] ; aesop;
      rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ] <;> aesop;
    exact ContinuousOn.congr ( h_cont.fun_neg ) fun x hx => by rw [ ← intervalIntegral.integral_symm ] ;
  have := h_cont 0 ( by norm_num );
  convert this.tendsto.mono_left _ using 2 ; norm_num [ Set.Ioi_subset_Ici_self ];
  exact nhdsWithin_mono _ <| Set.Ioi_subset_Ici_self

lemma tendsto_integral_exp_neg_div_Ioi :
    Tendsto (fun ε => ∫ t in (1:ℝ)..(1/ε), exp (-t) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Ioi (1:ℝ), exp (-t) / t)) := by

  simp at * ; have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi 1) := by
    exact integrableOn_exp_neg_div_Ioi;
  apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
  norm_num [ Filter.Tendsto ]

lemma tendsto_integral_exp_sub_one_div {y : ℝ} (hy : 0 < y) :
    Tendsto (fun ε => ∫ u in ε..y, (exp u - 1) / u)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ u in (0:ℝ)..y, (exp u - 1) / u)) := by

  have h_integrable : MeasureTheory.IntegrableOn (fun u => (Real.exp u - 1) / u) (Set.Ioc 0 y) := by
    exact integrableOn_exp_sub_one_div hy;

  obtain ⟨M, hM⟩ : ∃ M > y, True := by
    exact ⟨ y + 1, by linarith, trivial ⟩;

  have h_cont : ContinuousOn (fun ε => ∫ u in ε..y, (Real.exp u - 1) / u) (Set.Icc 0 M) := by
    have h_integrable_M : MeasureTheory.IntegrableOn (fun u => (Real.exp u - 1) / u) (Set.Ioc 0 M) := by
      have h_integrable_M : MeasureTheory.IntegrableOn (fun u => (Real.exp u - 1) / u) (Set.Ioc y M) := by
        exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) continuousAt_id <| by linarith [ hu.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
      convert h_integrable.union h_integrable_M using 1 ; rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith;
    have h_cont : ContinuousOn (fun ε => ∫ u in (y)..ε, (Real.exp u - 1) / u) (Set.Icc 0 M) := by
      intro ε hε; apply_rules [ intervalIntegral.continuousWithinAt_primitive ] ; aesop;
      rw [ min_eq_right hy.le, max_eq_right hM.1.le ] ; rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ( by linarith ) ] ; aesop;
    exact ContinuousOn.congr ( h_cont.fun_neg ) fun x hx => by rw [ ← intervalIntegral.integral_symm ] ;
  have := h_cont 0 ⟨ by norm_num, by linarith ⟩;
  convert this.tendsto.mono_left _ using 2;
  norm_num [ nhdsWithin, Filter.mem_inf_principal ];
  exact Filter.eventually_of_mem ( Iio_mem_nhds <| show 0 < M by linarith ) fun x hx => fun hx' => ⟨ le_of_lt hx', le_of_lt hx ⟩

lemma eulerMascheroni_eq_integral :
    eulerMascheroniConstant =
      (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t := by

  have h_gamma_deriv : Real.eulerMascheroniConstant = -∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by
    have h_gamma_deriv : deriv Real.Gamma 1 = ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by

      have h_gamma_deriv : deriv Real.Gamma 1 = ∫ t in Set.Ioi 0, t^0 * Real.exp (-t) * Real.log t := by
        have h_def : ∀ s > 0, Real.Gamma s = ∫ t in Set.Ioi 0, t^(s-1) * Real.exp (-t) := by
          exact fun s hs => by rw [ Real.Gamma_eq_integral hs ] ; congr; ext; ring;

        have h_dominated : Filter.Tendsto (fun h => ∫ t in Set.Ioi 0, (t^h - 1) / h * Real.exp (-t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t in Set.Ioi 0, Real.log t * Real.exp (-t))) := by

          have h_dominate : ∀ h ∈ Set.Ioo 0 1, ∀ t ∈ Set.Ioi 0, abs ((t^h - 1) / h * Real.exp (-t)) ≤ abs (Real.log t) * Real.exp (-t) * (t + 1) := by
            intros h hh t ht
            have h_abs : abs ((t^h - 1) / h) ≤ abs (Real.log t) * (t + 1) := by

              obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 h, t^h - 1 = h * t^c * Real.log t := by

                have h_mean_value : ∃ c ∈ Set.Ioo 0 h, deriv (fun x => t^x) c = (t^h - 1) / h := by
                  have := exists_deriv_eq_slope ( f := fun x => t ^ x ) hh.1;
                  simpa using this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith [ ht.out ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_const _ ) differentiableAt_id <| by linarith [ ht.out ] );
                norm_num [ Real.rpow_def_of_pos ht, mul_assoc, mul_comm, mul_left_comm ] at *;
                exact h_mean_value.imp fun x hx => ⟨ hx.1, by rw [ hx.2, mul_div_cancel₀ _ hh.1.ne' ] ⟩;
              by_cases h_zero : h = 0 <;> simp_all +decide [ abs_mul, mul_assoc, mul_comm ];
              by_cases h₂ : t ≤ 1;
              · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg ht.le _ ) ] ; exact le_trans ( Real.rpow_le_one ht.le h₂ ( by linarith ) ) ( by linarith ) ) ( abs_nonneg _ );
              · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg ht.le _ ) ] ; exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show c ≤ 1 by linarith ) ) ( by norm_num ) ) ( abs_nonneg _ );
            rw [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ] ; nlinarith [ Real.exp_pos ( -t ) ];

          have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t) * (t + 1)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t) * t) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * abs (Real.log t)) (Set.Ioi 0) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * abs (Real.log t)) (Set.Ioc 0 1) := by
                  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * abs (Real.log t)) (Set.Ioc 0 1) := by
                    have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.log t) (Set.Ioc 0 1) := by
                      exact Continuous.integrableOn_Ioc ( Real.continuous_mul_log );
                    refine' h_integrable.norm.congr _;
                    filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1.le ] ;
                  refine' h_integrable.mono' _ _;
                  · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_neg.aestronglyMeasurable ) ) ) ( Real.measurable_log.norm.aestronglyMeasurable );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ht.1.le ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right ht.1.le ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ht.1.le ) ) ) ( abs_nonneg _ ) ;
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * abs (Real.log t)) (Set.Ioi 1) := by
                  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * t) (Set.Ioi 1) := by
                    have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t^2 * Real.exp (-t)) (Set.Ioi 1) := by
                      have h_gamma : ∫ t in Set.Ioi 0, t^2 * Real.exp (-t) = Real.Gamma 3 := by
                        rw [ h_def ] <;> norm_num;
                      exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                    exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
                  refine' h_integrable.mono' _ _;
                  · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ) ( Real.measurable_log.norm ) );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ ht.out ] ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith [ ht.out ] ) ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ ht.out ] ) ) ( by linarith [ ht.out ] ) ) ( mul_nonneg ( by linarith [ ht.out ] ) ( Real.exp_nonneg _ ) ) ;
                convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun t : ℝ => t * Real.exp ( -t ) * |log t| ) ( Set.Ioc 0 1 ) volume› ‹IntegrableOn ( fun t : ℝ => t * Real.exp ( -t ) * |log t| ) ( Set.Ioi 1 ) volume› using 1 ; norm_num;
              exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
            have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t)) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t)) (Set.Ioc 0 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t)) (Set.Ioc 0 1) := by
                  have h_integrable : ∫ t in Set.Ioc 0 1, abs (Real.log t) = 1 := by
                    rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2 ), ← intervalIntegral.integral_of_le ] <;> norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
                refine' h_integrable.mono' _ _;
                · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr ht.1.le ) <| abs_nonneg <| Real.log t;
              have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t)) (Set.Ioi 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Set.Ioi 1) := by
                  have := @integral_rpow_mul_exp_neg_rpow 1;
                  specialize @this 1 ; norm_num at this;
                  exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num ) ) ) ) ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                refine' h_integrable.mono' _ _;
                · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log.norm ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.log_nonneg ht.out.le ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ ht.out ] ) ) ( by linarith [ ht.out ] ) ) ( by positivity ) ;
              convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun t : ℝ => |Real.log t| * Real.exp ( -t ) ) ( Set.Ioc 0 1 ) volume› ‹IntegrableOn ( fun t : ℝ => |Real.log t| * Real.exp ( -t ) ) ( Set.Ioi 1 ) volume› using 1 ; norm_num;
            simp_all +decide [ mul_add ];
            exact MeasureTheory.Integrable.add ‹_› ‹_›;
          refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
          refine' fun t => |Real.log t| * Real.exp ( -t ) * ( t + 1 );
          · filter_upwards [ self_mem_nhdsWithin ] with n hn using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.div_const ( by exact Measurable.sub ( measurable_id.pow_const _ ) measurable_const ) _ ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
          · filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with h hh using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun t ht => h_dominate h hh t ht;
          · exact h_integrable;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
            refine' Filter.Tendsto.mul _ tendsto_const_nhds;
            simpa [ div_eq_inv_mul, Real.rpow_def_of_pos ht ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( HasDerivAt.exp ( HasDerivAt.const_mul ( Real.log t ) ( hasDerivAt_id 0 ) ) ) ( hasDerivAt_const 0 1 ) );

        have h_deriv : Filter.Tendsto (fun h => (Real.Gamma (1 + h) - Real.Gamma 1) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv Real.Gamma 1)) := by
          have h_deriv : HasDerivAt Real.Gamma (deriv Real.Gamma 1) 1 := by
            exact DifferentiableAt.hasDerivAt ( Real.differentiableAt_Gamma fun m => by linarith );
          simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;

        have h_gamma_def : ∀ h > 0, (Real.Gamma (1 + h) - Real.Gamma 1) / h = ∫ t in Set.Ioi 0, (t^h - 1) / h * Real.exp (-t) := by
          intro h hh; rw [ h_def ( 1 + h ) ( by linarith ), h_def 1 zero_lt_one ] ; simp +decide [ sub_mul, div_mul_eq_mul_div, MeasureTheory.integral_div ] ;
          rw [ MeasureTheory.integral_sub ] <;> norm_num [ integral_exp_Iic ];
          · have := @integral_rpow_mul_exp_neg_rpow 1;
            exact ( by have := @this h ( by norm_num ) ( by linarith ) ; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef ( by aesop ) ] ; positivity ) );
          · exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero );
        simpa [ mul_assoc, mul_comm, mul_left_comm ] using tendsto_nhds_unique h_deriv ( h_dominated.congr' <| Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => h_gamma_def x hx ▸ rfl );
      aesop;
    rw [ ← h_gamma_deriv, Real.eulerMascheroniConstant_eq_neg_deriv ];

  have h_split : ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t = (∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t) + (∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t) := by
    rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
    · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.log t) (Set.Ioc 0 1) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one ];
        norm_num +zetaDelta at *;
      refine' h_integrable.norm.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) h_integrable.aestronglyMeasurable;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ norm_mul, Real.norm_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1, hx.2 ] ) ;
    ·
      have h_conv : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Set.Ioi 1) := by
        have h_integrable : ∫ t in Set.Ioi 0, Real.exp (-t) * t = Real.Gamma 2 := by
          rw [ Real.Gamma_eq_integral ] <;> norm_num;
        exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
      refine' h_conv.mono' _ _;
      · exact ContinuousOn.aestronglyMeasurable ( fun t ht => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.mul ( ContinuousAt.rexp ( continuousAt_id.neg ) ) ( Real.continuousAt_log ( by linarith [ ht.out ] ) ) ) ) measurableSet_Ioi;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.log_nonneg ht.out.le ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans ht.out ) ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt ) ;

  have h_log_zero_one : ∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t = -∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s := by
    have h_log_zero_one : ∀ t ∈ Set.Ioc 0 1, Real.log t = -∫ s in t..1, 1 / s := by
      intro t ht; rw [ integral_one_div_of_pos ] <;> aesop;
    rw [ ← MeasureTheory.integral_neg ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ h_log_zero_one x hx ] ; simp +decide [ div_eq_mul_inv, mul_comm ] ;

  have h_fubini : ∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s = ∫ s in Set.Ioc 0 1, ∫ t in Set.Ioc 0 s, Real.exp (-t) / s := by
    have h_fubini : ∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s = ∫ t in Set.Ioc 0 1, ∫ s in Set.Ioc 0 1, (if t ≤ s then Real.exp (-t) / s else 0) := by
      refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => _;
      rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      rw [ intervalIntegral.integral_of_le ht.2 ];
      rw [ ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      grind;
    rw [ h_fubini, ← MeasureTheory.integral_integral_swap ];
    · norm_num [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
      grind +splitImp;
    · rw [ MeasureTheory.integrable_prod_iff ];
      · field_simp;
        constructor;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
          refine' MeasureTheory.Integrable.indicator _ _;
          · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( Real.continuous_exp.comp <| ContinuousNeg.continuous_neg ) _ );
          · exact measurableSet_Iic;
        · refine' MeasureTheory.Integrable.congr _ _;
          use fun x => ∫ y in Set.Ioc 0 x, Real.exp ( -y ) / x;
          ·
            have h_inner : ∀ x ∈ Set.Ioc 0 1, ∫ y in Set.Ioc 0 x, Real.exp (-y) / x = (1 - Real.exp (-x)) / x := by
              intro x hx; rw [ ← intervalIntegral.integral_of_le hx.1.le ] ; norm_num [ intervalIntegral.integral_comp_neg ] ;
            rw [ MeasureTheory.integrable_congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => h_inner x hx ) ];
            refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 1;
            · norm_num;
            · exact ContinuousOn.aestronglyMeasurable ( fun x hx => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.div ( continuousAt_const.sub ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) ) ) continuousAt_id ( ne_of_gt hx.1 ) ) ) measurableSet_Ioc;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith [ hx.1, hx.2 ] ) hx.1.le ) ] ; exact div_le_one_of_le₀ ( by linarith [ hx.1, hx.2, Real.add_one_le_exp ( -x ) ] ) hx.1.le;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
            rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
            congr with y ; split_ifs <;> norm_num;
            · rw [ abs_of_nonneg ( div_nonneg ( Real.exp_nonneg _ ) hx.1.le ) ];
            · grind +revert;
            · grind;
            · aesop;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_le measurable_snd measurable_fst ) ( by exact Measurable.div ( Real.continuous_exp.measurable.comp ( measurable_neg.comp measurable_snd ) ) measurable_fst ) measurable_const );

  have h_log_one_infty : ∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t = ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
    norm_num [ div_eq_mul_inv, ht.out.le ];

  have h_fubini_one_infty : ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s = ∫ s in Set.Ioi 1, ∫ t in Set.Ioi s, Real.exp (-t) / s := by
    have h_fubini_one_infty : ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s = ∫ s in Set.Ioi 1, ∫ t in Set.Ioi 1, Real.exp (-t) / s * (if s ≤ t then 1 else 0) := by
      rw [ ← MeasureTheory.integral_integral_swap ];
      · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
        rw [ intervalIntegral.integral_of_le ht.out.le, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        simp only [ ← ite_and ];
      · rw [ MeasureTheory.integrable_prod_iff ];
        · constructor;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;

            have h_integrable : MeasureTheory.IntegrableOn (fun y => Real.exp (-t) / y) (Set.Ioc 1 t) := by
              exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ hx.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
            rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ioc ) ] at h_integrable;
            rw [ MeasureTheory.integrable_congr ];
            convert h_integrable.restrict;
            filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with y hy using by rw [ Set.indicator_apply ] ; aesop;
          · refine' MeasureTheory.Integrable.congr _ _;
            use fun x => ∫ y in Set.Ioc 1 x, Real.exp ( -x ) / y;
            ·
              have h_inner : ∀ x ∈ Set.Ioi 1, ∫ y in Set.Ioc 1 x, Real.exp (-x) / y = Real.exp (-x) * Real.log x := by
                intro x hx; rw [ ← intervalIntegral.integral_of_le hx.out.le ] ; norm_num [ div_eq_mul_inv, hx.out.le ] ;
              rw [ MeasureTheory.integrable_congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) h_inner ) ];
              have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x) (Set.Ioi 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x) (Set.Ioi 0) := by
                  have h_integrable : ∫ x in Set.Ioi 0, Real.exp (-x) * x = Real.Gamma 2 := by
                    rw [ Real.Gamma_eq_integral ] <;> norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
                exact h_integrable.mono_set <| Set.Ioi_subset_Ioi zero_le_one;
              refine' h_integrable.mono' _ _;
              · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) ( Real.measurable_log.aestronglyMeasurable );
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.log_nonneg hx.out.le ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans hx.out ) ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt ) ;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx;
              rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
              congr with y ; split_ifs <;> norm_num;
              · rw [ abs_of_nonneg ( div_nonneg ( Real.exp_nonneg _ ) ( by linarith ) ) ];
              · linarith;
              · grind +revert;
              · grind +qlia;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.mul ( Real.continuous_exp.measurable.comp ( measurable_neg.comp measurable_fst ) ) ( measurable_snd.inv ) ) ( by exact Measurable.ite ( measurableSet_le measurable_snd measurable_fst ) measurable_const measurable_const ) );
    rw [ h_fubini_one_infty ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => _;
    rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
    simp +decide [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton s ) ] with x hx using by split_ifs <;> cases lt_or_gt_of_ne hx <;> linarith [ hs.out ] ;
  simp_all +decide [ div_eq_mul_inv, ← intervalIntegral.integral_of_le zero_le_one ];
  rw [ intervalIntegral.integral_of_le zero_le_one ] ; norm_num [ MeasureTheory.integral_mul_const, integral_exp_neg_Ioi ] ; ring_nf;
  norm_num [ integral_exp_Iic, ← intervalIntegral.integral_of_le zero_le_one ] ; ring_nf;
  rw [ intervalIntegral.integral_of_le zero_le_one ] ; rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ ← intervalIntegral.integral_of_le hx.1.le ] ] ; norm_num [ intervalIntegral.integral_comp_neg ] ; ring_nf;
  rw [ intervalIntegral.integral_of_le zero_le_one ]

lemma pv_rewrite {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hε1 : ε < 1) (hεy : ε < y) :
    (∫ u in (-1/ε)..(-ε), exp u / u) + (∫ u in ε..y, exp u / u) =
    (∫ t in ε..1, (1 - exp (-t)) / t) - (∫ t in (1:ℝ)..(1/ε), exp (-t) / t) +
    (∫ u in ε..y, (exp u - 1) / u) + log y := by
  have _ := hy
  have h1 : ∫ u in (-1 / ε)..(-ε), Real.exp u / u = -(∫ t in ε..1 / ε, Real.exp (-t) / t) := by
    exact integral_exp_div_neg_eq hε
  have h2 : ∫ u in ε..y, Real.exp u / u = (∫ v in ε..y, ((Real.exp v) - 1) / v) + Real.log y - Real.log ε := by
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => ∫ u in ε..x, ( Real.exp u - 1 ) / u + 1 / u;
    · rw [ intervalIntegral.integral_add ] <;> norm_num [ hε, hεy.le ];
      · rw [ Real.log_div ] <;> linarith;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) continuousAt_id ( by cases Set.mem_uIcc.mp hu <;> linarith );
      · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ Set.mem_Icc.mp <| by simpa [ hε.le, hεy.le ] using hx ] ) ..;
    · intro x hx; convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
      use fun x => ∫ u in ε..x, Real.exp u / u;
      · apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id ( by cases Set.mem_uIcc.mp hu <;> cases Set.mem_uIcc.mp hx <;> linarith );
        · exact Measurable.stronglyMeasurable ( by exact Measurable.mul ( Real.continuous_exp.measurable ) ( measurable_id.inv ) ) |> fun h => h.stronglyMeasurableAtFilter;
        · exact ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id ( by cases Set.mem_uIcc.mp hx <;> linarith );
      · filter_upwards [ lt_mem_nhds ( show x > 0 by cases Set.mem_uIcc.mp hx <;> linarith ) ] with u hu using by refine' intervalIntegral.integral_congr fun v hv => _ ; rw [ sub_div, sub_add_cancel ] ;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div ( Real.continuous_exp.continuousAt ) continuousAt_id ( by cases Set.mem_uIcc.mp hu <;> linarith );
  rw [ h1, h2 ] ; ring_nf;
  rw [ intervalIntegral.integral_add ] <;> norm_num ; ring_nf;
  · rw [ integral_inv_of_pos, show ( ∫ u in ( ε : ℝ )..ε⁻¹, Real.exp ( -u ) * u⁻¹ ) = ( ∫ u in ( ε : ℝ )..1, Real.exp ( -u ) * u⁻¹ ) + ( ∫ u in ( 1 : ℝ )..ε⁻¹, Real.exp ( -u ) * u⁻¹ ) from ?_ ] <;> norm_num [ hε, hε1, hεy ] ; ring;
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ] <;> exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.mul ( ContinuousAt.rexp <| ContinuousAt.neg <| continuousAt_id ) <| ContinuousAt.inv₀ continuousAt_id <| by cases Set.mem_uIcc.mp hu <;> nlinarith [ inv_mul_cancel₀ hε.ne' ] ;
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.neg ( ContinuousAt.mul ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg continuousAt_id ) <| ContinuousAt.inv₀ continuousAt_id <| by cases Set.mem_uIcc.mp ht <;> linarith );
  · exact Or.inr <| Set.notMem_uIcc_of_lt hε zero_lt_one

theorem pv_exp_div_eq_gamma_add_log_add_integral {y : ℝ} (hy : 0 < y) :
    lim ((𝓝[>] (0 : ℝ)).map (fun ε =>
      (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..y, exp u / u)) =
    eulerMascheroniConstant + log y + ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) := by

  apply lim_eq

  rw [show eulerMascheroniConstant + log y + ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) =
    ((∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t) +
    (∫ u in (0:ℝ)..y, (exp u - 1) / u) + log y by
      rw [← eulerMascheroni_eq_integral]; ring]

  have h_rw : Tendsto
    (fun ε => (∫ t in ε..1, (1 - exp (-t)) / t) - (∫ t in (1:ℝ)..(1/ε), exp (-t) / t) +
      (∫ u in ε..y, (exp u - 1) / u) + log y)
    (𝓝[>] (0 : ℝ))
    (𝓝 (((∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t) +
      (∫ u in (0:ℝ)..y, (exp u - 1) / u) + log y)) := by
    exact ((tendsto_integral_one_sub_exp_neg_div.sub tendsto_integral_exp_neg_div_Ioi).add
      (tendsto_integral_exp_sub_one_div hy)).add tendsto_const_nhds

  apply h_rw.congr'
  have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min y 1 := by
    apply nhdsWithin_le_nhds
    exact Iio_mem_nhds (lt_min hy one_pos)
  filter_upwards [this, self_mem_nhdsWithin] with ε hε hε_pos
  exact (pv_rewrite hy hε_pos (lt_of_lt_of_le hε (min_le_right _ _))
    (lt_of_lt_of_le hε (min_le_left _ _))).symm

end

end Erdos970

end OAI
