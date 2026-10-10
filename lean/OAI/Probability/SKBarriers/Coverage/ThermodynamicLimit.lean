import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileClamp
import OAI.Probability.SKBarriers.Interpolation.GuerraUpper

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def finiteParisiValues (β : ℝ) : Set ℝ :=
  {p | ∃ k : ℕ, ∃ Q : Fin (k+1) → ℝ, Monotone Q ∧
    (∀ j, Q j ∈ Set.Icc 0 1) ∧ p = extendedQuantileParisi k β Q}

def finiteParisiInf (β : ℝ) : ℝ := sInf (finiteParisiValues β)

def quenchedPressure (β : ℝ) (N : ℕ) : ℝ :=
  (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ)

theorem finiteParisiValues_nonempty (β : ℝ) : (finiteParisiValues β).Nonempty := by
  refine ⟨extendedQuantileParisi 0 β (fun _ => 0),0,fun _ => 0,?_,?_,rfl⟩
  · exact monotone_const
  · intro j; exact ⟨le_rfl,zero_le_one⟩

theorem quenched_le_finiteParisiValue {N : ℕ} (hN : 0 < N) (β : ℝ)
    {p : ℝ} (hp : p ∈ finiteParisiValues β) : quenchedPressure β N ≤ p := by
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  exact quenched_le_extendedQuantileParisi hN β Q
    ((cumulativeGapMap_nonneg_iff k Q).mpr ⟨(hQ 0).1,hm⟩)

theorem finiteParisiValues_bddBelow (β : ℝ) : BddBelow (finiteParisiValues β) :=
  ⟨quenchedPressure β 1,fun _ hp => quenched_le_finiteParisiValue (by norm_num) β hp⟩

theorem finiteParisiInf_le {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    finiteParisiInf β ≤ extendedQuantileParisi k β Q :=
  csInf_le (finiteParisiValues_bddBelow β) ⟨k,Q,hm,hQ,rfl⟩

theorem quenched_le_finiteParisiInf {N : ℕ} (hN : 0 < N) (β : ℝ) :
    quenchedPressure β N ≤ finiteParisiInf β :=
  le_csInf (finiteParisiValues_nonempty β) (fun _ hp => quenched_le_finiteParisiValue hN β hp)

def finiteComparisonError (β : ℝ) (k : ℕ) (η : ℝ) (N : ℕ) : ℝ :=
  (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
    2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+4*(((k+1:ℕ):ℝ)*η))

def finiteComparisonErrorLimit (β : ℝ) (k : ℕ) (η : ℝ) : ℝ :=
  (β^2/4)*(20*(1/Real.sqrt (k:ℝ))+
    2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+4*(((k+1:ℕ):ℝ)*η))

theorem finiteParisiInf_sub_error_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    finiteParisiInf β-finiteComparisonError β k η N ≤ quenchedPressure β N := by
  obtain ⟨Q,hm,hQ,H⟩ := exists_admissible_scalar_lower_bound hN hk hβ hη hsmall
  exact (sub_le_sub_right (finiteParisiInf_le β Q hm hQ) _).trans H

theorem finiteComparisonRatio_tendsto (k : ℕ) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (fun N : ℕ => (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))) atTop (𝓝 0) := by
  exact (Real.tendsto_sqrt_atTop.comp
    (Filter.Tendsto.atTop_mul_const (by positivity : 0 < β^2*η)
      (tendsto_natCast_atTop_atTop (R := ℝ)))).const_div_atTop (k:ℝ)

theorem finiteComparisonError_tendsto (k : ℕ) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (finiteComparisonError β k η) atTop (𝓝 (finiteComparisonErrorLimit β k η)) := by
  unfold finiteComparisonError
  have H := finiteComparisonRatio_tendsto k hβ hη
  simpa only [finiteComparisonErrorLimit,zero_add] using
    ((((H.add_const (1/Real.sqrt (k:ℝ))).const_mul 20).add_const
      (2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η))).add_const
        (4*(((k+1:ℕ):ℝ)*η))).const_mul (β^2/4)

theorem finiteComparisonErrorLimit_continuous (β : ℝ) (k : ℕ) :
    Continuous (finiteComparisonErrorLimit β k) := by
  unfold finiteComparisonErrorLimit
  fun_prop

theorem eventually_lt_quenched_of_error {k : ℕ} (hk : 0 < k)
    {β η a : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (ha : a < finiteParisiInf β-finiteComparisonErrorLimit β k η) :
    ∀ᶠ N : ℕ in atTop, a < quenchedPressure β N := by
  have he := (finiteComparisonError_tendsto k hβ hη).eventually_lt_const
    (show finiteComparisonErrorLimit β k η < finiteParisiInf β-a by linarith)
  have hr := (finiteComparisonRatio_tendsto k hβ hη).eventually_lt_const (by norm_num : (0:ℝ)<1)
  filter_upwards [he,hr,eventually_gt_atTop (0:ℕ)] with N hE hR hN
  have H := finiteParisiInf_sub_error_le hN hk hβ hη hR.le
  linarith

theorem eventually_lt_quenched_of_mesh {k : ℕ} (hk : 0 < k) {β a : ℝ} (hβ : 0 < β)
    (ha : a < finiteParisiInf β-(β^2/4)*(20/Real.sqrt (k:ℝ))) :
    ∀ᶠ N : ℕ in atTop, a < quenchedPressure β N := by
  have H := (finiteComparisonErrorLimit_continuous β k).continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : finiteComparisonErrorLimit β k 0 = (β^2/4)*(20/Real.sqrt (k:ℝ)) := by
    simp only [finiteComparisonErrorLimit,mul_zero,add_zero,zero_mul,mul_one_div]
  rw [he] at H
  obtain ⟨n,hn⟩ := (H.eventually (eventually_lt_nhds
    (show (β^2/4)*(20/Real.sqrt (k:ℝ)) < finiteParisiInf β-a by linarith))).exists
  apply eventually_lt_quenched_of_error hk hβ (show 0 < 1/((n:ℝ)+1) by positivity)
  dsimp only [Function.comp_def] at hn
  linarith

theorem quenchedPressure_tendsto_finiteParisiInf {β : ℝ} (hβ : 0 < β) :
    Tendsto (quenchedPressure β) atTop (𝓝 (finiteParisiInf β)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have H : Tendsto (fun k : ℕ => (β^2/4)*(20/Real.sqrt (k:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero,Function.comp_def] using ((Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 20).const_mul (β^2/4)
    have HE := H.eventually (eventually_lt_nhds (sub_pos.mpr ha))
    obtain ⟨k,hk,hE⟩ := ((eventually_gt_atTop (0:ℕ)).and HE).exists
    exact eventually_lt_quenched_of_mesh hk hβ (by linarith)
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact (quenched_le_finiteParisiInf hN β).trans_lt ha
end SK.Analytic

end
end

end

end OAI
