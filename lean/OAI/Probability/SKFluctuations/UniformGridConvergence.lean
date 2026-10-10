import Mathlib
import OAI.Probability.SKFluctuations.Graft

namespace OAI

/-! Uniform Grid Convergence. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem HeatJet.uniform_grid_convergence {X : Type*} [TopologicalSpace X] {n : ℕ} (J : HeatJet n)
    (D : Fin (n+1) → ℝ) (hD : ∀ i x, |J.G i x| ≤ D i)
    (α : X → NonnegativeMassProfile) (B : ℝ) (l : ℝ) (t : ℝ≥0)
    (hB : ∀ z, (α z).mass (l+t)-(α z).mass l ≤ B) (x : Fin (n+1) → ℝ) :
    TendstoUniformly (fun k z => (J.schedule (((α z).positiveApprox k).grid l t k)).F x)
      (fun z => J.nonnegativeProfileValue (α z) l t x) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hh : Tendsto (fun k : ℕ => ((∑ i, (D i)^2)/2*t*(B+1))*(1/2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul ((∑ i, (D i)^2)/2*t*(B+1))
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with k hk
  intro z
  rw [Real.dist_eq,abs_sub_comm]
  exact (J.double_grid_error D hD (α z) B l t (hB z) x k).trans_lt hk

 theorem HeatJet.continuous_nonnegativeProfileValue {X : Type*} [TopologicalSpace X] {n : ℕ} (J : HeatJet n)
    (α : X → NonnegativeMassProfile) (hc : ∀ s, Continuous (fun z => (α z).mass s))
    (B : ℝ) (l : ℝ) (t : ℝ≥0) (hB : ∀ z, (α z).mass (l+t)-(α z).mass l ≤ B)
    (x : Fin (n+1) → ℝ) : Continuous (fun z => J.nonnegativeProfileValue (α z) l t x) := by
  choose D _ hD using fun i => (J.smoothG i).bound
  apply (J.uniform_grid_convergence D hD α B l t hB x).continuous
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro k
  exact J.continuous_grid D hD (fun z => (α z).positiveApprox k)
    (fun s => (hc s).add_const _) l t k x

 

def boundedMassProfiles : Set (ℝ → ℝ) :=
  {α | (∀ s, α s ∈ Icc (0:ℝ) 1) ∧ Monotone α}

 theorem boundedMassProfiles_compact : IsCompact boundedMassProfiles := by
  exact (isCompact_pi_infinite (fun _ : ℝ => isCompact_Icc (a := (0:ℝ)) (b := 1))).inter_right
    isClosed_monotone

 def boundedNonnegativeProfile (α : boundedMassProfiles) : NonnegativeMassProfile where
  mass := α.val
  nonneg s := (α.property.1 s).1
  monotone := α.property.2

 theorem continuous_boundedProfile_value {n : ℕ} (J : HeatJet n)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Continuous (fun α : boundedMassProfiles => J.nonnegativeProfileValue (boundedNonnegativeProfile α) l t x) := by
  refine J.continuous_nonnegativeProfileValue boundedNonnegativeProfile (fun s => ?_) 1 l t (fun α => ?_) x
  ·
    exact (continuous_apply s).comp continuous_subtype_val
  · exact sub_le_self _ (α.property.1 l).1 |>.trans (α.property.1 (l+t)).2

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 noncomputable def dyadicLowerSum (f : ℝ → ℝ) (l : ℝ) (t : ℝ≥0) : ℕ → ℝ
  | 0 => t*f l
  | k+1 => dyadicLowerSum f l (t/2) k + dyadicLowerSum f (l+(t:ℝ)/2) (t/2) k

 theorem dyadicLowerSum_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hc : ∀ s, Continuous (fun z => f z s)) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    Continuous (fun z => dyadicLowerSum (f z) l t k) := by
  induction k generalizing l t with
  | zero => exact (hc l).const_mul (t:ℝ)
  | succ k ih =>
    exact ((ih l (t/2)).add (ih (l+(t:ℝ)/2) (t/2))).congr (fun _ => rfl)

 theorem dyadicLowerSum_integral_bounds {f : ℝ → ℝ} (hf : Monotone f)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    0 ≤ (∫ s in l..l+(t:ℝ), f s)-dyadicLowerSum f l t k ∧
    (∫ s in l..l+(t:ℝ), f s)-dyadicLowerSum f l t k ≤
      (t:ℝ)/(2:ℝ)^k*(f (l+t)-f l) := by
  induction k generalizing l t with
  | zero =>
    have hl : l ≤ l+(t:ℝ) := by linarith [t.coe_nonneg]
    have hlo := intervalIntegral.integral_mono_on hl (intervalIntegrable_const : IntervalIntegrable (fun _ => f l) volume l (l+t))
        hf.intervalIntegrable (fun s hs => hf hs.1)
    have hhi := intervalIntegral.integral_mono_on hl hf.intervalIntegrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ => f (l+t)) volume l (l+t)) (fun s hs => hf hs.2)
    simp only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul] at hlo hhi
    simp only [dyadicLowerSum,pow_zero,div_one]
    constructor <;> nlinarith
  | succ k ih =>
    have h₁ := ih l (t/2)
    have h₂ := ih (l+(t:ℝ)/2) (t/2)
    have he : l+(t:ℝ)/2+(t:ℝ)/2 = l+t := by ring
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (a := l) (b := l+(t:ℝ)/2) (μ := volume))
      (hf.intervalIntegrable (a := l+(t:ℝ)/2) (b := l+(t:ℝ)) (μ := volume))
    simp only [NNReal.coe_div,NNReal.coe_ofNat,he] at h₁ h₂
    simp only [dyadicLowerSum]
    rw [← hi]
    constructor
    · linarith [h₁.1,h₂.1]
    · have hh := add_le_add h₁.2 h₂.2
      apply le_trans (by linarith : _ ≤ (t:ℝ)/2/2^k*(f (l+(t:ℝ)/2)-f l) +
        (t:ℝ)/2/2^k*(f (l+t)-f (l+(t:ℝ)/2)))
      apply le_of_eq
      rw [pow_succ]
      ring

 theorem dyadicLowerSum_integral_error {f : ℝ → ℝ} (hf : Monotone f)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    |(∫ s in l..l+(t:ℝ), f s)-dyadicLowerSum f l t k| ≤
      (t:ℝ)*(f (l+t)-f l)*(1/2:ℝ)^k := by
  have hh := dyadicLowerSum_integral_bounds hf l t k
  rw [abs_of_nonneg hh.1]
  apply hh.2.trans_eq
  rw [div_pow,one_pow]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

 
def scalarFeature (σ : Bool) : (Fin 1 → ℝ) →L[ℝ] ℝ :=
  (if σ then (1:ℝ) else -1) • ContinuousLinearMap.proj 0

noncomputable def scalarTerminal : HeatJet 0 :=
  gaussianFeatureJet (w := fun _ : Bool => (1/2:ℝ)) (by intro σ; norm_num)
    scalarFeature (fun _ => 0) (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) []
    (a := 0) (by constructor <;> norm_num) 0

 theorem scalarTerminal_F (x : Fin 1 → ℝ) :
    scalarTerminal.F x = Real.log (Real.cosh (x 0)) := by
  change Real.log (spinPartition (fun _ : Bool => (1/2:ℝ)) scalarFeature (0+x)) = _
  rw [zero_add]
  congr 1
  simp only [spinPartition,Fintype.sum_bool,scalarFeature,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Bool.false_eq_true,↓reduceIte,neg_mul,one_mul]
  rw [Real.cosh_eq]
  ring

 theorem scalarTerminal_G_bound (i : Fin 1) (x : Fin 1 → ℝ) :
    |scalarTerminal.G i x| ≤ 1 := by
  change |∑ σ : Bool, spinWeight (fun _ : Bool => (1/2:ℝ)) scalarFeature (0+x) σ*
    scalarFeature σ ((ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) (Pi.single i 1))| ≤ 1
  rw [zero_add]
  have hb (σ : Bool) : |scalarFeature σ ((ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) (Pi.single i 1))| ≤ 1 := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases σ <;> norm_num [scalarFeature,Pi.single_apply]
  calc
    _ ≤ ∑ σ : Bool, |spinWeight (fun _ : Bool => (1/2:ℝ)) scalarFeature x σ *
      scalarFeature σ ((ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) (Pi.single i 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Bool, spinWeight (fun _ : Bool => (1/2:ℝ)) scalarFeature x σ := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul,abs_of_nonneg (spinWeight_nonneg (by intro σ; norm_num) scalarFeature x σ)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb σ)
        (spinWeight_nonneg (by intro σ; norm_num) scalarFeature x σ)
    _ = 1 := sum_spinWeight (by intro σ; norm_num) scalarFeature x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def weightedProfile (α : boundedMassProfiles) (s : ℝ) : ℝ := max s 0 * α.val s

 theorem weightedProfile_monotone (α : boundedMassProfiles) : Monotone (weightedProfile α) := by
  exact (monotone_id.max monotone_const).mul α.property.2 (fun s => le_max_right s 0) (fun s => (α.property.1 s).1)

noncomputable def scalarPenalty (α : boundedMassProfiles) : ℝ := ∫ s in (0:ℝ)..1, weightedProfile α s

 theorem scalarPenalty_eq (α : boundedMassProfiles) :
    scalarPenalty α = ∫ s in (0:ℝ)..1, s*α.val s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
  dsimp only [weightedProfile]
  rw [max_eq_left hs.1]

 theorem scalarPenalty_continuous : Continuous scalarPenalty := by
  have he (α : boundedMassProfiles) (k : ℕ) :
      |scalarPenalty α-dyadicLowerSum (weightedProfile α) 0 1 k| ≤ (1/2:ℝ)^k := by
    have hh := dyadicLowerSum_integral_error (weightedProfile_monotone α) 0 1 k
    simp only [NNReal.coe_one,zero_add,weightedProfile,max_self,zero_mul,sub_zero,
      max_eq_left (by norm_num : (0:ℝ) ≤ 1),one_mul] at hh
    exact hh.trans (mul_le_of_le_one_left (by positivity) (α.property.1 1).2)
  have ht : TendstoUniformly (fun k α => dyadicLowerSum (weightedProfile α) 0 1 k) scalarPenalty atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    filter_upwards [hp.eventually (gt_mem_nhds hε)] with k hk
    intro α
    rw [Real.dist_eq]
    exact (he α k).trans_lt hk
  apply ht.continuous
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro k
  apply dyadicLowerSum_continuous
  intro s
  change Continuous (fun α : boundedMassProfiles => max s 0*α.val s)
  have hc : Continuous (fun α : boundedMassProfiles => α.val s) :=
    (continuous_apply s).comp continuous_subtype_val
  exact hc.const_mul (max s 0)

 

def scalarProfiles : Set boundedMassProfiles :=
  {α | (∀ s < 0, α.val s = 0) ∧ (∀ s > 1, α.val s = 1)}

 theorem scalarProfiles_closed : IsClosed scalarProfiles := by
  change IsClosed ({α : boundedMassProfiles | ∀ s < 0, α.val s = 0} ∩
    {α : boundedMassProfiles | ∀ s > 1, α.val s = 1})
  apply IsClosed.inter
  · simp only [ofPred_forall]
    apply isClosed_iInter
    intro s
    apply isClosed_iInter
    intro _
    exact isClosed_eq ((continuous_apply s).comp continuous_subtype_val) continuous_const
  · simp only [ofPred_forall]
    apply isClosed_iInter
    intro s
    apply isClosed_iInter
    intro _
    exact isClosed_eq ((continuous_apply s).comp continuous_subtype_val) continuous_const

 theorem scalarProfiles_nonempty : scalarProfiles.Nonempty := by
  let α : ℝ → ℝ := fun s => if s < 0 then 0 else 1
  have hb : α ∈ boundedMassProfiles := by
    constructor
    · intro s
      dsimp [α]
      split <;> norm_num
    · intro s t hst
      dsimp [α]
      split_ifs <;> norm_num at *
      linarith
  refine ⟨⟨α,hb⟩,?_,?_⟩
  · intro s hs
    exact ite_eq_left hs
  · intro s hs
    exact ite_eq_right (by linarith)

 def rescaledMassProfile (α : boundedMassProfiles) {T : ℝ} (hT : 0 < T) : NonnegativeMassProfile where
  mass u := α.val (u/T)
  nonneg u := (α.property.1 (u/T)).1
  monotone := α.property.2.comp (monotone_id.div_const hT.le)

 

noncomputable def scalarParisiValue {T : ℝ} (hT : 0 < T) (α : boundedMassProfiles) : ℝ :=
  scalarTerminal.nonnegativeProfileValue (rescaledMassProfile α hT) 0 ⟨T,hT.le⟩ 0 -
    T/2*scalarPenalty α - T/4

 theorem scalarParisiValue_continuous {T : ℝ} (hT : 0 < T) : Continuous (scalarParisiValue hT) := by
  have hp := scalarTerminal.continuous_nonnegativeProfileValue (fun α => rescaledMassProfile α hT)
    (fun s => (continuous_apply (s/T)).comp continuous_subtype_val) 1 0 ⟨T,hT.le⟩
    (fun α => sub_le_self _ (α.property.1 (0/T)).1 |>.trans (α.property.1 ((0+T)/T)).2) 0
  exact ((hp.sub (scalarPenalty_continuous.const_mul (T/2))).sub continuous_const).congr (fun _ => rfl)

 

theorem scalarParisiValue_attains_minimum {T : ℝ} (hT : 0 < T) :
    ∃ α ∈ scalarProfiles, ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β := by
  let _ : CompactSpace boundedMassProfiles := isCompact_iff_compactSpace.mp boundedMassProfiles_compact
  exact scalarProfiles_closed.isCompact.exists_isMinOn scalarProfiles_nonempty
    (scalarParisiValue_continuous hT).continuousOn

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem dyadicLowerSum_integral_error_control {f g : ℝ → ℝ} (hg : Monotone g)
    (hfg : ∀ x y, x ≤ y → |f y-f x| ≤ g y-g x)
    (hfi : ∀ l r, IntervalIntegrable f volume l r) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    |(∫ s in l..l+(t:ℝ), f s)-dyadicLowerSum f l t k| ≤
      (t:ℝ)/(2:ℝ)^k*(g (l+t)-g l) := by
  induction k generalizing l t with
  | zero =>
    have hl : l ≤ l+(t:ℝ) := by linarith [t.coe_nonneg]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := l+t) (C := g (l+t)-g l) (f := fun s => f s-f l)
      (fun s hs => by
        rw [uIoc_of_le hl] at hs
        exact (hfg l s hs.1.le).trans (sub_le_sub_right (hg hs.2) _))
    rw [intervalIntegral.integral_sub (hfi _ _) intervalIntegrable_const,
      intervalIntegral.integral_const] at hh
    simp only [dyadicLowerSum,pow_zero,div_one]
    simpa only [Real.norm_eq_abs,add_sub_cancel_left,smul_eq_mul,abs_of_nonneg t.coe_nonneg,mul_comm] using hh
  | succ k ih =>
    have h₁ := ih l (t/2)
    have h₂ := ih (l+(t:ℝ)/2) (t/2)
    have he : l+(t:ℝ)/2+(t:ℝ)/2 = l+t := by ring
    have hi := intervalIntegral.integral_add_adjacent_intervals (hfi l (l+(t:ℝ)/2))
      (hfi (l+(t:ℝ)/2) (l+t))
    simp only [NNReal.coe_div,NNReal.coe_ofNat,he] at h₁ h₂
    simp only [dyadicLowerSum]
    rw [← hi]
    have ha : (∫ s in l..l+(t:ℝ)/2, f s)+(∫ s in l+(t:ℝ)/2..l+t, f s) -
      (dyadicLowerSum f l (t/2) k+dyadicLowerSum f (l+(t:ℝ)/2) (t/2) k) =
      ((∫ s in l..l+(t:ℝ)/2, f s)-dyadicLowerSum f l (t/2) k) +
      ((∫ s in l+(t:ℝ)/2..l+t, f s)-dyadicLowerSum f (l+(t:ℝ)/2) (t/2) k) := by ring
    rw [ha]
    apply ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq
    rw [pow_succ]
    ring

 theorem monotone_abs_sub_error {α β : ℝ → ℝ} (hα : Monotone α) (hβ : Monotone β)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    |(∫ s in l..l+(t:ℝ), |α s-β s|)-dyadicLowerSum (fun s => |α s-β s|) l t k| ≤
      (t:ℝ)/(2:ℝ)^k*((α (l+t)-α l)+(β (l+t)-β l)) := by
  have hc (x y : ℝ) (hxy : x ≤ y) : abs (abs (α y-β y)-abs (α x-β x)) ≤ (α y+β y)-(α x+β x) := by
    have h₁ := abs_abs_sub_abs_le_abs_sub (α y-β y) (α x-β x)
    have h₂ := abs_sub_le (α y-α x) (0:ℝ) (β y-β x)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg (sub_nonneg.mpr (hα hxy)),
      abs_of_nonneg (sub_nonneg.mpr (hβ hxy))] at h₂
    have he : (α y-β y)-(α x-β x) = (α y-α x)-(β y-β x) := by ring
    rw [he] at h₁
    exact h₁.trans (h₂.trans_eq (by ring))
  have hi (l r : ℝ) : IntervalIntegrable (fun s => |α s-β s|) volume l r := by
    simpa only [Real.norm_eq_abs] using (hα.intervalIntegrable.sub hβ.intervalIntegrable).norm
  have hh := dyadicLowerSum_integral_error_control (hα.add hβ) hc hi l t k
  apply hh.trans_eq
  congr 1
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem PositiveMassProfile.pairedGrid_cost_eq_sum (α β : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    ((α.pairedGrid β l t k).map CoupledHeatClock.cost).sum =
      dyadicLowerSum (fun s => |α.mass s-β.mass s|) l t k := by
  induction k generalizing l t with
  | zero => simp [PositiveMassProfile.pairedGrid,CoupledHeatClock.cost,dyadicLowerSum,mul_comm]
  | succ k ih => simp only [PositiveMassProfile.pairedGrid,List.map_append,List.sum_append,ih,dyadicLowerSum]

 theorem monotone_abs_sub_sum_tendsto {α β : ℝ → ℝ} (hα : Monotone α) (hβ : Monotone β)
    (l : ℝ) (t : ℝ≥0) :
    Tendsto (fun k => dyadicLowerSum (fun s => |α s-β s|) l t k) atTop
      (𝓝 (∫ s in l..l+(t:ℝ), |α s-β s|)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hh : Tendsto (fun k : ℕ => (t:ℝ)*((α (l+t)-α l)+(β (l+t)-β l))*(1/2:ℝ)^k)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul
        ((t:ℝ)*((α (l+t)-α l)+(β (l+t)-β l)))
  apply squeeze_zero (fun _ => dist_nonneg) _ hh
  intro k
  rw [Real.dist_eq,abs_sub_comm]
  apply (monotone_abs_sub_error hα hβ l t k).trans_eq
  rw [div_pow,one_pow]
  ring

 

theorem HeatJet.profileValue_L1_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α β : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |J.profileValue α l t x-J.profileValue β l t x| ≤
      (∑ i, (D i)^2)/2*(∫ s in l..l+(t:ℝ), |α.mass s-β.mass s|) := by
  have ht := monotone_abs_sub_sum_tendsto α.monotone β.monotone l t
  apply le_of_tendsto_of_tendsto ((J.grid_tendsto α l t x).sub (J.grid_tendsto β l t x)).abs
    (ht.const_mul ((∑ i, (D i)^2)/2))
  apply Filter.Eventually.of_forall
  intro k
  have hh := J.schedule_mass_comparison D hD (α.pairedGrid β l t k) x
  rwa [α.pairedGrid_left,α.pairedGrid_right,α.pairedGrid_cost_eq_sum] at hh

 theorem HeatJet.nonnegativeProfileValue_L1_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α β : NonnegativeMassProfile)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |J.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue β l t x| ≤
      (∑ i, (D i)^2)/2*(∫ s in l..l+(t:ℝ), |α.mass s-β.mass s|) := by
  apply le_of_tendsto ((J.regularized_tendsto α l t x).sub (J.regularized_tendsto β l t x)).abs
  apply Filter.Eventually.of_forall
  intro k
  simpa only [NonnegativeMassProfile.positiveApprox,add_sub_add_right_eq_sub] using
    J.profileValue_L1_comparison D hD (α.positiveApprox k) (β.positiveApprox k) l t x

 theorem HeatJet.nonnegativeProfileValue_congr_ae {n : ℕ} (J : HeatJet n)
    (α β : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ)
    (he : α.mass =ᵐ[volume.restrict (Ioc l (l+t))] β.mass) :
    J.nonnegativeProfileValue α l t x = J.nonnegativeProfileValue β l t x := by
  choose D _ hD using fun i => (J.smoothG i).bound
  have hh := J.nonnegativeProfileValue_L1_comparison D hD α β l t x
  have hz : (∫ s in l..l+(t:ℝ), |α.mass s-β.mass s|) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith [t.coe_nonneg])]
    apply integral_eq_zero_of_ae
    filter_upwards [he] with s hs
    simp only [hs,sub_self,abs_zero,Pi.zero_apply]
  rw [hz,mul_zero] at hh
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal BigOperators

 
noncomputable def rightMassProfile (α : boundedMassProfiles) : boundedMassProfiles :=
  ⟨α.val.rightLim, (fun s => ⟨(α.property.1 s).1.trans (α.property.2.le_rightLim le_rfl),
    (α.property.2.rightLim_le (by linarith : s < s+1)).trans (α.property.1 (s+1)).2⟩),
    α.property.2.rightLim⟩

 theorem rightMassProfile_ae (α : boundedMassProfiles) :
    (rightMassProfile α).val =ᵐ[volume] α.val := by
  have hc : ∀ᵐ s ∂(volume : Measure ℝ), ContinuousAt α.val s := by
    rw [ae_iff]
    exact α.property.2.countable_not_continuousAt.measure_zero volume
  filter_upwards [hc] with s hs
  exact hs.continuousWithinAt.rightLim_eq

 theorem rightMassProfile_mem {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    rightMassProfile α ∈ scalarProfiles := by
  constructor
  · intro s hs
    apply le_antisymm _ ((rightMassProfile α).property.1 s).1
    exact (α.property.2.rightLim_le (by linarith : s < s/2)).trans_eq (hα.1 (s/2) (by linarith))
  · intro s hs
    apply le_antisymm ((rightMassProfile α).property.1 s).2
    exact (hα.2 s hs).symm.le.trans (α.property.2.le_rightLim le_rfl)

noncomputable def profileStieltjes (α : boundedMassProfiles) : StieltjesFunction ℝ where
  toFun := α.val.rightLim
  mono' := α.property.2.rightLim
  right_continuous' s := continuousWithinAt_rightLim_Ici (α.property.2.tendsto_rightLim s)

 theorem scalarProfile_tendsto_bot {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    Tendsto α.val atBot (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with s hs
  exact (hα.1 s hs).symm

 theorem scalarProfile_tendsto_top {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    Tendsto α.val atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with s hs
  exact (hα.2 s hs).symm

 theorem profileStieltjes_probability {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    IsProbabilityMeasure (profileStieltjes α).measure := by
  constructor
  rw [(profileStieltjes α).measure_univ
    (scalarProfile_tendsto_bot (rightMassProfile_mem hα))
    (scalarProfile_tendsto_top (rightMassProfile_mem hα)),sub_zero, ENNReal.ofReal_one]

 theorem cdf_profileStieltjes {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    cdf (profileStieltjes α).measure = profileStieltjes α :=
  cdf_measure_stieltjesFunction _ (scalarProfile_tendsto_bot (rightMassProfile_mem hα))
    (scalarProfile_tendsto_top (rightMassProfile_mem hα))

 theorem scalarParisiValue_congr_ae {T : ℝ} (hT : 0 < T) {α β : boundedMassProfiles}
    (he : α.val =ᵐ[volume] β.val) : scalarParisiValue hT α = scalarParisiValue hT β := by
  have hs : (rescaledMassProfile α hT).mass =ᵐ[volume] (rescaledMassProfile β hT).mass := by
    have hh := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hT.ne')).ae_eq_comp he
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm,rescaledMassProfile,Function.comp_def] using hh
  have hp := scalarTerminal.nonnegativeProfileValue_congr_ae (rescaledMassProfile α hT)
    (rescaledMassProfile β hT) 0 ⟨T,hT.le⟩ 0 (ae_restrict_of_ae hs)
  have hpen : scalarPenalty α = scalarPenalty β := by
    rw [scalarPenalty_eq,scalarPenalty_eq]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [he] with s hs
    intro _
    rw [hs]
  unfold scalarParisiValue
  rw [hp,hpen]

 

theorem scalarParisiValue_attains_distribution {T : ℝ} (hT : 0 < T) :
    ∃ (α : boundedMassProfiles), α ∈ scalarProfiles ∧
      (∀ s, ContinuousWithinAt α.val (Ici s) s) ∧
      IsProbabilityMeasure (profileStieltjes α).measure ∧
      (∀ s, cdf (profileStieltjes α).measure s = α.val s) ∧
      ∀ β ∈ scalarProfiles, scalarParisiValue hT α ≤ scalarParisiValue hT β := by
  obtain ⟨α,hα,hmin⟩ := scalarParisiValue_attains_minimum hT
  let β := rightMassProfile α
  have hβ := rightMassProfile_mem hα
  have hc (s : ℝ) : ContinuousWithinAt β.val (Ici s) s :=
    continuousWithinAt_rightLim_Ici (α.property.2.tendsto_rightLim s)
  refine ⟨β,hβ,hc,profileStieltjes_probability hβ,?_,?_⟩
  · intro s
    rw [cdf_profileStieltjes hβ]
    exact (hc s).rightLim_eq
  · intro γ hγ
    rw [scalarParisiValue_congr_ae hT (rightMassProfile_ae α)]
    exact hmin γ hγ

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal BigOperators

 theorem profileStieltjes_left_zero {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    Function.leftLim (profileStieltjes α) 0 = 0 := by
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ((rightMassProfile_mem hα).1 s hs).symm

 theorem profileStieltjes_one {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    profileStieltjes α 1 = 1 := by
  change α.val.rightLim 1 = 1
  apply rightLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hα.2 s hs).symm

 

theorem profileStieltjes_carried {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    ∀ᵐ s ∂(profileStieltjes α).measure, s ∈ Icc (0:ℝ) 1 := by
  rw [ae_iff]
  change (profileStieltjes α).measure ((Icc (0:ℝ) 1)ᶜ) = 0
  have he : (Icc (0:ℝ) 1)ᶜ = Iio 0 ∪ Ioi 1 := by ext s; simp only [mem_compl_iff,mem_Icc,not_and_or,not_le,mem_union,mem_Iio,mem_Ioi]
  rw [he,measure_union_null_iff]
  constructor
  · rw [(profileStieltjes α).measure_Iio (scalarProfile_tendsto_bot (rightMassProfile_mem hα)),
      profileStieltjes_left_zero hα,sub_self,ENNReal.ofReal_zero]
  · rw [(profileStieltjes α).measure_Ioi (scalarProfile_tendsto_top (rightMassProfile_mem hα)),
      profileStieltjes_one hα,sub_self,ENNReal.ofReal_zero]

 theorem profileStieltjes_Icc {α : boundedMassProfiles} (hα : α ∈ scalarProfiles) :
    (profileStieltjes α).measure (Icc (0:ℝ) 1) = 1 := by
  let _ := profileStieltjes_probability hα
  exact (mem_ae_iff_prob_eq_one measurableSet_Icc).mp (profileStieltjes_carried hα)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem HeatJet.grid_constant {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {m : ℝ} (hm : 0 < m) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ)) (k : ℕ)
    (hc : ∀ s ∈ Ico l (l+t), α.mass s = m) :
    (J.schedule (α.grid l t k)).F = clockContinuation m J.F t := by
  induction k generalizing J l t with
  | zero =>
    change clockContinuation (α.mass l) J.F t = _
    rw [hc l ⟨le_rfl,by linarith⟩]
  | succ k ih =>
    have hhalf : 0 < ((t/2:ℝ≥0):ℝ) := by simpa using half_pos ht
    have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s = m := by
      intro s hs
      apply hc s
      simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
      exact ⟨hs.1,by linarith [hs.2]⟩
    have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s = m := by
      intro s hs
      apply hc s
      simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
      constructor <;> linarith [hs.1,hs.2]
    rw [PositiveMassProfile.grid,J.schedule_append]
    rw [ih _ l (t/2) hhalf hl,ih J (l+(t:ℝ)/2) (t/2) hhalf hr]
    funext x
    rw [clockContinuation_add J.lipschitz hm.ne' (by positivity) (by positivity)]
    congr 1
    simp only [NNReal.coe_div,NNReal.coe_ofNat]
    ring

 theorem HeatJet.profileValue_constant {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {m : ℝ} (hm : 0 < m) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ))
    (hc : ∀ s ∈ Ico l (l+t), α.mass s = m) (x : Fin (n+1) → ℝ) :
    J.profileValue α l t x = clockContinuation m J.F t x := by
  apply tendsto_nhds_unique (J.grid_tendsto α l t x)
  have he : (fun k => (J.schedule (α.grid l t k)).F x) =
      (fun _ : ℕ => clockContinuation m J.F t x) := by
    funext k
    rw [J.grid_constant α hm l t ht k hc]
  rw [he]
  exact tendsto_const_nhds

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem HeatJet.grid_step {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ))
    (j r : ℕ) (hc : ∀ s ∈ Ico l (l+t), α.mass s = if s < l+(t:ℝ)/2^j then a else b) :
    (J.schedule (α.grid l t (j+r))).F =
      clockContinuation a (clockContinuation b J.F ((t:ℝ)-(t:ℝ)/2^j)) ((t:ℝ)/2^j) := by
  induction j generalizing J l t with
  | zero =>
    simp only [pow_zero,div_one,Nat.zero_add,sub_self]
    have hz : clockContinuation b J.F 0 = J.F := funext (clockContinuation_zero hb.ne')
    rw [hz]
    apply J.grid_constant α ha l t ht r
    intro s hs
    rw [hc s hs,ite_eq_left]
    simpa only [pow_zero,div_one] using hs.2
  | succ j ih =>
    have hp : (0:ℝ) < 2^j := by positivity
    have he : (((t/2:ℝ≥0):ℝ)/2^j) = (t:ℝ)/2^(j+1) := by
      simp only [NNReal.coe_div,NNReal.coe_ofNat,pow_succ]
      ring
    have hq : (t:ℝ)/2^(j+1) ≤ (t:ℝ)/2 := by
      apply div_le_div_of_nonneg_left ht.le (by norm_num)
      rw [pow_succ]
      nlinarith [(one_le_pow₀ (n := j) (by norm_num : (1:ℝ) ≤ 2))]
    have hhalf : 0 < ((t/2:ℝ≥0):ℝ) := by simpa using half_pos ht
    have hl : ∀ s ∈ Ico l (l+(t/2:ℝ≥0)), α.mass s =
        if s < l+((t/2:ℝ≥0):ℝ)/2^j then a else b := by
      intro s hs
      rw [he]
      apply hc s
      simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
      exact ⟨hs.1,by linarith [hs.2]⟩
    have hr : ∀ s ∈ Ico (l+(t:ℝ)/2) (l+(t:ℝ)/2+(t/2:ℝ≥0)), α.mass s = b := by
      intro s hs
      have hs' : s ∈ Ico l (l+t) := by
        simp only [NNReal.coe_div,NNReal.coe_ofNat] at hs
        constructor <;> linarith [hs.1,hs.2]
      rw [hc s hs',ite_eq_right]
      linarith [hs.1]
    rw [Nat.succ_add,PositiveMassProfile.grid,J.schedule_append]
    rw [ih _ l (t/2) hhalf hl,J.grid_constant α hb (l+(t:ℝ)/2) (t/2) hhalf (j+r) hr]
    rw [he]
    have hmerge : clockContinuation b (clockContinuation b J.F ((t/2:ℝ≥0):ℝ))
        (((t/2:ℝ≥0):ℝ)-(t:ℝ)/2^(j+1)) =
        clockContinuation b J.F ((t:ℝ)-(t:ℝ)/2^(j+1)) := by
      funext y
      rw [clockContinuation_add J.lipschitz hb.ne'
        (by simpa only [NNReal.coe_div,NNReal.coe_ofNat] using sub_nonneg.mpr hq)
        (by positivity)]
      congr 1
      simp only [NNReal.coe_div,NNReal.coe_ofNat]
      ring
    rw [hmerge]

 theorem HeatJet.profileValue_step {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (l : ℝ) (t : ℝ≥0) (ht : 0 < (t:ℝ))
    (j : ℕ) (hc : ∀ s ∈ Ico l (l+t), α.mass s = if s < l+(t:ℝ)/2^j then a else b)
    (x : Fin (n+1) → ℝ) :
    J.profileValue α l t x =
      clockContinuation a (clockContinuation b J.F ((t:ℝ)-(t:ℝ)/2^j)) ((t:ℝ)/2^j) x := by
  have hh := (J.grid_tendsto α l t x).comp (tendsto_add_atTop_nat j)
  apply tendsto_nhds_unique hh
  have he : (fun r : ℕ => (J.schedule (α.grid l t (r+j))).F x) =
      (fun _ : ℕ => clockContinuation a (clockContinuation b J.F ((t:ℝ)-(t:ℝ)/2^j)) ((t:ℝ)/2^j) x) := by
    funext r
    rw [Nat.add_comm,J.grid_step α ha hb l t ht j r hc]
  change Tendsto (fun r : ℕ => (J.schedule (α.grid l t (r+j))).F x) _ _
  rw [he]
  exact tendsto_const_nhds

end SKFluctuations.Hierarchy

end

end OAI
