import Mathlib
import OAI.Probability.SKValue.Evolution.GridConvergence
import OAI.Probability.SKValue.Equations.ShortStripClose
import OAI.Probability.SKValue.Evolution.DerivativeLimit
import OAI.Probability.SKValue.Gaussian.ProfileSplit

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma gridDelta_le_one (n:ℕ) : (gridDelta n:ℝ)≤1 := by
  change 1/(n+1:ℝ)≤1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]
lemma OrderParameter.splitGrid_le (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) :
    profileCoeff (γ.splitGrid t n) s≤γ.coeff s+(gridDelta n:ℝ) := by
  obtain ⟨r,hr,he,hrs,_⟩:=γ.splitGrid_sample t n ⟨hs.1,hs.2.le⟩
  rw [he]
  exact add_le_add (γ.monotone hr hs hrs) le_rfl
lemma OrderParameter.splitGrid_tendsto (γ:OrderParameter) (t:Ioo (0:ℝ) 1)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) (hc:ContinuousWithinAt γ.coeff (Ico (0:ℝ) 1) s) :
    Tendsto (fun n ↦ profileCoeff (γ.splitGrid t n) s) atTop (𝓝 (γ.coeff s)) := by
  choose r hr he hrs hdist using fun n ↦ γ.splitGrid_sample t n ⟨hs.1,hs.2.le⟩
  have hd:Tendsto (fun n ↦ dist (r n) s) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (hrs n))]
    exact hdist n
  have hl:=hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨(tendsto_iff_dist_tendsto_zero).mpr hd,Eventually.of_forall hr⟩)
  have hh:=hl.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hh' : Tendsto (fun n ↦ γ.coeff (r n)+(gridDelta n:ℝ)) atTop (𝓝 (γ.coeff s)) := by
    change Tendsto (fun n ↦ γ.coeff (r n)+1/(n+1:ℝ)) atTop (𝓝 (γ.coeff s))
    simpa only [Function.comp_apply,add_zero] using hh
  exact hh'.congr (fun n ↦ (he n).symm)
noncomputable def OrderParameter.splitError (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ :=
  ∫ s in (0:ℝ)..1,|profileCoeff (γ.splitGrid t n) s-γ.cutoff s|
lemma OrderParameter.splitError_nonneg (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    0≤γ.splitError t n := intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
lemma OrderParameter.splitError_tendsto (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
    Tendsto (γ.splitError t) atTop (𝓝 0) := by
  have hdom:∀ n,∀ᵐ s ∂volume,s∈uIoc (0:ℝ) 1 →
      ‖|profileCoeff (γ.splitGrid t n) s-γ.cutoff s|‖≤γ.cutoff s+1 := by
    intro n
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with s hne hs
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hs
    have hs':s∈Ico (0:ℝ) 1 := ⟨hs.1.le,lt_of_le_of_ne hs.2 hne⟩
    have hlo:=profileCoeff_nonneg (γ.splitGrid t n) s
    have hup:=γ.splitGrid_le t n hs'
    have hg:=γ.nonneg s hs'
    rw [Real.norm_eq_abs,abs_abs,OrderParameter.cutoff,indicator_of_mem hs']
    apply abs_le.mpr
    constructor <;> linarith [gridDelta_le_one n]
  have hl:=intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a:=0) (b:=1) (μ:=volume) (l:=atTop) (f:=fun _ : ℝ ↦ (0:ℝ))
    (F:=fun n s ↦ |profileCoeff (γ.splitGrid t n) s-γ.cutoff s|) (fun s ↦ γ.cutoff s+1)
    (Eventually.of_forall (fun n ↦ ((profileCoeff_measurable _).sub γ.cutoff_measurable).abs.aestronglyMeasurable))
    (Eventually.of_forall hdom)
    (γ.cutoff_integrable.intervalIntegrable.add (intervalIntegrable_const)) (by
      filter_upwards [γ.monotone.countable_not_continuousWithinAt.ae_notMem volume,Measure.ae_ne volume (1:ℝ)] with s hc hne hs
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hs
      have hs':s∈Ico (0:ℝ) 1 := ⟨hs.1.le,lt_of_le_of_ne hs.2 hne⟩
      have hc':ContinuousWithinAt γ.coeff (Ico (0:ℝ) 1) s := by
        by_contra hh;exact hc ⟨hs',hh⟩
      have he:=((γ.splitGrid_tendsto t hs' hc').sub_const (γ.coeff s)).abs
      simpa only [OrderParameter.cutoff,indicator_of_mem hs',sub_self,abs_zero] using he)
  change Tendsto (fun n ↦ ∫ s in (0:ℝ)..1,|profileCoeff (γ.splitGrid t n) s-γ.cutoff s|) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using hl
lemma OrderParameter.split_shift_error (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    (∫ r in (0:ℝ)..(1-s),|profileCoeff (γ.splitGrid t n) (s+r)-γ.cutoff (s+r)|)≤γ.splitError t n := by
  have hg:IntervalIntegrable (profileCoeff (γ.splitGrid t n)) volume 0 1 := by
    simpa only [γ.splitGrid_time] using profileCoeff_integrable (γ.splitGrid t n)
  have hi:IntervalIntegrable (fun r ↦ |profileCoeff (γ.splitGrid t n) r-γ.cutoff r|) volume 0 1 :=
    (hg.sub γ.cutoff_integrable.intervalIntegrable).abs
  have he:(∫ r in (0:ℝ)..(1-s),|profileCoeff (γ.splitGrid t n) (s+r)-γ.cutoff (s+r)|)=
      ∫ r in s..1,|profileCoeff (γ.splitGrid t n) r-γ.cutoff r| := by
    simpa only [add_zero,add_sub_cancel] using intervalIntegral.integral_comp_add_left
      (f:=fun r ↦ |profileCoeff (γ.splitGrid t n) r-γ.cutoff r|) (a:=0) (b:=1-s) s
  rw [he]
  exact intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hi
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
noncomputable def profileHeight : HeatProfile → ℝ
  | [] => 0
  | p::l => max (p.2:ℝ) (profileHeight l)
lemma profileHeight_nonneg (l:HeatProfile) : 0 ≤ profileHeight l := by
  cases l with
  | nil => exact le_rfl
  | cons p l => exact p.2.coe_nonneg.trans (le_max_left _ _)
lemma profileHeight_mem {l:HeatProfile} {p:ℝ≥0 × ℝ≥0} (hp:p∈l) : (p.2:ℝ) ≤ profileHeight l := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_max_left _ _
    · exact (ih hp).trans (le_max_right _ _)
noncomputable def splitSmoothParameter (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ :=
  n+1+profileHeight (γ.splitGrid t n)
lemma splitSmoothParameter_pos (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    0<splitSmoothParameter γ t n := add_pos_of_pos_of_nonneg (by positivity) (profileHeight_nonneg _)
lemma splitSmoothParameter_ge (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    n+1 ≤ splitSmoothParameter γ t n := le_add_of_nonneg_right (profileHeight_nonneg _)
noncomputable def splitSmooth (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) : ℝ → ℝ → ℝ :=
  profileValue (logCoshTerminal (splitSmoothParameter γ t n)) (γ.splitGrid t n)
lemma splitSmooth_evolution (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothEvolution 1 (profileCoeff (γ.splitGrid t n)) (splitSmooth γ t n) := by
  unfold splitSmooth
  convert (logCoshTerminal_smoothTerminal (splitSmoothParameter_pos γ t n)).profile_evolution (γ.splitGrid t n) using 1
  exact (γ.splitGrid_time t n).symm
lemma splitSmooth_value_bound (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) (x:ℝ) :
    |splitSmooth γ t n s x-phi W γ s x| ≤ Real.log 2/(n+1:ℝ)+(3/2:ℝ)*γ.splitError t n := by
  have hZ:=brownian_increment_memLp W s
  have hψ:=logCoshTerminal_smoothTerminal (splitSmoothParameter_pos γ t n)
  have hm:Measurable (fun r:ℝ ↦ profileCoeff (γ.splitGrid t n) (s+r)) :=
    (profileCoeff_measurable _).comp (measurable_const.add measurable_id)
  have hi:IntervalIntegrable (fun r ↦ profileCoeff (γ.splitGrid t n) (s+r)) volume 0 (1-s) := by
    have hij:IntervalIntegrable (profileCoeff (γ.splitGrid t n)) volume s 1 := by
      apply (profileCoeff_integrable _).mono_set
      rw [γ.splitGrid_time,uIcc_of_le hs.2.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc hs.1 le_rfl
    simpa only [sub_self] using hij.comp_add_left s
  have hic:IntervalIntegrable (fun r ↦ γ.cutoff (s+r)) volume 0 (1-s) := by
    simpa only [sub_self] using (γ.cutoff_integrable.intervalIntegrable (a:=s) (b:=1)).comp_add_left s
  have herror:∀ x,abs (logCoshTerminal (splitSmoothParameter γ t n) x-abs x) ≤ Real.log 2/(n+1:ℝ) := by
    intro x
    exact (logCoshTerminal_uniform_error (splitSmoothParameter_pos γ t n) x).trans
      (div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by positivity) (splitSmoothParameter_ge γ t n))
  have he:=elapsedValue_difference_bound (f:=shiftedFiltration W s) hZ hψ.lipschitz
    (by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub a b)
    herror hm (γ.cutoff_measurable.comp (measurable_const.add measurable_id)) hi hic (sub_nonneg.mpr hs.2.le) (x:=x)
  dsimp only [Function.comp_def,Pi.add_apply,id_eq] at he
  rw [hψ.profile_elapsedValue W (γ.splitGrid_mono t n) (γ.splitGrid_time t n) hs x,
    ←phi_eq_elapsedValue W γ ⟨hs.1,hs.2.le⟩ x] at he
  change |splitSmooth γ t n s x-phi W γ s x| ≤ _ at he
  linarith [γ.split_shift_error t n ⟨hs.1,hs.2.le⟩]
lemma splitSmooth_tendsto (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
    TendstoUniformly (fun n (p:Ico (0:ℝ) 1×ℝ) ↦ splitSmooth γ t n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := by
  have hl:Tendsto (fun n:ℕ ↦ Real.log 2/(n+1:ℝ)+(3/2:ℝ)*γ.splitError t n) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero,add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log 2)).add ((γ.splitError_tendsto t).const_mul (3/2:ℝ))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn p
  rw [Real.dist_eq,abs_sub_comm]
  exact (splitSmooth_value_bound W γ t n p.1.property p.2).trans_lt hn
lemma splitSmooth_bulk_jets (γ:OrderParameter) (t:Ioo (0:ℝ) 1) {S:ℝ}
    (hS:S∈Ico (0:ℝ) 1) (m:ℕ) :
    ∃ C:ℝ,0 ≤ C ∧ ∀ n s,s∈Icc (0:ℝ) S → ∀ k ≤ m,∀ x,
      |iteratedDeriv k (deriv (splitSmooth γ t n s)) x| ≤ C := by
  let T:=(S+1)/2
  have hST:S<T := by dsimp only [T];linarith [hS.2]
  have hT1:T<1 := by dsimp only [T];linarith [hS.2]
  have hT:T∈Ico (0:ℝ) 1 := ⟨hS.1.trans hST.le,hT1⟩
  obtain ⟨C,hC,hb⟩:=uniform_bulk_jets (γ.coeff T+1) (by linarith [γ.nonneg _ hT]) T m S hS.1 hST
  refine ⟨C,hC,?_⟩
  intro n s hs k hk x
  exact hb (profileCoeff (γ.splitGrid t n)) (splitSmooth γ t n)
    ((splitSmooth_evolution γ t n).restrict hT1.le) (profileCoeff_measurable _)
    ((profileCoeff_mono (γ.splitGrid_mono t n)).mono (by rw [γ.splitGrid_time];exact Icc_subset_Icc le_rfl hT1.le))
    (fun r hr ↦ by
      rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
      exact (γ.splitGrid_le t n ⟨hr.1,hr.2.trans_lt hT1⟩).trans
        (add_le_add (γ.monotone ⟨hr.1,hr.2.trans_lt hT1⟩ hT hr.2) (gridDelta_le_one n))) s hs k hk x
lemma splitSmooth_jet_limits (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) {S:ℝ}
    (hS:S∈Ico (0:ℝ) 1) (k:ℕ) :
    TendstoUniformly (fun n (p:Icc (0:ℝ) S×ℝ) ↦ iteratedDeriv k (splitSmooth γ t n p.1) p.2)
      (fun p ↦ iteratedDeriv k (phi W γ p.1) p.2) atTop := by
  let f:Icc (0:ℝ) S×ℝ → Ico (0:ℝ) 1×ℝ := fun p ↦ (⟨p.1,⟨p.1.property.1,p.1.property.2.trans_lt hS.2⟩⟩,p.2)
  have hl:= (splitSmooth_tendsto W γ t).comp f
  have hs (n:ℕ) (s:Icc (0:ℝ) S):ContDiff ℝ ∞ (splitSmooth γ t n s) :=
    ((splitSmooth_evolution γ t n).slices s ⟨s.property.1,s.property.2.trans hS.2.le⟩).smooth
  have hb (j:ℕ):∃ C:ℝ,0 ≤ C ∧ ∀ (n:ℕ) (s:Icc (0:ℝ) S) x,|iteratedDeriv (j+1) (splitSmooth γ t n s) x| ≤ C := by
    obtain ⟨C,hC,hb⟩:=splitSmooth_bulk_jets γ t hS j
    refine ⟨C,hC,fun n s x ↦ ?_⟩
    simpa only [iteratedDeriv_succ'] using hb n s s.property j le_rfl x
  have hl' : TendstoUniformly (fun n (p:Icc (0:ℝ) S×ℝ) ↦ splitSmooth γ t n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := hl
  exact (uniform_all_derivative_limits (f:=fun (s:Icc (0:ℝ) S) x ↦ phi W γ s x) hl' hs hb).1 k
end SKValue

end

end OAI
