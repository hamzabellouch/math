import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RandomRestrictionKernel

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions

lemma lintegral_finite_stop_guard (W : Measure GDriver)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    (M : GDriver→Measure UpperPlane) (A : Set GDriver) (f : UpperPlane→ℝ≥0∞) :
    (∫⁻b in A,∫⁻z,f z∂(if S b=∞ then 0 else M b)∂W)=
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂M b∂W := by
  have hfinite : MeasurableSet {b | S b≠∞} :=
    (hS.measurable' (measurableSet_singleton ∞)).compl
  rw [inter_comm A {b | S b≠∞},←Measure.restrict_restrict hfinite,←lintegral_indicator hfinite]
  apply lintegral_congr
  intro b
  by_cases hb : S b=∞ <;> simp [hb]

 

theorem recoveredPostStop_potential (a : ℝ) (ha : 1/4<a)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass a ha s c hc v b)))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {t : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[(afterStopFiltration hS) t] A)
    {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    let ν := recoveredPostStop a ha s c hc S
    (∫⁻b in A,∫⁻z,f z∂ν ∞ b∂W)=
      (∫⁻b in A,∫⁻z,f z∂ν t b∂W)+
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂(survivingKernel a ha ((S b).toNNReal+t) b).restrict
        {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}∂W := by
  intro ν
  let := hW.isGaussianProcess.isProbabilityMeasure
  let μ := recoveredMass a ha s c hc
  let T := shiftStop S t
  have hT := shiftStop_isStoppingTime hS t
  let R := stoppedSurvivingKernel a ha T hT
  have hcond (H : GDriver×UpperPlane→ℝ≥0∞)
      (hH : Measurable[hT.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H) :
      (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂W)=(∫⁻b,∫⁻z,H (b,z)∂μ (T b) b∂W)+
        ∫⁻b,∫⁻z,H (b,z)∂ R b∂W := by
    have hi := (recoveredMass_all_stopping a ha W hW s c hc hs hsum hconv T hT).2.2.2.2 H hH
    have hn : Measurable H := hH.mono (prod_sigma_le hT.measurableSpace_le _) le_rfl
    have he (b : GDriver) : (∫⁻z,H (b,z)∂ R b)=
        ∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (T b) b z.1)∂upperArea := by
      rw [stoppedSurvivingKernel_apply]
      exact (lintegral_withDensity_eq_lintegral_mul upperArea
        (stoppedSurvivingGreen_spatial_measurable a ha T hT b).ennreal_ofReal
        (hn.comp (measurable_const.prodMk measurable_id))).trans
        (lintegral_congr fun _ => mul_comm _ _)
    simpa only [he,μ] using hi
  let D : GDriver→Set UpperPlane := fun b => {z | alive a b.1 (S b).toNNReal z.1}
  have hD : MeasurableSet[hT.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)]
      {p : GDriver×UpperPlane | p.2∈D p.1} :=
    (prod_sigma_le (measurableSpace_le_shiftStop hS t) _) _ (measurableSet_alive_atStop_raw a ha hS)
  have hB : MeasurableSet[hT.measurableSpace] (A∩{b | S b≠∞}) :=
    hA.inter ((measurableSpace_le_shiftStop hS t) _ (hS.measurable (measurableSet_singleton ∞)).compl)
  have h := conditional_random_restrict_on hT.measurableSpace_le W (μ ∞)
    (fun b => μ (T b) b) R hcond D hD hB hf
  have he (v : ℝ≥0∞) : (∫⁻b in A,∫⁻z,f z∂ν v b∂W)=
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂(μ (S b+v) b).restrict (D b)∂W :=
    lintegral_finite_stop_guard W hS _ A f
  rw [he,he]
  simp only [add_top] 
  refine h.trans (congrArg (fun x => (∫⁻b in A∩{b | S b≠∞},
    ∫⁻z,f z∂(μ (T b) b).restrict (D b)∂W)+x) ?_)
  apply setLIntegral_congr_fun (hT.measurableSpace_le _ hB)
  intro b hb
  have hbt : T b≠∞ := ENNReal.add_ne_top.mpr ⟨hb.2,ENNReal.coe_ne_top⟩
  have heR : R b=survivingKernel a ha ((S b).toNNReal+t) b := by
    rw [stoppedSurvivingKernel_apply,survivingKernel_apply]
    congr 1
    funext z
    simp only [stoppedSurvivingGreen,T,shiftStop,ite_eq_right (show S b+(t:ℝ≥0∞)≠∞ from hbt),
      ENNReal.toNNReal_add hb.2 ENNReal.coe_ne_top,ENNReal.toNNReal_coe]
  change (∫⁻z,f z∂(R b).restrict (D b))=_
  rw [heR]

 
theorem recoveredRestart_potential (a : ℝ) (ha : 1/4<a)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass a ha s c hc v b)))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {t : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[(afterStopFiltration hS) t] A)
    {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    let ν := recoveredRestart a ha s c hc S
    (∫⁻b in A,∫⁻z,f z∂ν ∞ b∂W)=
      (∫⁻b in A,∫⁻z,f z∂ν t b∂W)+
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂(survivingKernel a ha ((S b).toNNReal+t) b).restrict
        {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}∂W := by
  intro ν
  have he (v : ℝ≥0∞) : (∫⁻b in A,∫⁻z,f z∂ν v b∂W)=
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha)
        b (S b).toNNReal (recoveredMass a ha s c hc v (restartAt S b))∂W :=
    lintegral_finite_stop_guard W hS _ A f
  rw [he,he]
  exact recoveredMass_restarted_potential a ha W hW s c hc hs hsum hconv hS hA hf

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology CompactlySupported
namespace SLEExactGauge.MassVersions
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

lemma measure_eq_of_determiningTests (μ ν : Measure X)
    [μ.Regular] [ν.Regular]
    (he : ∀ i, (∫x, determiningTests i x ∂μ) = ∫x, determiningTests i x ∂ν) :
    μ=ν := by
  let L : ℕ → (C_c(X,ℝ) →ₚ[ℝ] ℝ) := fun n =>
    if n%2=0 then CompactlySupportedContinuousMap.integralPositiveLinearMap μ
      else CompactlySupportedContinuousMap.integralPositiveLinearMap ν
  have hc : TestConverges L := by
    intro i
    refine ⟨∫x, determiningTests i x ∂μ,?_⟩
    have hh (n : ℕ) : L n (determiningTests i) = ∫x, determiningTests i x ∂μ := by
      dsimp only [L]
      split_ifs
      · rfl
      · exact (he i).symm
    simpa only [hh] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => ∫x, determiningTests i x ∂μ) atTop (𝓝 (∫x, determiningTests i x ∂μ)))
  have hmul : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hadd : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hmul
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have heven := (tendsto_radonLimit L hc f).comp hmul
  have hodd := (tendsto_radonLimit L hc f).comp hadd
  have hem (n : ℕ) : L (2*n) f=∫x,f x∂μ := by simp [L]
  have hov (n : ℕ) : L (2*n+1) f=∫x,f x∂ν := by simp [L]
  simp only [Function.comp_def,hem] at heven
  simp only [Function.comp_def,hov] at hodd
  exact (tendsto_nhds_unique tendsto_const_nhds heven).trans
    (tendsto_nhds_unique tendsto_const_nhds hodd).symm

 
theorem ae_all_measure_eq_of_test_eq {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ ν : I → Ω → Measure X)
    [∀ t ω, (μ t ω).Regular] [∀ t ω, (ν t ω).Regular]
    (he : ∀ i, ∀ᵐ ω ∂P, ∀ t, (∫x,determiningTests i x∂μ t ω) =
      ∫x,determiningTests i x∂ν t ω) :
    ∀ᵐ ω ∂P, ∀ t, μ t ω=ν t ω := by
  filter_upwards [ae_all_iff.mpr he] with ω hω t
  exact measure_eq_of_determiningTests _ _ (fun i => hω i t)

 
def positiveTest (f : C_c(X,ℝ)) : C_c(X,ℝ) :=
  ⟨⟨fun x => max (f x) 0, f.continuous.max continuous_const⟩,
    f.hasCompactSupport.sup (.zero)⟩

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
lemma positiveTest_nonneg [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (f : C_c(X,ℝ)) (x : X) : 0≤positiveTest f x :=
  le_max_right _ _

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
lemma positiveTest_sub [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (f : C_c(X,ℝ)) (x : X) :
    positiveTest f x-positiveTest (-f) x=f x := by
  change max (f x) 0-max (-(f x)) 0=f x
  exact posPart_sub_negPart (f x)

lemma integral_positiveTest_sub (f : C_c(X,ℝ)) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] :
    (∫x,positiveTest f x∂μ)-(∫x,positiveTest (-f) x∂μ)=∫x,f x∂μ := by
  rw [← integral_sub (positiveTest f).integrable (positiveTest (-f)).integrable]
  simp only [positiveTest_sub]

end SLEExactGauge.MassVersions
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.MeshEnergy

 
def grid (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := T * i / ((n:ℝ≥0)+1)

@[simp] lemma grid_zero (T : ℝ≥0) (n : ℕ) : grid T n 0=0 := by simp [grid]

@[simp] lemma grid_last (T : ℝ≥0) (n : ℕ) : grid T n (n+1)=T := by
  have h : (n:ℝ≥0)+1≠0 := ne_of_gt (by positivity)
  simp [grid,Nat.cast_add,Nat.cast_one,h]

lemma grid_mono (T : ℝ≥0) (n : ℕ) : Monotone (grid T n) := by
  intro i j hij
  dsimp [grid]
  gcongr

lemma grid_mem (T : ℝ≥0) (n i : ℕ) (hi : i≤n+1) : grid T n i∈Icc 0 T :=
  ⟨zero_le, (grid_mono T n hi).trans_eq (grid_last T n)⟩

lemma dist_grid_succ (T : ℝ≥0) (n i : ℕ) :
    dist (grid T n (i+1)) (grid T n i) = (T:ℝ)/((n:ℝ)+1) := by
  rw [NNReal.dist_eq]
  simp only [grid,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,
    NNReal.coe_one,Nat.cast_add,Nat.cast_one]
  have he : (T:ℝ)*((i:ℝ)+1)/((n:ℝ)+1)-T*i/((n:ℝ)+1)=T/((n:ℝ)+1) := by ring
  rw [he,abs_of_nonneg (by positivity)]

lemma tendsto_mesh (T : ℝ≥0) :
    Tendsto (fun n : ℕ => (T:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)))

 
def energy (M : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (M (grid T n (i+1))-M (grid T n i))^2

lemma energy_nonneg (M : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : 0≤energy M T n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

 
lemma energy_le (M C : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hcontrol : ∀ s t, s≤t → t≤T → |M t-M s|≤C t-C s) (n : ℕ) :
    energy M T n ≤ (C T-C 0)^2 := by
  let A : ℕ → ℝ := fun i => C (grid T n (i+1))-C (grid T n i)
  have ha (i : ℕ) (hi : i∈Finset.range (n+1)) :
      |M (grid T n (i+1))-M (grid T n i)|≤A i :=
    hcontrol _ _ (grid_mono T n (Nat.le_succ _))
      (grid_mem T n (i+1) (by simpa using Finset.mem_range.mp hi)).2
  have han (i : ℕ) (hi : i∈Finset.range (n+1)) : 0≤A i :=
    (abs_nonneg _).trans (ha i hi)
  calc
    energy M T n ≤ ∑ i ∈ Finset.range (n+1), (A i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = |M (grid T n (i+1))-M (grid T n i)|^2 := (sq_abs _).symm
        _ ≤ (A i)^2 := (sq_le_sq₀ (abs_nonneg _) (han i hi)).mpr (ha i hi)
    _ ≤ (∑ i ∈ Finset.range (n+1), A i)^2 := Finset.sum_sq_le_sq_sum_of_nonneg han
    _ = (C T-C 0)^2 := by
      rw [show (∑ i ∈ Finset.range (n+1), A i)=C (grid T n (n+1))-C (grid T n 0) from
        Finset.sum_range_sub (fun i => C (grid T n i)) (n+1)]
      simp

 
theorem tendsto_energy_zero (M C : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hc : ContinuousOn C (Icc 0 T))
    (hcontrol : ∀ s t, s≤t → t≤T → |M t-M s|≤C t-C s) :
    Tendsto (energy M T) atTop (𝓝 0) := by
  let V := C T-C 0
  have hv : 0≤V := (abs_nonneg _).trans (hcontrol 0 T (zero_le) le_rfl)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hη : 0<ε/(V+1) := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/(V+1)) hη
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_mesh T).eventually (gt_mem_nhds hδ))
  refine ⟨N,fun n hn => ?_⟩
  let A : ℕ → ℝ := fun i => C (grid T n (i+1))-C (grid T n i)
  have ha (i : ℕ) (hi : i∈Finset.range (n+1)) :
      |M (grid T n (i+1))-M (grid T n i)|≤A i :=
    hcontrol _ _ (grid_mono T n (Nat.le_succ _))
      (grid_mem T n (i+1) (by simpa using Finset.mem_range.mp hi)).2
  have hb (i : ℕ) (hi : i∈Finset.range (n+1)) : A i<ε/(V+1) := by
    have hi' : i<n+1 := Finset.mem_range.mp hi
    have h := hd _ (grid_mem T n (i+1) hi') _ (grid_mem T n i hi'.le)
      (by rw [dist_grid_succ]; exact hN n hn)
    exact (le_abs_self (A i)).trans_lt h
  have he : energy M T n≤ε/(V+1)*V := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1), (ε/(V+1))* A i := by
        apply Finset.sum_le_sum
        intro i hi
        have h0 : 0≤A i := (abs_nonneg _).trans (ha i hi)
        calc
          _ = |M (grid T n (i+1))-M (grid T n i)|^2 := (sq_abs _).symm
          _ ≤ (A i)^2 := (sq_le_sq₀ (abs_nonneg _) h0).mpr (ha i hi)
          _ ≤ ε/(V+1)*A i := by rw [pow_two]; exact mul_le_mul_of_nonneg_right (hb i hi).le h0
      _ = _ := by
        rw [← Finset.mul_sum, show (∑ i ∈ Finset.range (n+1), A i)=
          C (grid T n (n+1))-C (grid T n 0) from
            Finset.sum_range_sub (fun i => C (grid T n i)) (n+1)]
        simp [V]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (energy_nonneg _ _ _)]
  refine he.trans_lt ?_
  apply (div_mul_eq_mul_div _ _ _).trans_lt
  exact (div_lt_iff₀ (by linarith : 0<V+1)).mpr (by nlinarith)

end SLEExactGauge.MeshEnergy
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.TaylorVariation
open MeshEnergy

 
lemma remainder_le_sq (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    {K : ℝ≥0} (hg : LipschitzWith K g) (x y : ℝ) :
    |f y - f x - g x * (y-x)| ≤ (K:ℝ) * (y-x)^2 := by
  have h := (convex_uIcc (𝕜 := ℝ) x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z-g x*z) (f' := fun z => g z-g x)
    (C := (K:ℝ)*|y-x|)
    (fun z _ => (by
      convert! ((hd z).sub ((hasDerivAt_id z).const_mul (g x))).hasDerivWithinAt using 1
      simp))
    (fun z hz => (hg.norm_sub_le z x).trans (mul_le_mul_of_nonneg_left
      (norm_sub_le_of_mem_segment (by simpa [segment_eq_uIcc] using hz)) K.2))
    left_mem_uIcc right_mem_uIcc
  have he : f y-g x*y-(f x-g x*x)=f y-f x-g x*(y-x) := by ring
  calc
    _ ≤ (K:ℝ) * |y-x| * |y-x| := by simpa only [Real.norm_eq_abs,he] using h
    _ = _ := by rw [mul_assoc, ← pow_two, sq_abs]

lemma lipschitz_of_deriv_bound (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    {L : ℝ≥0} (hg : ∀ x, |g x|≤L) : LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
  intro x
  change |deriv f x|≤(L:ℝ)
  rw [(hd x).deriv]
  exact hg x

lemma remainder_le_abs (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    {L : ℝ≥0} (hg : ∀ x, |g x|≤L) (x y : ℝ) :
    |f y-f x-g x*(y-x)|≤(2*(L:ℝ))*|y-x| := by
  have hf := (lipschitz_of_deriv_bound f g hd hg).norm_sub_le y x
  calc
    _ ≤ |f y-f x|+|g x*(y-x)| := abs_sub _ _
    _ ≤ L*|y-x|+L*|y-x| := by
      rw [abs_mul]
      exact add_le_add hf (mul_le_mul_of_nonneg_right (hg x) (abs_nonneg _))
    _ = _ := by ring

 
def error (f g : ℝ → ℝ) (M : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  f (M T)-f (M 0) - ∑ i ∈ Finset.range (n+1),
    g (M (grid T n i)) * (M (grid T n (i+1))-M (grid T n i))

lemma error_eq_sum (f g : ℝ → ℝ) (M : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    error f g M T n = ∑ i ∈ Finset.range (n+1),
      (f (M (grid T n (i+1)))-f (M (grid T n i)) -
        g (M (grid T n i)) * (M (grid T n (i+1))-M (grid T n i))) := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => f (M (grid T n i))) (n+1)]
  simp [error]

lemma abs_error_le_energy (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    {K : ℝ≥0} (hg : LipschitzWith K g) (M : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    |error f g M T n|≤(K:ℝ)*energy M T n := by
  rw [error_eq_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), |f (M (grid T n (i+1)))-f (M (grid T n i)) -
        g (M (grid T n i)) * (M (grid T n (i+1))-M (grid T n i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (K:ℝ) * (M (grid T n (i+1))-M (grid T n i))^2 :=
      Finset.sum_le_sum (fun i _ => remainder_le_sq f g hd hg _ _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

lemma abs_error_le_variation (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    {L : ℝ≥0} (hg : ∀ x, |g x|≤L) (M C : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hcontrol : ∀ s t, s≤t → t≤T → |M t-M s|≤C t-C s) (n : ℕ) :
    |error f g M T n|≤(2*(L:ℝ))*(C T-C 0) := by
  rw [error_eq_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), |f (M (grid T n (i+1)))-f (M (grid T n i)) -
        g (M (grid T n i)) * (M (grid T n (i+1))-M (grid T n i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (2*(L:ℝ)) * (C (grid T n (i+1))-C (grid T n i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (remainder_le_abs f g hd hg _ _).trans (mul_le_mul_of_nonneg_left
        (hcontrol _ _ (grid_mono T n (Nat.le_succ _))
          (grid_mem T n (i+1) (by simpa using Finset.mem_range.mp hi)).2) (by positivity))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => C (grid T n i)) (n+1)]
      simp

lemma tendsto_error_zero (f g : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (g x) x)
    {K : ℝ≥0} (hg : LipschitzWith K g) (M C : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hc : ContinuousOn C (Icc 0 T))
    (hcontrol : ∀ s t, s≤t → t≤T → |M t-M s|≤C t-C s) :
    Tendsto (error f g M T) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => (K:ℝ)*energy M T n) atTop (𝓝 0) by
      simpa using (tendsto_energy_zero M C T hc hcontrol).const_mul (K:ℝ))
  exact abs_error_le_energy f g hd hg M T n

 

def detector (x : ℝ) : ℝ := Real.sqrt (1+x^2)-1

def detectorDeriv (x : ℝ) : ℝ := x / Real.sqrt (1+x^2)

lemma one_le_root (x : ℝ) : 1≤Real.sqrt (1+x^2) :=
  Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg x])

lemma hasDerivAt_root (x : ℝ) : HasDerivAt (fun x : ℝ => Real.sqrt (1+x^2))
    (x/Real.sqrt (1+x^2)) x := by
  have h : 1+x^2≠0 := ne_of_gt (by positivity)
  convert! (((hasDerivAt_id x).pow 2).const_add 1).sqrt h using 1
  dsimp
  ring

lemma hasDerivAt_detector (x : ℝ) : HasDerivAt detector (detectorDeriv x) x :=
  (hasDerivAt_root x).sub_const 1

lemma hasDerivAt_detectorDeriv (x : ℝ) :
    HasDerivAt detectorDeriv (1/(Real.sqrt (1+x^2))^3) x := by
  have hp : 0<Real.sqrt (1+x^2) := lt_of_lt_of_le zero_lt_one (one_le_root x)
  have hs := Real.sq_sqrt (show 0≤1+x^2 by positivity)
  have hx : HasDerivAt detectorDeriv
      ((Real.sqrt (1+x^2)-x*(x/Real.sqrt (1+x^2)))/(Real.sqrt (1+x^2))^2) x := by
    convert! (hasDerivAt_id x).div (hasDerivAt_root x) (ne_of_gt hp) using 1
    simp
  convert! hx using 1
  field_simp
  nlinarith [hs]

lemma abs_detectorDeriv_le (x : ℝ) : |detectorDeriv x|≤1 := by
  have hp : 0<Real.sqrt (1+x^2) := lt_of_lt_of_le zero_lt_one (one_le_root x)
  have hs := Real.sq_sqrt (show 0≤1+x^2 by positivity)
  rw [detectorDeriv,abs_div,abs_of_pos hp,div_le_iff₀ hp,one_mul]
  nlinarith [sq_abs x,abs_nonneg x]

lemma lipschitz_detector : LipschitzWith 1 detector :=
  lipschitz_of_deriv_bound detector detectorDeriv hasDerivAt_detector abs_detectorDeriv_le

lemma lipschitz_detectorDeriv : LipschitzWith 1 detectorDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_detectorDeriv x).differentiableAt)
  intro x
  change |deriv detectorDeriv x|≤(1:ℝ)
  rw [(hasDerivAt_detectorDeriv x).deriv,abs_of_nonneg (by positivity)]
  have h := one_le_root x
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ h)

@[simp] lemma detector_zero : detector 0=0 := by simp [detector]

lemma detector_nonneg (x : ℝ) : 0≤detector x := sub_nonneg.mpr (one_le_root x)

@[simp] lemma detector_eq_zero_iff (x : ℝ) : detector x=0 ↔ x=0 := by
  constructor
  · intro h
    have hs := Real.sq_sqrt (show 0≤1+x^2 by positivity)
    have he : Real.sqrt (1+x^2)=1 := sub_eq_zero.mp h
    rw [he] at hs
    nlinarith [sq_nonneg x]
  · rintro rfl
    exact detector_zero

lemma abs_detector_le (x : ℝ) : |detector x|≤|x| := by
  simpa using lipschitz_detector.norm_sub_le x 0

end SLEExactGauge.TaylorVariation
end
end

end OAI
