import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusFlatMode
import OAI.Analysis.Conductivity.Sobolev.CollarLpPullback
import OAI.Analysis.Conductivity.Fourier.EndPoissonJets

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma lp_hasSum_ae_unique {X E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [Countable ι] [Infinite ι]
    {μ : Measure X} {p : ℝ≥0∞} [Fact (1≤p)]
    {u : Lp E p μ} {f : ι → Lp E p μ} {a : ι → X → E} {g : X → E}
    (hf : HasSum f u) (ha : ∀ i,f i=ᵐ[μ] a i)
    (hg : ∀ᵐ x∂μ,HasSum (fun i => a i x) (g x)) : u=ᵐ[μ] g := by
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α:=ℕ) (β:=ι)
  have ht := (e.hasSum_iff.mpr hf).tendsto_sum_nat
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hs : ∀ᵐ x∂μ,∀ n : ℕ,(∑ i∈Finset.range n,f (e i)) x=
      ∑ i∈Finset.range n,a (e i) x := by
    have hA : ∀ᵐ x∂μ,∀ i : ℕ,f (e i) x=a (e i) x := ae_all_iff.mpr (fun i => ha (e i))
    have hF : ∀ᵐ x∂μ,∀ n : ℕ,(∑ i∈Finset.range n,f (e i)) x=
        ∑ i∈Finset.range n,f (e i) x :=
      ae_all_iff.mpr (fun n => Lp.coeFn_fun_finsetSum (Finset.range n) (fun i => f (e i)))
    filter_upwards [hA,hF] with x hx hy n
    rw [hy]
    exact Finset.sum_congr rfl (fun i _ => hx i)
  filter_upwards [hg,hn,hs] with x hx hn hs
  have hpoint := ((e.hasSum_iff.mpr hx).tendsto_sum_nat).comp hns.tendsto_atTop
  have hco : (fun i => (∑ k∈Finset.range (ns i),f (e k)) x)=
      (fun i => ∑ k∈Finset.range (ns i),a (e k) x) := funext (fun i => hs (ns i))
  change Tendsto (fun i => (∑ k∈Finset.range (ns i),f (e k)) x) atTop (𝓝 (u x)) at hn
  rw [hco] at hn
  exact tendsto_nhds_unique hn hpoint

def endPoissonModeField (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (j : Fin 4)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  (Real.exp (-torusRate s h*z.1):ℂ)*endModeCoefficient s h a j*mFourier h z.2

def endPoissonField (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s)) (j : Fin 4)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  ∑' h,endPoissonModeField s h (f.val 0 h) j z

lemma endPoissonModeJet_ae (s : Fin 3 → ℝ) (R : ℝ) (h : TorusModes) (a : ℂ) (j : Fin 4) :
    endPoissonModeJet s R h a j=ᵐ[(FiniteAxisMeasure R).prod volume]
      endPoissonModeField s h a j := by
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := FiniteAxisMeasure R) (ν := (volume : Measure (UnitAddTorus (Fin 2))))).ae
    (finiteDecayLp_ae (torusRate s h) R (endModeCoefficient s h a j))
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := FiniteAxisMeasure R) (ν := (volume : Measure (UnitAddTorus (Fin 2))))).ae (coeFn_mFourierLp 2 h)
  filter_upwards [cylinderTensor_ae
    (finiteDecayLp (torusRate s h) R (endModeCoefficient s h a j)) (mFourierLp 2 h),h1,h2]
      with z hz h1 h2
  change cylinderTensor _ _ z=_
  rw [hz,h1,h2]
  rfl

lemma endModeCoefficient_norm_bound (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) (j : Fin 4) :
    ‖endModeCoefficient s h a j‖ ≤ (1+torusRate s h+torusSize h)*‖a‖ := by
  have hm : 0≤torusRate s h := Real.sqrt_nonneg _
  have hsize := torusSize_nonneg h
  fin_cases j
  · change ‖a‖≤_
    nlinarith [mul_nonneg hm (norm_nonneg a),mul_nonneg hsize (norm_nonneg a)]
  · change ‖-(torusRate s h:ℂ)*a‖≤_
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a)
  · change ‖Complex.I*(h 0:ℂ)*a‖≤_
    rw [norm_mul,norm_mul,Complex.norm_I,one_mul]
    have he : ‖(h 0:ℂ)‖=|(h 0:ℝ)| := by simp
    rw [he]
    have hh : |(h 0:ℝ)|≤torusSize h := le_add_of_nonneg_right (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a)
  · change ‖Complex.I*(h 1:ℂ)*a‖≤_
    rw [norm_mul,norm_mul,Complex.norm_I,one_mul]
    have he : ‖(h 1:ℂ)‖=|(h 1:ℝ)| := by simp
    rw [he]
    have hh : |(h 1:ℝ)|≤torusSize h := le_add_of_nonneg_left (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg a)

lemma endPoissonField_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4)
    {z : ℝ × UnitAddTorus (Fin 2)} (hz : 0<z.1) :
    HasSum (fun h => endPoissonModeField s h (f.val 0 h) j z) (endPoissonField s f j z) := by
  apply Summable.hasSum
  apply Summable.of_norm
  have hb : Summable (fun h => ‖f.val 0‖*((1+torusRate s h+torusSize h)*
      Real.exp (-z.1*torusRate s h))) := by
    have h0 := torusRate_exp_summable hs hz
    have h1 := flatMode_derivative_summable hs 1 hz
    simpa only [pow_one,add_mul,one_mul,add_assoc] using (h0.add h1).mul_left ‖f.val 0‖
  apply hb.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => ?_)
  have hc := endModeCoefficient_norm_bound s h (f.val 0 h) j
  have ha := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (f.val 0) h
  have hp : 0≤1+torusRate s h+torusSize h := by
    have hm : 0≤torusRate s h := Real.sqrt_nonneg _
    linarith [torusSize_nonneg h]
  have hc' := hc.trans (mul_le_mul_of_nonneg_left ha hp)
  have hm : ‖mFourier h z.2‖≤1 := by simpa only [mFourier_norm] using (mFourier h).norm_coe_le_norm z.2
  unfold endPoissonModeField
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-torusRate s h*z.1)*((1+torusRate s h+torusSize h)*‖f.val 0‖))*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc' (Real.exp_nonneg _)) hm (norm_nonneg _)
        (mul_nonneg (Real.exp_nonneg _) (mul_nonneg hp (norm_nonneg _)))
    _ = _ := by rw [show -torusRate s h*z.1= -z.1*torusRate s h by ring]; ring

theorem endPoissonJet_ae (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    endPoissonJet s hs R hR f j=ᵐ[(FiniteAxisMeasure R).prod volume] endPoissonField s f j := by
  apply lp_hasSum_ae_unique (endPoissonJet_component_hasSum s hs R hR f j)
    (fun h => endPoissonModeJet_ae s R h (f.val 0 h) j)
  have ht : ∀ᵐ t∂FiniteAxisMeasure R,0<t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z hz
  exact endPoissonField_hasSum s hs f j hz

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_endPoissonModeField (s : Fin 3 → ℝ) (h : TorusModes)
    (a : ℂ) (j : Fin 4) : Continuous (endPoissonModeField s h a j) := by
  unfold endPoissonModeField
  fun_prop

lemma measurable_endPoissonField (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4) : Measurable (endPoissonField s f j) := by
  exact Measurable.tsum (fun h => (continuous_endPoissonModeField s h (f.val 0 h) j).measurable)

def physicalEndPoissonField (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4) : (Fin 3 → ℝ) → ℂ :=
  endPoissonField s f j ∘ sourcePhysicalCoordinates

lemma measurable_physicalEndPoissonField (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4) : Measurable (physicalEndPoissonField s f j) :=
  (measurable_endPoissonField s f j).comp measurable_sourcePhysicalCoordinates

lemma physicalEndPoissonField_angular (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) (j : Fin 4) {t : ℝ}
    (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (θ : UnitAddTorus (Fin 2)) :
    physicalEndPoissonField s f j (sourceAngularCollar t θ)=endPoissonField s f j (t,θ) := by
  simp only [physicalEndPoissonField,Function.comp_apply,sourcePhysicalCoordinates_angular ht]

def physicalEndPoissonJet (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (hR' : R≤1/100) (f : spectralTraceGraph (torusRate s))
    (j : Fin 4) : Lp ℂ 2 (sourcePhysicalCollarMeasure 0 R) :=
  sourceCollarPullback hR (by norm_num) hR' (endPoissonJet s hs R hR f j)

lemma physicalEndPoissonJet_ae (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (hR' : R≤1/100) (f : spectralTraceGraph (torusRate s))
    (j : Fin 4) : physicalEndPoissonJet s hs R hR hR' f j=ᵐ[sourcePhysicalCollarMeasure 0 R]
      physicalEndPoissonField s f j :=
  sourceCollarPullback_ae_of_ae hR (by norm_num) hR' _ (endPoissonJet_ae s hs R hR f j)

lemma physicalEndPoissonField_memLp (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (hR' : R≤1/100) (f : spectralTraceGraph (torusRate s))
    (j : Fin 4) : MemLp (physicalEndPoissonField s f j) 2 (sourcePhysicalCollarMeasure 0 R) :=
  (memLp_congr_ae (physicalEndPoissonJet_ae s hs R hR hR' f j)).mp
    (Lp.memLp (physicalEndPoissonJet s hs R hR hR' f j))

lemma physicalEndPoissonJet_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0≤R) (hR' : R≤1/100) (f : spectralTraceGraph (torusRate s))
    (j : Fin 4) :
    HasSum (fun h => sourceCollarPullback hR (by norm_num) hR'
      (endPoissonModeJet s R h (f.val 0 h) j))
      (physicalEndPoissonJet s hs R hR hR' f j) :=
  sourceCollarPullback_hasSum hR (by norm_num) hR' (endPoissonJet_component_hasSum s hs R hR f j)

end ScalarConductivity

end

end OAI
