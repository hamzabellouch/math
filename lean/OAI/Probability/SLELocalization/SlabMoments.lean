import Mathlib
import OAI.Probability.SLELocalization.IntegratedMeshSimple
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Mesh estimates. -/

section
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge.Mesh

lemma asynchronous_bracket_bound_active {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) (hU : Continuous driver)
    {A : Set ℂ} (hA : MeasurableSet A) {a b : ℂ → ℝ} {D : ℂ → ℝ → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hB : Measurable (fun q : ℝ × ℂ => slab (D q.2) (a q.2) (b q.2) q.1))
    (L : ℂ → ℂ → ℝ≥0∞) (hL : Measurable (Function.uncurry L))
    (hLeq : ∀ z ∈ A, ∀ w ∈ A, L z w = laterGreen g a b z w)
    {K R C : ℝ} (hK : 0 ≤ K) (hR : 0 < R)
    (hstart : ∀ z ∈ A, 0 ≤ a z) (hab : ∀ z ∈ A, a z ≤ b z)
    (hlive : ∀ z ∈ A, z ∈ localizationDomain γ (b z))
    (happroach : ∀ z ∈ A, a z < b z → dist z (γ (a z)) ≤ R)
    (hcoeff : ∀ z ∈ A, ∀ t ∈ Icc (a z) (b z),
      |slab (D z) (a z) (b z) t| ≤ K*poissonFactor driver g t z)
    (hlayer : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ localizationDomain γ t,
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain γ t ∧ infDist w (localizationDomain γ t)ᶜ ≤ R},
        ENNReal.ofReal (halfPlaneGreen (g t z) (g t w))) ≤ ENNReal.ofReal (C*R^2)) :
    (∫⁻ t, ENNReal.ofReal (|∫ z in A, slab (D z) (a z) (b z) t|^2)) ≤
      2*ENNReal.ofReal (K^2)*ENNReal.ofReal (C*R^2)*volume A := by
  let A' := A ∩ {z | a z < b z}
  have hA' : MeasurableSet A' := hA.inter (measurableSet_lt ha hb)
  have hs : A' ⊆ A := inter_subset_left
  have he (t : ℝ) : (∫ z in A, slab (D z) (a z) (b z) t) =
      ∫ z in A', slab (D z) (a z) (b z) t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA hs
    intro z hz
    have hab' : a z = b z := le_antisymm (hab z hz.1) (not_lt.1 (fun hh => hz.2 ⟨hz.1,hh⟩))
    simp only [slab,hab',sub_self]
  simp only [he]
  apply (asynchronous_bracket_bound_with_kernel (B := fun t z => slab (D z) (a z) (b z) t) h hU hA' hB L hL
    (fun z hz w hw => hLeq z hz.1 w hw.1) hK hR
    (fun z hz => hstart z hz.1) (fun z hz => hab z hz.1)
    (fun z hz => hlive z hz.1) (fun z hz => happroach z hz.1 hz.2)
    (fun z hz t ht => slab_eq_zero_of_not_mem (hab z hz.1) ht)
    (fun z hz t ht => hcoeff z hz.1 t ht) hlayer).trans
  have hv : volume A' ≤ volume A := measure_mono hs
  exact mul_le_mul_right hv _

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized Mesh
local instance slabMomentsBracketRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance slabMomentsBracketRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance slabMomentsBracketComplexPathMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance slabMomentsBracketComplexPathBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

lemma measurable_halfPlaneGreen : Measurable (fun q : ℂ × ℂ => halfPlaneGreen q.1 q.2) := by
  unfold halfPlaneGreen
  fun_prop

lemma observed_bracket {Ω : Type*} {A : Set ℂ} {u : ℂ → ℝ}
    (C : FiniteTilt.CommonCutoff A u) (hA : MeasurableSet A)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 4) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (hhalf : ∀ z ∈ A, z ∈ halfPlane) (hu : ∀ z ∈ A, 0 < u z)
    {ρ : ℝ} (hr : ∀ z ∈ A, (2*z.im)*Real.exp (-u z) = ρ)
    (V : C(I,ℂ)) (hV : ∀ q : I, V q = γ ω ((C.horizon:ℝ)*q))
    (e r : ℝ) (he : 0 < e) (her : e ≤ r) (hes : ∀ z ∈ A, e < z.im)
    (J : ℝ) (hlayer : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ localizationDomain (γ ω) t,
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain (γ ω) t ∧ infDist w (localizationDomain (γ ω) t)ᶜ ≤ r},
        ENNReal.ofReal (halfPlaneGreen (g ω t z) (g ω t w))) ≤ ENNReal.ofReal (J*r^2)) :
    let U := BrownianDriver.path B (Real.sqrt κ) C.horizon ω
    let a := fun z => observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle r ((U,V),z)
    let b := fun z => observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle e ((U,V),z)
    let D := fun z t => iteratedDeriv 1
      (field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) (B t.toNNReal ω)
    (∫⁻ t, ENNReal.ofReal (|∫ z in A, slab (D z) (a z) (b z) t|^2)) ≤
      2*ENNReal.ofReal ((Real.sqrt κ*(8/κ-1)*(e/4)^(-(1-κ/8)))^2)*ENNReal.ofReal (J*r^2)*volume A := by
  intro U a b D
  have ham : Measurable a := by
    have hh := (measurable_observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle r).comp
      (measurable_const.prodMk measurable_id : Measurable (fun z : ℂ => ((U,V),z)))
    exact hh
  have hbm : Measurable b := by
    have hh := (measurable_observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle e).comp
      (measurable_const.prodMk measurable_id : Measurable (fun z : ℂ => ((U,V),z)))
    exact hh
  have hDc : Continuous (fun q : ℝ × ℂ => D q.2 q.1) := by
    have hp : Continuous (fun q : ℝ × ℂ => (((U,q.2),q.1),B q.1.toNNReal ω)) :=
      ((continuous_const.prodMk continuous_snd).prodMk continuous_fst).prodMk
        ((hc.comp continuous_real_toNNReal).comp continuous_fst)
    have hh := (continuous_mark_first C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ)).comp hp
    exact hh
  have hpos (z : ℂ) (hz : z ∈ A) (t : ℝ) (ht : t ∈ Icc 0 ((C.at z hz).stopTime κ B ω)) :
      g ω t z = position C.height_pos C.horizon.coe_nonneg U z t := by
    let Cz := C.at z hz
    have h0 := Cz.initial_deficit_brownian κ B ω (hhalf z hz) (hu z hz) hc hb0
    have hs := source_until_stop Cz.height_pos Cz.horizon_pos hm _ z _ Cz.angle (Cz.path_eq κ B ω hc) h0
    exact hs.2 ht
  have hat (z : ℂ) (hz : z ∈ A) : a z = (C.at z hz).physicalTime κ B γ r ω :=
    observedTime_eq C κ B γ g f ω hm hc hb0 z hz (hhalf z hz) (hu z hz) (hr z hz) V hV r
  have hbt (z : ℂ) (hz : z ∈ A) : b z = (C.at z hz).physicalTime κ B γ e ω :=
    observedTime_eq C κ B γ g f ω hm hc hb0 z hz (hhalf z hz) (hu z hz) (hr z hz) V hV e
  have hab (z : ℂ) : a z ≤ b z := observedTime_antitone C.height_pos C.horizon.coe_nonneg ρ C.angle ((U,V),z) her
  have ha0 (z : ℂ) : 0 ≤ a z := (observedTime_bounds C.height_pos C.horizon.coe_nonneg ρ C.angle r ((U,V),z)).1
  have hbz (z : ℂ) (hz : z ∈ A) : b z ≤ (C.at z hz).stopTime κ B ω := by
    rw [hbt z hz]; exact ((C.at z hz).physicalTime_bounds κ B γ e ω).2
  let L : ℂ → ℂ → ℝ≥0∞ := fun z w =>
    if a w ≤ a z ∧ a z ≤ b w then ENNReal.ofReal (halfPlaneGreen
      (position C.height_pos C.horizon.coe_nonneg U z (a z))
      (position C.height_pos C.horizon.coe_nonneg U w (a z))) else 0
  have hL : Measurable (Function.uncurry L) := by
    have h1 : Measurable (fun q : ℂ × ℂ => ((U,q.1),a q.1)) :=
      (measurable_const.prodMk measurable_fst).prodMk (ham.comp measurable_fst)
    have h2 : Measurable (fun q : ℂ × ℂ => ((U,q.2),a q.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk (ham.comp measurable_fst)
    have hp1 := (continuous_mark_position C.height_pos C.horizon.coe_nonneg).measurable.comp h1
    have hp2 := (continuous_mark_position C.height_pos C.horizon.coe_nonneg).measurable.comp h2
    have hh := (measurable_halfPlaneGreen.comp (hp1.prodMk hp2)).ennreal_ofReal
    exact hh.ite ((measurableSet_le (ham.comp measurable_snd) (ham.comp measurable_fst)).inter
      (measurableSet_le (ham.comp measurable_fst) (hbm.comp measurable_snd))) measurable_const
  have hLe (z : ℂ) (hz : z ∈ A) (w : ℂ) (hw : w ∈ A) : L z w = laterGreen (g ω) a b z w := by
    dsimp only [L,laterGreen]
    split_ifs with hh
    · rw [← hpos z hz (a z) ⟨ha0 z,(hab z).trans (hbz z hz)⟩,
        ← hpos w hw (a z) ⟨ha0 z,hh.2.trans (hbz w hw)⟩]
      rfl
    · rfl
  have haexp : 0 ≤ 8/κ-1 := by
    have hh : 1 ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by linarith [hκ.2])
    linarith
  have hKn : 0 ≤ Real.sqrt κ*(8/κ-1)*(e/4)^(-(1-κ/8)) := by positivity
  apply asynchronous_bracket_bound_active hm
    (continuous_const.mul (hc.comp continuous_real_toNNReal)) hA ham hbm
    (measurable_slab hDc.measurable ham hbm) L hL hLe hKn (he.trans_le her)
    (fun z _ => ha0 z) (fun z _ => hab z)
  · intro z hz
    exact survivingDomain_mono (hbz z hz) ((C.at z hz).source_live κ B ω hm (hhalf z hz) (hu z hz) hc hb0)
  · intro z hz hh
    exact observedTime_approach C.height_pos C.horizon_pos ρ C.angle e r U V (γ ω) hV z hh
  · intro z hz t ht
    have hti : t ∈ Icc 0 ((C.at z hz).physicalTime κ B γ e ω) := by
      rw [← hbt z hz]; exact ⟨(ha0 z).trans ht.1,ht.2⟩
    have hb := (C.at z hz).first_le_poisson κ hκ B γ g f ω hm hc hb0 (hhalf z hz) (hu z hz) he (hes z hz) hti
    have hl := survivingDomain_mono (hti.2.trans ((C.at z hz).physicalTime_bounds κ B γ e ω).2)
      ((C.at z hz).source_live κ B ω hm (hhalf z hz) (hu z hz) hc hb0)
    have hn : 0 ≤ poissonFactor (fun t => Real.sqrt κ*B t.toNNReal ω) (g ω) t z :=
      div_nonneg (hm.im_pos hti.1 hl).le (sq_nonneg _)
    exact slab_abs_le (hab z) (mul_nonneg hKn hn) hb
  · exact hlayer

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable

lemma gaussian_exp_compensated (v : ℝ≥0) (x a θ : ℝ) :
    (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (x+θ*a*y-θ^2*a^2*(v:ℝ)/2))
      ∂gaussianReal 0 v) = ENNReal.ofReal (Real.exp x) := by
  have he (y : ℝ) : Real.exp (x+θ*a*y-θ^2*a^2*(v:ℝ)/2) =
      Real.exp (x-θ^2*a^2*(v:ℝ)/2)*Real.exp ((θ*a)*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop),← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_gaussianReal (θ*a)) (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))]
  have hm := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) (θ*a)
  change (∫ y : ℝ, Real.exp ((θ*a)*y) ∂gaussianReal 0 v) = _ at hm
  rw [hm,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

lemma past_exp_step {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t)
    (X A : Ω → ℝ) (hX : Measurable[pastSigma B s] X)
    (hA : Measurable[pastSigma B s] A) (hXa : AEMeasurable X P)
    (hAa : AEMeasurable A P) (θ : ℝ) :
    (∫⁻ sample, ENNReal.ofReal (Real.exp (X sample+θ*A sample*(B t sample-B s sample)-
      θ^2*(A sample)^2*((t-s:ℝ≥0):ℝ)/2)) ∂P) =
      ∫⁻ sample, ENNReal.ofReal (Real.exp (X sample)) ∂P := by
  let V : Ω → ℝ × ℝ := fun sample => (X sample,A sample)
  have hVm : Measurable[pastSigma B s] V := hX.prodMk hA
  have hVa : AEMeasurable V P := hXa.prodMk hAa
  have hi := brownian_indep_of_past_measurable hB s (t-s) hVm
  rw [add_tsub_cancel_of_le hst] at hi
  have hl : HasLaw V (P.map V) P := ⟨hVa,rfl⟩
  have hprod := IndepFun.hasLaw_prod hl (increment_hasLaw hB hst) hi
  let F : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (Real.exp (q.1.1+θ*q.1.2*q.2-θ^2*q.1.2^2*((t-s:ℝ≥0):ℝ)/2))
  have hFm : Measurable F := by fun_prop
  have he := hprod.lintegral_comp hFm.aemeasurable
  change (∫⁻ sample, F (V sample,B t sample-B s sample) ∂P) = _ at he
  rw [he,lintegral_prod _ hFm.aemeasurable]
  simp only [F,gaussian_exp_compensated]
  have hmap := hl.lintegral_comp
    (show AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp q.1)) (P.map V) by fun_prop)
  exact hmap.symm

def exponentialLogSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (A : ℕ → Ω → ℝ) (θ : ℝ) (N : ℕ) (sample : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, (θ*A i sample*(B (t (i+1)) sample-B (t i) sample)-
    θ^2*(A i sample)^2*((t (i+1)-t i:ℝ≥0):ℝ)/2)

lemma exponentialLogSum_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[pastSigma B (t i)] (A i))
    (θ : ℝ) (N : ℕ) : Measurable[pastSigma B (t N)] (exponentialLogSum B t A θ N) := by
  apply Finset.measurable_fun_sum
  intro i hi
  have hAi := (hA i).mono (pastSigma_mono B (ht (Finset.mem_range.1 hi).le)) le_rfl
  have hBi := past_measurable_eval B (ht (Finset.mem_range.1 hi).le)
  have hBin := past_measurable_eval B (ht (Nat.succ_le_of_lt (Finset.mem_range.1 hi)))
  exact (((hAi.const_mul θ).mul (hBin.sub hBi)).sub
    (((hAi.pow_const 2).const_mul (θ^2)).mul_const _ |>.div_const 2))

lemma exponentialLogSum_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (A : ℕ → Ω → ℝ) (hA : ∀ i, AEMeasurable (A i) P)
    (θ : ℝ) (N : ℕ) : AEMeasurable (exponentialLogSum B t A θ N) P := by
  apply Finset.aemeasurable_fun_sum
  intro i hi
  have hBi := hB.toIsPreBrownianReal.aemeasurable (t i)
  have hBin := hB.toIsPreBrownianReal.aemeasurable (t (i+1))
  fun_prop

lemma exponentialLogSum_identity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (A : ℕ → Ω → ℝ) (hA : ∀ i, Measurable[pastSigma B (t i)] (A i))
    (hAa : ∀ i, AEMeasurable (A i) P) (θ : ℝ) (N : ℕ) :
    (∫⁻ sample, ENNReal.ofReal (Real.exp (exponentialLogSum B t A θ N sample)) ∂P) = 1 := by
  induction N with
  | zero => simp [exponentialLogSum]
  | succ N hN =>
    simp only [exponentialLogSum,Finset.sum_range_succ]
    change (∫⁻ sample, ENNReal.ofReal (Real.exp (exponentialLogSum B t A θ N sample+
      (θ*A N sample*(B (t (N+1)) sample-B (t N) sample)-
      θ^2*(A N sample)^2*((t (N+1)-t N:ℝ≥0):ℝ)/2))) ∂P) = 1
    simp_rw [← add_sub_assoc]
    rw [past_exp_step hB (ht (Nat.le_succ N)) _ _ (exponentialLogSum_past B t ht A hA θ N)
      (hA N) (exponentialLogSum_aemeasurable hB t A hAa θ N) (hAa N),hN]

end SLEExactGauge.BrownianPredictable

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable
open PredictableLimit

def dyadicVariance {Ω : Type*} (T : ℝ≥0) (A : ℕ → ℕ → Ω → ℝ) (n : ℕ) (sample : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), (A n i sample)^2 *
    ((dyadicTime T n (i+1)-dyadicTime T n i:ℝ≥0):ℝ)

lemma exponentialLogSum_dyadic {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (A : ℕ → ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (sample : Ω) :
    exponentialLogSum B (dyadicTime T n) (A n) θ (2^n) sample =
      θ*dyadicDriverSum B T A n sample - θ^2*dyadicVariance T A n sample/2 := by
  simp only [exponentialLogSum,dyadicDriverSum,dyadicVariance,Finset.mul_sum,
    Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem limit_exponential_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T : ℝ≥0) (A : ℕ → ℕ → Ω → ℝ)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (A n i))
    (hAa : ∀ n i, AEMeasurable (A n i) P)
    (Y Q : Ω → ℝ)
    (hY : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T A n sample) atTop (𝓝 (Y sample)))
    (hQ : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicVariance T A n sample) atTop (𝓝 (Q sample)))
    (K : ℝ) (hK : ∀ᵐ sample ∂P, Q sample ≤ K) (θ : ℝ) :
    (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample)) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*K/2)) := by
  let E : ℕ → Ω → ℝ≥0∞ := fun n sample => ENNReal.ofReal
    (Real.exp (exponentialLogSum B (dyadicTime T n) (A n) θ (2^n) sample))
  have hEm (n : ℕ) : AEMeasurable (E n) P :=
    ((exponentialLogSum_aemeasurable hB _ _ (hAa n) θ (2^n)).exp).ennreal_ofReal
  have hEi (n : ℕ) : (∫⁻ sample, E n sample ∂P) = 1 :=
    exponentialLogSum_identity hB _ (dyadicTime_mono T n) _ (hA n) (hAa n) θ (2^n)
  have hElim : ∀ᵐ sample ∂P, Tendsto (fun n => E n sample) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)))) := by
    filter_upwards [hY,hQ] with sample hy hq
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp
        ((hy.const_mul θ).sub ((hq.const_mul (θ^2)).div_const 2)))
    simpa only [E,exponentialLogSum_dyadic,Function.comp_def] using hh
  have hFatou : (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)) ∂P) ≤ 1 := by
    calc
      _ = ∫⁻ sample, liminf (fun n => E n sample) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hElim] with sample hs
        exact hs.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ sample, E n sample ∂P) atTop := lintegral_liminf_le' hEm
      _ = 1 := by simp only [hEi,liminf_const]
  have hlimMeas : AEMeasurable (fun sample => ENNReal.ofReal
      (Real.exp (θ*Y sample-θ^2*Q sample/2))) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop hEm hElim
  calc
    _ ≤ ∫⁻ sample, ENNReal.ofReal (Real.exp (θ^2*K/2)) *
        ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hK] with sample hk
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left hk (sq_nonneg θ)]
    _ = ENNReal.ofReal (Real.exp (θ^2*K/2)) *
        (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)) ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_right hFatou (ENNReal.ofReal (Real.exp (θ^2*K/2)))

lemma tail_of_exponential_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ θ : ℝ, (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample)) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*K/2))) {x : ℝ} (hx : 0 < x) :
    P {sample | x < Y sample} ≤ ENNReal.ofReal (Real.exp (-x^2/(2*K))) := by
  let θ := x/K
  have hθ : 0 < θ := div_pos hx hK
  have hYm : AEMeasurable (fun sample => ENNReal.ofReal (Real.exp (θ*Y sample))) P :=
    (hY.const_mul θ).exp.ennreal_ofReal
  have he := meas_ge_le_lintegral_div hYm
    (ENNReal.ofReal_ne_zero_iff.2 (Real.exp_pos (θ*x))) ENNReal.ofReal_ne_top
  have he' : P {sample | x < Y sample} ≤
      (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample)) ∂P) /
        ENNReal.ofReal (Real.exp (θ*x)) := by
    apply (measure_mono _).trans he
    intro sample hs
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hs.le hθ.le))
  refine he'.trans ((ENNReal.div_le_div_right (hbound θ) _).trans_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _),← Real.exp_sub]
  congr 2
  dsimp [θ]
  field_simp
  ring

end SLEExactGauge.BrownianPredictable

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Mesh
open TaylorMeshes BrownianPredictable BrownianIto

lemma spatial_variance_tendsto {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (T : ℝ≥0)
    (C : ℝ → Z → ℝ) (hC : Measurable (Function.uncurry C))
    (a b : Z → ℝ) (ha : ∀ z, a z ∈ Icc 0 (T:ℝ)) (hb : ∀ z, b z ∈ Icc 0 (T:ℝ))
    (D : Z → ℝ → ℝ) (hD : ∀ z, ContinuousOn (D z) (Icc 0 (T:ℝ)))
    (he : ∀ t z, C t z = slab (D z) (a z) (b z) t)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ t ∈ Icc 0 (T:ℝ), ∀ z, |C t z| ≤ K) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (∫ z, C (mesh T n i) z ∂ν)^2 * ((T:ℝ)/(2:ℝ)^n)) atTop
      (𝓝 (∫ t in (0:ℝ)..T, (∫ z, C t z ∂ν)^2)) := by
  let F : ℕ → Z × Z → ℝ := fun n q => ∑ i ∈ Finset.range (2^n),
    (C (mesh T n i) q.1*C (mesh T n i) q.2)*((T:ℝ)/(2:ℝ)^n)
  let G : Z × Z → ℝ := fun q => ∫ t in (0:ℝ)..T, C t q.1*C t q.2
  have hsec (t : ℝ) : Measurable (C t) := hC.comp (measurable_const.prodMk measurable_id)
  have hF (n : ℕ) : Measurable (F n) := by
    apply Finset.measurable_fun_sum
    intro i hi
    exact (((hsec _).comp measurable_fst).mul ((hsec _).comp measurable_snd)).mul_const _
  have hFb (n : ℕ) (q : Z × Z) : ‖F n q‖ ≤ (T:ℝ)*K^2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (2^n), ‖(C (mesh T n i) q.1*C (mesh T n i) q.2)*((T:ℝ)/(2:ℝ)^n)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (2^n), K^2*((T:ℝ)/(2:ℝ)^n) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (T:ℝ)/(2:ℝ)^n)]
        rw [pow_two]
        gcongr <;> exact hbound _ (mesh_mem _ T.coe_nonneg n i (Finset.mem_range.1 hi).le) _
      _ = _ := by simp; field_simp
  have hlim (q : Z × Z) : Tendsto (fun n => F n q) atTop (𝓝 (G q)) := by
    simp only [F,G,he]
    exact slab_riemann_tendsto_integral T.coe_nonneg (ha q.1) (hb q.1) (ha q.2) (hb q.2) (hD q.1) (hD q.2)
  have hl := tendsto_integral_of_dominated_convergence (μ := ν.prod ν) (fun _ : Z × Z => (T:ℝ)*K^2)
    (fun n => (hF n).aestronglyMeasurable) (integrable_const _) (fun n => Filter.Eventually.of_forall (hFb n))
    (Filter.Eventually.of_forall hlim)
  have hFi (n : ℕ) : Integrable (F n) (ν.prod ν) :=
    Integrable.of_bound (hF n).aestronglyMeasurable _ (Filter.Eventually.of_forall (hFb n))
  have hprod (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : Integrable (fun q : Z × Z => C t q.1*C t q.2) (ν.prod ν) := by
    apply Integrable.of_bound (((hsec t).comp measurable_fst).mul ((hsec t).comp measurable_snd)).aestronglyMeasurable (K^2)
    apply Filter.Eventually.of_forall
    intro q
    change |C t q.1*C t q.2| ≤ K^2
    simp only [abs_mul,pow_two]
    exact mul_le_mul (hbound t ht q.1) (hbound t ht q.2) (abs_nonneg _) hK
  have hFe (n : ℕ) : (∫ q, F n q ∂ν.prod ν) = ∑ i ∈ Finset.range (2^n),
      (∫ z, C (mesh T n i) z ∂ν)^2 * ((T:ℝ)/(2:ℝ)^n) := by
    rw [show F n = fun q => ∑ i ∈ Finset.range (2^n), (C (mesh T n i) q.1*C (mesh T n i) q.2)*((T:ℝ)/(2:ℝ)^n) from rfl,
      integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_prod_mul,pow_two]
    · intro i hi
      exact (hprod _ (mesh_mem _ T.coe_nonneg n i (Finset.mem_range.1 hi).le)).mul_const _
  let μ := volume.restrict (Ioc (0:ℝ) (T:ℝ))
  have hCt : Measurable (fun q : (Z × Z) × ℝ => C q.2 q.1.1*C q.2 q.1.2) :=
    ((hC.comp (measurable_snd.prodMk measurable_fst.fst)).mul
      (hC.comp (measurable_snd.prodMk measurable_fst.snd)))
  have hCti : Integrable (fun q : (Z × Z) × ℝ => C q.2 q.1.1*C q.2 q.1.2) ((ν.prod ν).prod μ) := by
    apply Integrable.of_bound hCt.aestronglyMeasurable (K^2)
    have hm : ∀ᵐ t ∂μ, t ∈ Ioc (0:ℝ) (T:ℝ) := ae_restrict_mem measurableSet_Ioc
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2 (Filter.Eventually.of_forall (fun q : Z × Z => hm))] with q hq
    simp only [Real.norm_eq_abs,abs_mul,pow_two]
    exact mul_le_mul (hbound q.2 ⟨hq.1.le,hq.2⟩ q.1.1) (hbound q.2 ⟨hq.1.le,hq.2⟩ q.1.2) (abs_nonneg _) hK
  have hGe : (∫ q, G q ∂ν.prod ν) = ∫ t in (0:ℝ)..T, (∫ z, C t z ∂ν)^2 := by
    simp only [G,intervalIntegral.integral_of_le T.coe_nonneg]
    rw [integral_integral_swap hCti]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      rw [integral_prod_mul,pow_two])
  simpa only [hFe,hGe] using hl

lemma spatial_dyadicVariance_tendsto {Z Ω : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (T : ℝ≥0)
    (A : ℕ → ℕ → Ω × Z → ℝ) (ω : Ω)
    (C : ℝ → Z → ℝ) (hC : Measurable (Function.uncurry C))
    (a b : Z → ℝ) (ha : ∀ z, a z ∈ Icc 0 (T:ℝ)) (hb : ∀ z, b z ∈ Icc 0 (T:ℝ))
    (D : Z → ℝ → ℝ) (hD : ∀ z, ContinuousOn (D z) (Icc 0 (T:ℝ)))
    (he : ∀ t z, C t z = slab (D z) (a z) (b z) t)
    (hAe : ∀ n i, ∀ᵐ z ∂ν, A n i (ω,z) = C (mesh T n i) z)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ t ∈ Icc 0 (T:ℝ), ∀ z, |C t z| ≤ K) :
    Tendsto (fun n => dyadicVariance T (fun n i ω => ∫ z, A n i (ω,z) ∂ν) n ω) atTop
      (𝓝 (∫ t in (0:ℝ)..T, (∫ z, C t z ∂ν)^2)) := by
  have hl := spatial_variance_tendsto ν T C hC a b ha hb D hD he K hK hbound
  convert hl using 1
  funext n
  unfold dyadicVariance
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [integral_congr_ae (hAe n i)]
  rw [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ i)),dyadicTime_step]

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized Mesh
open BrownianPredictable BrownianIto TaylorMeshes PredictableLimit
local instance slabMomentsCoeffRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance slabMomentsCoeffRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance slabMomentsCoeffComplexPathMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance slabMomentsCoeffComplexPathBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

def slabCoeff {Ω : Type*} {ε : ℝ} (hε : 0 < ε) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T s : ℝ≥0) (ρ δ e r : ℝ) (q : Ω × ℂ) : ℝ :=
  coeff hε κ B T s ρ δ e q - coeff hε κ B T s ρ δ r q

def pathFirst {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (κ : ℝ)
    (U : C(I,ℝ)) (b : ℝ≥0 → ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  iteratedDeriv 1 (field hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) (b t.toNNReal)

def pathSlab {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (κ ρ δ e r : ℝ)
    (U : C(I,ℝ)) (V : C(I,ℂ)) (b : ℝ≥0 → ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  slab (pathFirst hε hT κ U b z)
    (observedTime hε hT ρ δ r ((U,V),z)) (observedTime hε hT ρ δ e ((U,V),z)) t

lemma continuous_pathFirst {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (κ : ℝ)
    (U : C(I,ℝ)) (b : ℝ≥0 → ℝ) (hb : Continuous b) :
    Continuous (fun q : ℝ × ℂ => pathFirst hε hT κ U b q.2 q.1) := by
  have hp : Continuous (fun q : ℝ × ℂ => (((U,q.2),q.1),b q.1.toNNReal)) :=
    ((continuous_const.prodMk continuous_snd).prodMk continuous_fst).prodMk
      ((hb.comp continuous_real_toNNReal).comp continuous_fst)
  have hh := (continuous_mark_first hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ)).comp hp
  exact hh

lemma measurable_pathSlab {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (κ ρ δ e r : ℝ)
    (U : C(I,ℝ)) (V : C(I,ℂ)) (b : ℝ≥0 → ℝ) (hb : Continuous b) :
    Measurable (Function.uncurry (pathSlab hε hT κ ρ δ e r U V b)) := by
  have hs (s : ℝ) := (measurable_observedTime hε hT ρ δ s).comp
    (measurable_const.prodMk measurable_id : Measurable (fun z : ℂ => ((U,V),z)))
  exact measurable_slab (continuous_pathFirst hε hT κ U b hb).measurable (hs r) (hs e)

lemma pathSlab_uniform_bound {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (ρ δ e r : ℝ) (her : e ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : C(I,ℝ)) (V : C(I,ℂ)) (b : ℝ≥0 → ℝ) t z,
      |pathSlab hε hT κ ρ δ e r U V b t z| ≤ K := by
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by
    have hh : 1 ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le)
    linarith
  let K := |Real.sqrt κ| *((2*ε/Real.exp ((2/ε^2)*T))^(-(1-κ/8))*(8/κ-1)/ε)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro U V b t z
  exact slab_abs_le (observedTime_antitone hε hT ρ δ ((U,V),z) her) hK
    (first_bound hε hT _ _ _ hp ha U z t (b t.toNNReal))

lemma slabCoeff_eq {Ω : Type*} {A : Set ℂ} {u : ℂ → ℝ}
    (C : FiniteTilt.CommonCutoff A u) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (z : ℂ) (hz : z ∈ A) (hhalf : z ∈ halfPlane) (hu : 0 < u z)
    {ρ : ℝ} (hr : (2*z.im)*Real.exp (-u z) = ρ)
    (V : C(I,ℂ)) (hV : ∀ q : I, V q = γ ω ((C.horizon:ℝ)*q)) (e r : ℝ) (s : ℝ≥0) :
    slabCoeff C.height_pos κ B C.horizon s ρ C.angle e r (ω,z) =
      pathSlab C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r
        (BrownianDriver.path B (Real.sqrt κ) C.horizon ω) V (fun t => B t ω) s z := by
  unfold slabCoeff
  rw [← coeff_common C κ B z hz hr e s ω,← coeff_common C κ B z hz hr r s ω,
    (C.at z hz).physicalCoeff_eq κ B γ g f ω hm hc hb0 hhalf hu e 1 s,
    (C.at z hz).physicalCoeff_eq κ B γ g f ω hm hc hb0 hhalf hu r 1 s]
  dsimp only [pathSlab,slab,pathFirst]
  rw [observedTime_eq C κ B γ g f ω hm hc hb0 z hz hhalf hu hr V hV r,
    observedTime_eq C κ B γ g f ω hm hc hb0 z hz hhalf hu hr V hV e]
  simp only [Real.toNNReal_coe]
  rfl

lemma slabCoeff_variance_tendsto {Ω : Type*} {A : Set ℂ} {u : ℂ → ℝ}
    (C : FiniteTilt.CommonCutoff A u) (hA : MeasurableSet A) [IsFiniteMeasure (volume.restrict A)]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    (hhalf : ∀ z ∈ A, z ∈ halfPlane) (hu : ∀ z ∈ A, 0 < u z)
    {ρ : ℝ} (hr : ∀ z ∈ A, (2*z.im)*Real.exp (-u z) = ρ)
    (V : C(I,ℂ)) (hV : ∀ q : I, V q = γ ω ((C.horizon:ℝ)*q)) (e r : ℝ) (her : e ≤ r) :
    Tendsto (fun n => dyadicVariance C.horizon
      (fun n i ω => ∫ z in A, slabCoeff C.height_pos κ B C.horizon (dyadicTime C.horizon n i) ρ C.angle e r (ω,z)) n ω)
      atTop (𝓝 (∫ t in (0:ℝ)..C.horizon, (∫ z in A,
        pathSlab C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r
          (BrownianDriver.path B (Real.sqrt κ) C.horizon ω) V (fun t => B t ω) t z)^2)) := by
  let U := BrownianDriver.path B (Real.sqrt κ) C.horizon ω
  let a := fun z => observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle r ((U,V),z)
  let b := fun z => observedTime C.height_pos C.horizon.coe_nonneg ρ C.angle e ((U,V),z)
  let D := pathFirst C.height_pos C.horizon.coe_nonneg κ U (fun t => B t ω)
  let S := pathSlab C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r U V (fun t => B t ω)
  obtain ⟨K,hK,hbound⟩ := pathSlab_uniform_bound C.height_pos C.horizon.coe_nonneg κ hκ ρ C.angle e r her
  apply spatial_dyadicVariance_tendsto (K := K) (volume.restrict A) C.horizon
    (fun n i => slabCoeff C.height_pos κ B C.horizon (dyadicTime C.horizon n i) ρ C.angle e r)
    ω S (measurable_pathSlab _ _ _ _ _ _ _ _ _ _ hc) a b
    (fun z => observedTime_bounds _ _ _ _ _ _) (fun z => observedTime_bounds _ _ _ _ _ _) D
  · intro z
    have hh := (continuous_pathFirst C.height_pos C.horizon.coe_nonneg κ U (fun t => B t ω) hc).comp
      (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ => (t,z)))
    exact hh.continuousOn
  · intro t z; rfl
  · intro n i
    filter_upwards [ae_restrict_mem hA] with z hz
    simpa only [coe_dyadicTime] using
      slabCoeff_eq C κ B γ g f ω hm hc hb0 z hz (hhalf z hz) (hu z hz) (hr z hz) V hV e r (dyadicTime C.horizon n i)
  · exact hK
  · intro t ht z
    exact hbound U V (fun t => B t ω) t z

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.SpatialLimit
open L2Limit

lemma uniformIntegrable_one_of_eLpNorm_two_bounded {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEStronglyMeasurable (X i) P) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (X i) 2 P ≤ C) : UniformIntegrable X 1 P := by
  let D : ℝ≥0∞ := (C : ℝ≥0∞) * (P univ) ^ (1/2 : ℝ)
  have hDt : D ≠ ∞ := by dsimp [D]; finiteness
  refine ⟨?_, D.toNNReal, ?_⟩
  · apply unifIntegrable_iff.2
    intro ε hε
    by_cases hεt : ε = ∞
    · subst ε
      exact ⟨1, by norm_num, fun _ _ _ => le_top⟩
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    let d : ℝ≥0 := ⟨ε.toReal / ((C : ℝ)+1), div_nonneg hεr.le (by positivity)⟩
    have hd : 0 < (d : ℝ) := div_pos hεr (by positivity)
    refine ⟨ENNReal.ofReal ((d : ℝ)^2), ENNReal.ofReal_pos.2 (sq_pos_of_pos hd),
      fun i s hμs => ?_⟩
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hXm i).restrict
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one] at hb
    rw [Measure.restrict_apply_univ] at hb
    have hp : (P s) ^ (1/2 : ℝ) ≤ (d : ℝ≥0∞) := by
      calc
        _ ≤ (ENNReal.ofReal ((d : ℝ)^2)) ^ (1/2 : ℝ) :=
          ENNReal.rpow_le_rpow hμs (by norm_num)
        _ = _ := by
          rw [ENNReal.ofReal_pow d.coe_nonneg]
          simp only [ENNReal.ofReal_coe_nnreal]
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
    calc
      _ ≤ eLpNorm (X i) 2 (P.restrict s) * (P s) ^ (1/2 : ℝ) := hb
      _ ≤ C * (d : ℝ≥0∞) := mul_le_mul
        ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i)) hp (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal ε.toReal := by
        rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
        simp only [NNReal.coe_mul]
        apply ENNReal.ofReal_le_ofReal
        change (C : ℝ) * (ε.toReal / ((C : ℝ)+1)) ≤ ε.toReal
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
      _ = ε := ENNReal.ofReal_toReal hεt
  · intro i
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hXm i)
    rw [ENNReal.coe_toNNReal hDt]
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one] at hb
    exact hb.trans (mul_le_mul_left (hC i) ((P univ) ^ (1/2 : ℝ)))

lemma L1_tendsto_of_square_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (A : ℝ)
    (hA : ∀ n, (∫ ω, X n ω ^ 2 ∂P) ≤ A)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y P ∧ Tendsto (fun n => eLpNorm (X n-Y) 1 P) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := (ENNReal.ofReal A) ^ (1/2 : ℝ)
  have hCt : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hC (n : ℕ) : eLpNorm (X n) 2 P ≤ C.toNNReal := by
    rw [ENNReal.coe_toNNReal hCt, eLpNorm_two_eq_integral_sq (hX n)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hA n)) (by norm_num)
  have hui := uniformIntegrable_one_of_eLpNorm_two_bounded
    (fun n => (hX n).aestronglyMeasurable) C.toNNReal hC
  have hY := hui.memLp_of_ae_tendsto hXY
  exact ⟨memLp_one_iff_integrable.1 hY,
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      (by norm_num) (fun n => (hX n).aestronglyMeasurable) hY hui.unifIntegrable hXY⟩

lemma integrate_L1_le {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ν : Measure Z} [SFinite P] [SFinite ν]
    {X Y : Ω × Z → ℝ} (hX : Integrable X (P.prod ν)) (hY : Integrable Y (P.prod ν)) :
    eLpNorm ((fun ω => ∫ z, X (ω,z) ∂ν)-(fun ω => ∫ z, Y (ω,z) ∂ν)) 1 P ≤
      eLpNorm (X-Y) 1 (P.prod ν) := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (hX.aestronglyMeasurable.integral_prod_right'.sub
      hY.aestronglyMeasurable.integral_prod_right'),
    eLpNorm_one_eq_lintegral_enorm (hX.sub hY).aestronglyMeasurable]
  rw [lintegral_prod _ (hX.sub hY).aestronglyMeasurable.enorm]
  apply lintegral_mono_ae
  filter_upwards [hX.prod_right_ae,hY.prod_right_ae] with ω hx hy
  simp only [Pi.sub_apply]
  rw [← integral_sub hx hy]
  change ‖∫ z, X (ω,z)-Y (ω,z) ∂ν‖ₑ ≤ _
  exact enorm_integral_le_lintegral_enorm _

lemma spatial_L1_limit {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ν : Measure Z} [IsFiniteMeasure P] [IsFiniteMeasure ν]
    {X : ℕ → Ω × Z → ℝ} {Y : Ω × Z → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (P.prod ν)) (A : ℝ)
    (hA : ∀ n, (∫ q, X n q ^ 2 ∂P.prod ν) ≤ A)
    (hXY : ∀ᵐ q ∂P.prod ν, Tendsto (fun n => X n q) atTop (𝓝 (Y q))) :
    Integrable Y (P.prod ν) ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P,
        Tendsto (fun n => ∫ z, X (ns n) (ω,z) ∂ν) atTop (𝓝 (∫ z, Y (ω,z) ∂ν)) := by
  obtain ⟨hY,hL⟩ := L1_tendsto_of_square_bound hX A hA hXY
  have hi (n : ℕ) := (hX n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hh : Tendsto (fun n => eLpNorm
      ((fun ω => ∫ z, X n (ω,z) ∂ν)-(fun ω => ∫ z, Y (ω,z) ∂ν)) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun _ => bot_le) (fun n => integrate_L1_le (hi n) hY)
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    hh
  exact ⟨hY,hm.exists_seq_tendsto_ae⟩

end SLEExactGauge.SpatialLimit

end

end

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.SpatialLimit

lemma memLp_two_prod_of_fiber_bound {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ν : Measure Z} [SFinite P] [IsFiniteMeasure ν]
    {X : Ω × Z → ℝ} (hX : AEMeasurable X (P.prod ν))
    (hXi : ∀ᵐ z ∂ν, MemLp (fun ω => X (ω,z)) 2 P) (A : ℝ)
    (hA : ∀ᵐ z ∂ν, (∫ ω, X (ω,z)^2 ∂P) ≤ A) :
    MemLp X 2 (P.prod ν) ∧ (∫ q, X q ^ 2 ∂P.prod ν) ≤ ∫ _ : Z, A ∂ν := by
  have hsq : AEStronglyMeasurable (fun q => X q^2) (P.prod ν) := (hX.pow_const 2).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun z => ∫ ω, ‖X (ω,z)^2‖ ∂P) ν :=
    hsq.norm.prod_swap.integral_prod_right'
  have he (z : Z) : (∫ ω, ‖X (ω,z)^2‖ ∂P) = ∫ ω, X (ω,z)^2 ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => Real.norm_of_nonneg (sq_nonneg _))
  have hi : Integrable (fun q => X q^2) (P.prod ν) := by
    apply (integrable_prod_iff' hsq).2
    refine ⟨hXi.mono (fun z hz => hz.integrable_sq),?_⟩
    apply (integrable_const A).mono' hmeas
    filter_upwards [hA] with z hz
    rw [he,Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact hz
  refine ⟨(memLp_two_iff_integrable_sq hX.aestronglyMeasurable).2 hi,?_⟩
  rw [integral_prod_symm _ hi]
  exact integral_mono_ae hi.integral_prod_right (integrable_const _) hA

lemma ae_prod_tendsto_of_fibers {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ν : Measure Z} [SFinite P] [SFinite ν]
    {X : ℕ → Ω × Z → ℝ} {Y : Ω × Z → ℝ}
    (hX : ∀ n, AEMeasurable (X n) (P.prod ν)) (hY : AEMeasurable Y (P.prod ν))
    (hh : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P, Tendsto (fun n => X n (ω,z)) atTop (𝓝 (Y (ω,z)))) :
    ∀ᵐ q ∂P.prod ν, Tendsto (fun n => X n q) atTop (𝓝 (Y q)) := by
  let F : ℕ → Ω × Z → ℝ := fun n => (hX n).mk (X n)
  let G := hY.mk Y
  have hF (n : ℕ) : Measurable (F n) := (hX n).measurable_mk
  have hG : Measurable G := hY.measurable_mk
  have he : ∀ᵐ q ∂P.prod ν, (∀ n, X n q = F n q) ∧ Y q = G q :=
    (ae_all_iff.2 (fun n => (hX n).ae_eq_mk)).and hY.ae_eq_mk
  have hes : ∀ᵐ q ∂ν.prod P, (∀ n, X n q.swap = F n q.swap) ∧ Y q.swap = G q.swap :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae he
  have hf : ∀ᵐ q ∂ν.prod P, Tendsto (fun n => F n q.swap) atTop (𝓝 (G q.swap)) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun
      (fun n => (hF n).comp measurable_swap) (hG.comp measurable_swap))).2
    filter_upwards [hh,Measure.ae_ae_of_ae_prod hes] with z hz hez
    filter_upwards [hz,hez] with ω hω heω
    change (∀ n, X n (ω,z) = F n (ω,z)) ∧ Y (ω,z) = G (ω,z) at heω
    change Tendsto (fun n => F n (ω,z)) atTop (𝓝 (G (ω,z)))
    simpa only [heω.1,heω.2] using hω
  have hf' := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hf
  filter_upwards [he,hf'] with q heq hq
  simpa only [heq.1,heq.2,Prod.swap_swap] using hq

end SLEExactGauge.SpatialLimit

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable
open PredictableLimit

theorem limit_exponential_bound_subseq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T : ℝ≥0) (A : ℕ → ℕ → Ω → ℝ)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (A n i))
    (hAa : ∀ n i, AEMeasurable (A n i) P)
    (ns : ℕ → ℕ) (Y Q : Ω → ℝ)
    (hY : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T A (ns n) sample) atTop (𝓝 (Y sample)))
    (hQ : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicVariance T A (ns n) sample) atTop (𝓝 (Q sample)))
    (K : ℝ) (hK : ∀ᵐ sample ∂P, Q sample ≤ K) (θ : ℝ) :
    (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample)) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*K/2)) := by
  let E : ℕ → Ω → ℝ≥0∞ := fun n sample => ENNReal.ofReal
    (Real.exp (exponentialLogSum B (dyadicTime T (ns n)) (A (ns n)) θ (2^(ns n)) sample))
  have hEm (n : ℕ) : AEMeasurable (E n) P :=
    ((exponentialLogSum_aemeasurable hB _ _ (hAa (ns n)) θ (2^(ns n))).exp).ennreal_ofReal
  have hEi (n : ℕ) : (∫⁻ sample, E n sample ∂P) = 1 :=
    exponentialLogSum_identity hB _ (dyadicTime_mono T (ns n)) _ (hA (ns n)) (hAa (ns n)) θ (2^(ns n))
  have hElim : ∀ᵐ sample ∂P, Tendsto (fun n => E n sample) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)))) := by
    filter_upwards [hY,hQ] with sample hy hq
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp
        ((hy.const_mul θ).sub ((hq.const_mul (θ^2)).div_const 2)))
    simpa only [E,exponentialLogSum_dyadic,Function.comp_def] using hh
  have hFatou : (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)) ∂P) ≤ 1 := by
    calc
      _ = ∫⁻ sample, liminf (fun n => E n sample) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hElim] with sample hs
        exact hs.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ sample, E n sample ∂P) atTop := lintegral_liminf_le' hEm
      _ = 1 := by simp only [hEi,liminf_const]
  have hlimMeas : AEMeasurable (fun sample => ENNReal.ofReal
      (Real.exp (θ*Y sample-θ^2*Q sample/2))) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop hEm hElim
  calc
    _ ≤ ∫⁻ sample, ENNReal.ofReal (Real.exp (θ^2*K/2)) *
        ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hK] with sample hk
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_left hk (sq_nonneg θ)]
    _ = ENNReal.ofReal (Real.exp (θ^2*K/2)) *
        (∫⁻ sample, ENNReal.ofReal (Real.exp (θ*Y sample-θ^2*Q sample/2)) ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_right hFatou (ENNReal.ofReal (Real.exp (θ^2*K/2)))

end SLEExactGauge.BrownianPredictable

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.SpatialLimit
open BrownianPredictable PredictableLimit

lemma dyadicDriverSum_integrate {Ω Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (A : ℕ → ℕ → Ω × Z → ℝ) (n : ℕ) (ω : Ω)
    (hA : ∀ i, Integrable (fun z => A n i (ω,z)) ν) :
    dyadicDriverSum B T (fun n i ω => ∫ z, A n i (ω,z) ∂ν) n ω =
      ∫ z, dyadicDriverSum B T (fun n i ω => A n i (ω,z)) n ω ∂ν := by
  unfold dyadicDriverSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const]
  · intro i hi
    exact (hA i).mul_const _

theorem spatial_exponential_bound {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : Measure Z) [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (A : ℕ → ℕ → Ω × Z → ℝ)
    (hAi : ∀ n i, Integrable (A n i) (P.prod ν))
    (hA : ∀ n i, @Measurable (Ω × Z) ℝ
      (Prod.instMeasurableSpace (m₁ := pastSigma B (dyadicTime T n i)) (m₂ := inferInstance)) _ (A n i))
    (Y : Ω × Z → ℝ)
    (hX : ∀ n, MemLp (fun q => dyadicDriverSum B T (fun n i ω => A n i (ω,q.2)) n q.1) 2 (P.prod ν))
    (V : ℝ) (hV : ∀ n, (∫ q, (dyadicDriverSum B T (fun n i ω => A n i (ω,q.2)) n q.1)^2 ∂P.prod ν) ≤ V)
    (hY : ∀ᵐ q ∂P.prod ν, Tendsto
      (fun n => dyadicDriverSum B T (fun n i ω => A n i (ω,q.2)) n q.1) atTop (𝓝 (Y q)))
    (Q : Ω → ℝ)
    (hQ : ∀ᵐ ω ∂P, Tendsto (fun n => dyadicVariance T (fun n i ω => ∫ z, A n i (ω,z) ∂ν) n ω)
      atTop (𝓝 (Q ω))) (K θ : ℝ) (hK : ∀ᵐ ω ∂P, Q ω ≤ K) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(∫ z, Y (ω,z) ∂ν))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*K/2)) := by
  let C := fun n i ω => ∫ z, A n i (ω,z) ∂ν
  have hCi (n i : ℕ) : AEMeasurable (C n i) P :=
    (hAi n i).aestronglyMeasurable.integral_prod_right'.aemeasurable
  have hCp (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (C n i) := by
    let : MeasurableSpace Ω := pastSigma B (dyadicTime T n i)
    exact (hA n i).stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨hYi,ns,hns,hlim⟩ := spatial_L1_limit hX V hV hY
  have he : ∀ᵐ ω ∂P, ∀ n, dyadicDriverSum B T C n ω =
      ∫ z, dyadicDriverSum B T (fun n i ω => A n i (ω,z)) n ω ∂ν := by
    have hh : ∀ᵐ ω ∂P, ∀ n i, Integrable (fun z => A n i (ω,z)) ν :=
      ae_all_iff.2 (fun n => ae_all_iff.2 (fun i => (hAi n i).prod_right_ae))
    filter_upwards [hh] with ω hω n
    exact dyadicDriverSum_integrate ν B T A n ω (hω n)
  have hS : ∀ᵐ ω ∂P, Tendsto (fun n => dyadicDriverSum B T C (ns n) ω) atTop
      (𝓝 (∫ z, Y (ω,z) ∂ν)) := by
    filter_upwards [he,hlim] with ω heω hω
    simpa only [heω] using hω
  have hQV : ∀ᵐ ω ∂P, Tendsto (fun n => dyadicVariance T C (ns n) ω) atTop (𝓝 (Q ω)) :=
    hQ.mono (fun ω hω => hω.comp hns.tendsto_atTop)
  exact limit_exponential_bound_subseq hB T C hCp hCi ns _ Q hS hQV K hK θ

lemma sums_aemeasurable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ν : Measure Z} [SFinite P] [SFinite ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (A : ℕ → ℕ → Ω × Z → ℝ)
    (hA : ∀ n i, AEMeasurable (A n i) (P.prod ν)) (n : ℕ) :
    AEMeasurable (fun q => dyadicDriverSum B T (fun n i ω => A n i (ω,q.2)) n q.1) (P.prod ν) := by
  apply Finset.aemeasurable_fun_sum
  intro i hi
  exact (hA n i).mul
    (((hB.toIsPreBrownianReal.hasLaw_eval _).aemeasurable.comp_fst).sub
      ((hB.toIsPreBrownianReal.hasLaw_eval _).aemeasurable.comp_fst))

lemma bounded_sums {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : Measure Z) [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (A : ℕ → ℕ → Ω × Z → ℝ)
    (hA : ∀ n i, @Measurable (Ω × Z) ℝ
      (Prod.instMeasurableSpace (m₁ := pastSigma B (dyadicTime T n i)) (m₂ := inferInstance)) _ (A n i))
    (hAm : ∀ n i, AEMeasurable (A n i) (P.prod ν))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ n i q, |A n i q| ≤ K) :
    (∀ n i, Integrable (A n i) (P.prod ν)) ∧
    ∀ n, MemLp (fun q => dyadicDriverSum B T (fun n i ω => A n i (ω,q.2)) n q.1) 2 (P.prod ν) ∧
      (∫ q, (dyadicDriverSum B T (fun n i ω => A n i (ω,q.2)) n q.1)^2 ∂P.prod ν) ≤
        ∫ _ : Z, K^2*(T:ℝ) ∂ν := by
  have hi (n i : ℕ) : Integrable (A n i) (P.prod ν) :=
    Integrable.of_bound (hAm n i).aestronglyMeasurable K (Filter.Eventually.of_forall (hbound n i))
  refine ⟨hi,?_⟩
  intro n
  have hsect : ∀ᵐ z ∂ν, ∀ n i, AEStronglyMeasurable (fun ω => A n i (ω,z)) P :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun i => ((hi n i).prod_left_ae.mono (fun z hz => hz.aestronglyMeasurable))))
  have hcp (z : Z) (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (fun ω => A n i (ω,z)) := by
    let : MeasurableSpace Ω := pastSigma B (dyadicTime T n i)
    exact (hA n i).comp (measurable_id.prodMk measurable_const)
  have hh : ∀ᵐ z ∂ν,
      MemLp (fun ω => dyadicDriverSum B T (fun n i ω => A n i (ω,z)) n ω) 2 P ∧
      (∫ ω, (dyadicDriverSum B T (fun n i ω => A n i (ω,z)) n ω)^2 ∂P) ≤ K^2*(T:ℝ) := by
    filter_upwards [hsect] with z hz
    have h2 (n i : ℕ) : MemLp (fun ω => A n i (ω,z)) 2 P :=
      MemLp.of_bound (hz n i) K (Filter.Eventually.of_forall (fun ω => hbound n i (ω,z)))
    exact ⟨dyadicDriverSum_memLp hB T _ (hcp z) h2 n,
      dyadicDriverSum_second_moment_le hB T _ (hcp z) h2 K hK
        (fun n i => Filter.Eventually.of_forall (fun ω => hbound n i (ω,z))) n⟩
  exact memLp_two_prod_of_fiber_bound (sums_aemeasurable hB T A hAm n)
    (hh.mono (fun z hz => hz.1)) (K^2*(T:ℝ)) (hh.mono (fun z hz => hz.2))

end SLEExactGauge.SpatialLimit

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized Mesh
open BrownianPredictable BrownianIto TaylorMeshes PredictableLimit
local instance slabMomentsDifferenceRealPathMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance slabMomentsDifferenceRealPathBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance slabMomentsDifferenceComplexPathMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance slabMomentsDifferenceComplexPathBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

def observedDifference {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (κ ρ δ e r : ℝ)
    (q : (C(I,ℝ) × C(I,ℂ)) × ℂ) : ℝ :=
  observedValue hε hT ρ δ e (1-κ/8) (8/κ-1) q -
    observedValue hε hT ρ δ r (1-κ/8) (8/κ-1) q

lemma observedDifference_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (ν : Measure ℂ) [SFinite ν] {ε : ℝ} (hε : 0 < ε)
    (κ ρ δ e r : ℝ) (T : ℝ≥0) (V : Ω → C(I,ℂ)) (hV : Measurable V) :
    AEMeasurable (fun q : Ω × ℂ => observedDifference hε T.coe_nonneg κ ρ δ e r
      ((BrownianDriver.path B (Real.sqrt κ) T q.1,V q.1),q.2)) (P.prod ν) := by
  have hc := (measurable_observedValue hε T.coe_nonneg ρ δ e (1-κ/8) (8/κ-1)).sub
    (measurable_observedValue hε T.coe_nonneg ρ δ r (1-κ/8) (8/κ-1))
  have hp : AEMeasurable (fun q : Ω × ℂ => ((BrownianDriver.path B (Real.sqrt κ) T q.1,V q.1),q.2)) (P.prod ν) :=
    (((BrownianDriver.path_aemeasurable hB (Real.sqrt κ) T).comp_fst).prodMk
      ((hV.comp measurable_fst).aemeasurable)).prodMk measurable_snd.aemeasurable
  exact hc.comp_aemeasurable hp

lemma slab_sum_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Set ℂ} {u : ℂ → ℝ} (C : FiniteTilt.CommonCutoff A u)
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (z : ℂ) (hz : z ∈ A) (hhalf : z ∈ halfPlane) (hu : 0 < u z)
    {ρ : ℝ} (hr : (2*z.im)*Real.exp (-u z) = ρ)
    (V : Ω → C(I,ℂ)) (hV : ∀ᵐ ω ∂P, ∀ q : I, V ω q = γ ω ((C.horizon:ℝ)*q)) (e r : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => dyadicDriverSum B C.horizon
      (fun n i ω => slabCoeff C.height_pos κ B C.horizon (dyadicTime C.horizon n i) ρ C.angle e r (ω,z)) n ω) atTop
      (𝓝 (observedDifference C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r
        ((BrownianDriver.path B (Real.sqrt κ) C.horizon ω,V ω),z))) := by
  have he := (C.at z hz).physical_sum_tendsto hB κ hκ γ g f hmaps hhalf hu e
  have hr' := (C.at z hz).physical_sum_tendsto hB κ hκ γ g f hmaps hhalf hu r
  filter_upwards [he,hr',hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hV] with ω heω hrω hm hc hb0 hVω
  have hv (s : ℝ) := observedValue_eq C κ B γ g f ω hm hc hb0 z hz hhalf hu hr (V ω) hVω s
  unfold observedDifference
  rw [hv e,hv r]
  have hl := heω.sub hrω
  convert hl using 1
  · funext n
    simp only [dyadicDriverSum,slabCoeff,← coeff_common C κ B z hz hr,
      sub_mul,Finset.sum_sub_distrib]
    rfl
  · congr 1
    ring

end SLEExactGauge.MeshSlab

end

end

end OAI
