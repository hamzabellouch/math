import Mathlib
import OAI.Geometry.BallPacking.Necessity.GlobalArea

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

def planeUnitCutoff (z : Plane) : ℝ := outerProfile 1 (radiusSq z)

theorem planeUnitCutoff_smooth : ContDiff ℝ ∞ planeUnitCutoff :=
  (outerProfile_smooth 1).comp radiusSq_smooth

theorem planeUnitCutoff_compact : HasCompactSupport planeUnitCutoff :=
  HasCompactSupport.comp_radiusSq (outerProfile_compact (by norm_num : (0:ℝ)<1))

theorem planeUnitCutoff_bounds (z : Plane) : 0 ≤ planeUnitCutoff z ∧ planeUnitCutoff z ≤ 1 :=
  ⟨outerProfile_nonneg 1 (radiusSq z),outerProfile_le_one 1 (radiusSq z)⟩

theorem planeUnitCutoff_one {z : Plane} (hz : radiusSq z ≤ 1) : planeUnitCutoff z = 1 :=
  outerProfile_one (by norm_num) (radiusSq_nonneg z) hz

theorem planeUnitCutoff_deriv_zero {z : Plane} (hz : radiusSq z < 1) :
    fderiv ℝ planeUnitCutoff z = 0 := by
  have he : planeUnitCutoff =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
    filter_upwards [radiusSq_smooth.continuous.continuousAt.eventually
      (Iio_mem_nhds hz)] with w hw
    exact planeUnitCutoff_one hw.le
  rw [he.fderiv_eq]
  exact fderiv_const_apply _

def planeDilatedCutoff (N : ℕ) (z : Plane) : ℝ :=
  planeUnitCutoff (((N:ℝ)+1)⁻¹ • z)

theorem planeDilatedCutoff_smooth (N : ℕ) : ContDiff ℝ ∞ (planeDilatedCutoff N) :=
  by
    have h : ContDiff ℝ ∞ (fun z : Plane => ((N:ℝ)+1)⁻¹ • z) :=
      ((((N:ℝ)+1)⁻¹) • ContinuousLinearMap.id ℝ Plane).contDiff
    exact planeUnitCutoff_smooth.comp h

theorem planeDilatedCutoff_compact (N : ℕ) : HasCompactSupport (planeDilatedCutoff N) := by
  exact planeUnitCutoff_compact.comp_homeomorph
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero (by positivity : (N:ℝ)+1≠0))).unit)

theorem planeDilatedCutoff_bounds (N : ℕ) (z : Plane) :
    0 ≤ planeDilatedCutoff N z ∧ planeDilatedCutoff N z ≤ 1 :=
  planeUnitCutoff_bounds _

theorem planeDilatedCutoff_fderiv (N : ℕ) (z : Plane) :
    fderiv ℝ (planeDilatedCutoff N) z =
      ((N:ℝ)+1)⁻¹ • fderiv ℝ planeUnitCutoff (((N:ℝ)+1)⁻¹ • z) := by
  have h := (planeUnitCutoff_smooth.differentiable (by simp) _).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul (((N:ℝ)+1)⁻¹))
  have he := h.fderiv
  dsimp only [Function.comp_def, Pi.smul_apply, id_eq] at he
  rw [show fderiv ℝ (planeDilatedCutoff N) z = _ from he]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]

theorem planeDilatedCutoff_tendsto_smul (z : Plane) :
    Tendsto (fun N : ℕ => (((N:ℝ)+1)⁻¹) • z) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop))).smul_const z

theorem planeDilatedCutoff_eventually_one (z : Plane) :
    ∀ᶠ N in atTop, planeDilatedCutoff N z = 1 := by
  have h := (radiusSq_smooth.continuous.tendsto 0).comp (planeDilatedCutoff_tendsto_smul z)
  have hh : radiusSq (0:Plane) < 1 := by norm_num [radiusSq]
  filter_upwards [h.eventually (Iio_mem_nhds hh)] with N hN
  exact planeUnitCutoff_one hN.le

theorem planeDilatedCutoff_eventually_deriv_zero (z : Plane) :
    ∀ᶠ N in atTop, fderiv ℝ (planeDilatedCutoff N) z = 0 := by
  have h := (radiusSq_smooth.continuous.tendsto 0).comp (planeDilatedCutoff_tendsto_smul z)
  have hh : radiusSq (0:Plane) < 1 := by norm_num [radiusSq]
  filter_upwards [h.eventually (Iio_mem_nhds hh)] with N hN
  rw [planeDilatedCutoff_fderiv,planeUnitCutoff_deriv_zero hN,smul_zero]

theorem compact_smooth_derivative_sq_integrable {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun z => ‖fderiv ℝ f z‖^2) := by
  have hc1 : HasCompactSupport (fderiv ℝ f) := hc.fderiv ℝ
  have hc2 : HasCompactSupport ((fun L : Plane →L[ℝ] ℝ => ‖L‖^2) ∘ fderiv ℝ f) :=
    hc1.comp_left (by simp)
  exact (((hf.continuous_fderiv (by simp)).norm).pow 2).integrable_of_hasCompactSupport hc2

theorem planeDilatedCutoff_grad_integral (N : ℕ) :
    (∫ z : Plane, ‖fderiv ℝ (planeDilatedCutoff N) z‖^2) =
      ∫ z : Plane, ‖fderiv ℝ planeUnitCutoff z‖^2 := by
  simp_rw [planeDilatedCutoff_fderiv,norm_smul,Real.norm_eq_abs,mul_pow,
    sq_abs]
  rw [integral_const_mul, Measure.integral_comp_smul volume
    (fun z : Plane => ‖fderiv ℝ planeUnitCutoff z‖^2)]
  have hn : (N:ℝ)+1 ≠ 0 := by positivity
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane,Module.finrank_prod]
  rw [hdim]
  simp only [smul_eq_mul,inv_pow,inv_inv,abs_pow,abs_of_nonneg (by positivity : 0≤(N:ℝ)+1)]
  field_simp

def cutoffDerivativeTail (N : ℕ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) : ℝ :=
  by
    classical
    exact if fderiv ℝ (planeDilatedCutoff N) z = 0 then 0 else ‖β z‖^2

theorem cutoffDerivativeTail_bounds (N : ℕ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    0 ≤ cutoffDerivativeTail N β z ∧ cutoffDerivativeTail N β z ≤ ‖β z‖^2 := by
  classical
  unfold cutoffDerivativeTail
  split_ifs <;> constructor <;> first | positivity | exact le_rfl

theorem cutoffDerivativeTail_integrable (N : ℕ) {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : Integrable (fun z => ‖β z‖^2)) : Integrable (cutoffDerivativeTail N β) := by
  classical
  have hm : MeasurableSet {z | fderiv ℝ (planeDilatedCutoff N) z ≠ 0} :=
    (isClosed_singleton.preimage
      ((planeDilatedCutoff_smooth N).continuous_fderiv (by simp))).isOpen_compl.measurableSet
  have he : cutoffDerivativeTail N β =
      {z | fderiv ℝ (planeDilatedCutoff N) z ≠ 0}.indicator (fun z => ‖β z‖^2) := by
    funext z
    simp only [cutoffDerivativeTail,Set.indicator,mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he]
  exact hβ.indicator hm

theorem cutoffDerivativeTail_integral_tendsto {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : Integrable (fun z => ‖β z‖^2)) :
    Tendsto (fun N => ∫ z, cutoffDerivativeTail N β z) atTop (𝓝 0) := by
  classical
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0:ℝ)) (fun z => ‖β z‖^2)
    (fun N => (cutoffDerivativeTail_integrable N hβ).aestronglyMeasurable) hβ
    (fun N => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (cutoffDerivativeTail_bounds N β z).1]
      exact (cutoffDerivativeTail_bounds N β z).2)
    (Filter.Eventually.of_forall fun z => by
      apply Filter.EventuallyEq.tendsto
      filter_upwards [planeDilatedCutoff_eventually_deriv_zero z] with N hN
      simp [cutoffDerivativeTail,hN])
  simpa using ht

theorem cutoffWedge_norm_le (f : Plane → ℝ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    ‖cutoffWedge f β z‖ ≤ 2 * ‖fderiv ℝ f z‖ * ‖β z‖ := by
  have h1 : ‖fderiv ℝ f z (1,0)‖ ≤ ‖fderiv ℝ f z‖ := by
    simpa using (fderiv ℝ f z).le_opNorm ((1,0):Plane)
  have h2 : ‖fderiv ℝ f z (0,1)‖ ≤ ‖fderiv ℝ f z‖ := by
    simpa using (fderiv ℝ f z).le_opNorm ((0,1):Plane)
  have h3 : ‖β z (1,0)‖ ≤ ‖β z‖ := by
    simpa using (β z).le_opNorm ((1,0):Plane)
  have h4 : ‖β z (0,1)‖ ≤ ‖β z‖ := by
    simpa using (β z).le_opNorm ((0,1):Plane)
  calc
    _ ≤ ‖fderiv ℝ f z (1,0)‖ * ‖β z (0,1)‖ +
        ‖fderiv ℝ f z (0,1)‖ * ‖β z (1,0)‖ := by
      simpa only [cutoffWedge,norm_mul] using
        norm_sub_le (fderiv ℝ f z (1,0)*β z (0,1)) (fderiv ℝ f z (0,1)*β z (1,0))
    _ ≤ _ := by nlinarith [mul_le_mul h1 h4 (norm_nonneg _) (norm_nonneg _),
        mul_le_mul h2 h3 (norm_nonneg _) (norm_nonneg _)]

theorem cutoffWedge_young (N : ℕ) (β : Plane → Plane →L[ℝ] ℝ)
    {ε : ℝ} (hε : 0 < ε) (z : Plane) :
    ‖cutoffWedge (planeDilatedCutoff N) β z‖ ≤
      ε * ‖fderiv ℝ (planeDilatedCutoff N) z‖^2 + ε⁻¹ * cutoffDerivativeTail N β z := by
  classical
  by_cases hz : fderiv ℝ (planeDilatedCutoff N) z = 0
  · simp [cutoffWedge, cutoffDerivativeTail, hz]
  rw [cutoffDerivativeTail,ite_eq_right hz]
  apply (cutoffWedge_norm_le _ _ _).trans
  apply (mul_le_mul_iff_right₀ hε).mp
  have hi : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
  nlinarith [sq_nonneg (ε * ‖fderiv ℝ (planeDilatedCutoff N) z‖ - ‖β z‖)]

theorem integral_cutoffCurl_tendsto {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) (hc : Integrable (planarCurl β)) :
    Tendsto (fun N => ∫ z, planeDilatedCutoff N z * planarCurl β z) atTop
      (𝓝 (∫ z, planarCurl β z)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖planarCurl β z‖)
  · intro N
    exact ((planeDilatedCutoff_smooth N).mul (planarCurl_contDiff hβ)).continuous.aestronglyMeasurable
  · exact hc.norm
  · intro N
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul,Real.norm_of_nonneg (planeDilatedCutoff_bounds N z).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (planeDilatedCutoff_bounds N z).2
  · apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [planeDilatedCutoff_eventually_one z] with N hN
    rw [hN,one_mul]

 

theorem integral_planarCurl_zero_of_sq_integrable {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) (hc : Integrable (planarCurl β))
    (hβ2 : Integrable (fun z => ‖β z‖^2)) : (∫ z, planarCurl β z) = 0 := by
  let B := ∫ z : Plane, ‖fderiv ℝ planeUnitCutoff z‖^2
  have hAll (ε : ℝ) (hε : 0 < ε) : |∫ z, planarCurl β z| ≤ ε * B := by
    have hineq (N : ℕ) : |∫ z, planeDilatedCutoff N z * planarCurl β z| ≤
        ε * B + ε⁻¹ * ∫ z, cutoffDerivativeTail N β z := by
      have hi := cutoffWedge_integrable (planeDilatedCutoff_smooth N)
        (planeDilatedCutoff_compact N) hβ
      have hgrad := compact_smooth_derivative_sq_integrable (planeDilatedCutoff_smooth N)
        (planeDilatedCutoff_compact N)
      calc
        _ = ‖∫ z, cutoffWedge (planeDilatedCutoff N) β z‖ := by
          rw [integral_cutoffWedge (planeDilatedCutoff_smooth N) (planeDilatedCutoff_compact N) hβ]
          simp only [norm_neg,Real.norm_eq_abs]
        _ ≤ ∫ z, ‖cutoffWedge (planeDilatedCutoff N) β z‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ z, ε * ‖fderiv ℝ (planeDilatedCutoff N) z‖^2 +
            ε⁻¹ * cutoffDerivativeTail N β z :=
          integral_mono hi.norm ((hgrad.const_mul ε).add
            ((cutoffDerivativeTail_integrable N hβ2).const_mul _)) (cutoffWedge_young N β hε)
        _ = _ := by
          rw [integral_add (hgrad.const_mul ε)
            ((cutoffDerivativeTail_integrable N hβ2).const_mul _),integral_const_mul,
            integral_const_mul,planeDilatedCutoff_grad_integral]
    have hb := (tendsto_const_nhds (x := ε * B)).add
      ((cutoffDerivativeTail_integral_tendsto hβ2).const_mul ε⁻¹)
    have hh := le_of_tendsto_of_tendsto (integral_cutoffCurl_tendsto hβ hc).abs hb
      (Filter.Eventually.of_forall hineq)
    simpa only [mul_zero,add_zero] using hh
  have ht : Tendsto (fun N : ℕ => ((N:ℝ)+1)⁻¹ * B) atTop (𝓝 0) := by
    simpa only [zero_mul,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop))).mul_const B
  exact abs_nonpos_iff.mp (ge_of_tendsto ht
    (Filter.Eventually.of_forall fun N => hAll _ (by positivity)))

theorem radialForm_self_smul {n : ℕ} (S T : ℝ) (J : Phase n → End n)
    (x v : Phase n) (a : ℝ) :
    radialForm S T x (a • v) (J x (a • v)) = a^2 * radialForm S T x v (J x v) := by
  simp only [radialForm, ← stdOmega_apply, map_smul,
    smul_apply, smul_eq_mul]
  ring

theorem radialForm_on_graph_continuous {n : ℕ} {S T : ℝ} (hST : S < T)
    {J : Phase n → End n} (hJ : Continuous J) :
    Continuous (fun y : Phase n × Phase n => radialForm S T y.1 y.2 (J y.1 y.2)) := by
  have hc : Continuous (fun y : Phase n × Phase n => capacity y.1) :=
    (capacity_smooth n).continuous.comp continuous_fst
  have hr := (radialCoefficient_smooth hST).continuous.comp hc
  have hs : Continuous (radialSlope S T) := by
    apply ((radialSwitch_smooth S T).continuous.neg).div
      ((continuous_const.add (radialOffset_smooth S T).continuous).pow 2)
    intro t
    exact pow_ne_zero 2 (ne_of_gt (show 0 < 1 + radialOffset S T t from by
      linarith [radialOffset_nonneg hST t]))
  have hj := (hJ.comp continuous_fst).clm_apply continuous_snd
  have ho (a b : Phase n × Phase n → Phase n) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun y => standardForm (a y) (b y)) := by
    simpa only [Function.comp_apply,stdOmega_apply] using ((stdOmega n).continuous.comp ha).clm_apply hb
  have hd (a b : Phase n × Phase n → Phase n) (ha : Continuous a) (hb : Continuous b) :
      Continuous (fun y => stdDot n (a y) (b y)) :=
    ((stdDot n).continuous.comp ha).clm_apply hb
  exact (hr.mul (ho _ _ continuous_snd hj)).add
    ((continuous_const.mul (hs.comp hc)).mul
      (((hd _ _ continuous_fst continuous_snd).mul (ho _ _ continuous_fst hj)).sub
        ((hd _ _ continuous_fst hj).mul (ho _ _ continuous_fst continuous_snd))))

 
theorem radialForm_compact_coercive {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {J : Phase n → End n} (hJs : Continuous J) (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, S < capacity x → J x = standardJ n)
    {K : Set (Phase n)} (hK : IsCompact K) :
    ∃ c > 0, ∀ x ∈ K, ∀ v : Phase n,
      c * ‖v‖^2 ≤ radialForm S T x v (J x v) := by
  let L := K ×ˢ Metric.sphere (0 : Phase n) 1
  have hL : IsCompact L := hK.prod (isCompact_sphere _ _)
  have hnormalize {x : Phase n} (hx : x ∈ K) {v : Phase n} (hv : v ≠ 0) :
      (x, ‖v‖⁻¹ • v) ∈ L := by
    refine ⟨hx, ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  by_cases hne : L.Nonempty
  · obtain ⟨y,hy,hmin⟩ := hL.exists_isMinOn hne
      (radialForm_on_graph_continuous hST hJs).continuousOn
    have hyv : y.2 ≠ 0 := by
      intro he
      have hh := hy.2
      simp [he] at hh
    have hp := radialForm_adapted_pos hST hT hJ houtside y.1 hyv
    refine ⟨_,hp,?_⟩
    intro x hx v
    by_cases hv : v = 0
    · simp [hv,radialForm, ← stdOmega_apply]
    have hm := hmin (hnormalize hx hv)
    change radialForm S T y.1 y.2 (J y.1 y.2) ≤
      radialForm S T x (‖v‖⁻¹ • v) (J x (‖v‖⁻¹ • v)) at hm
    rw [radialForm_self_smul] at hm
    have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hh := (mul_le_mul_of_nonneg_right hm hn.le)
    have he : (‖v‖⁻¹)^2 * radialForm S T x v (J x v) * ‖v‖^2 =
        radialForm S T x v (J x v) := by
      field_simp
    rw [he] at hh
    exact hh
  · refine ⟨1,by norm_num,?_⟩
    intro x hx v
    have hv : v = 0 := by
      by_contra hv
      exact hne ⟨_,hnormalize hx hv⟩
    simp [hv,radialForm, ← stdOmega_apply]

theorem planarCR_opNorm_bound {n : ℕ} (D : Plane →L[ℝ] Phase n) (A : End n)
    (hD : D (0,1) = A (D (1,0))) :
    ‖D‖ ≤ (1 + ‖A‖) * ‖D (1,0)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hw : w = w.1 • ((1,0) : Plane) + w.2 • ((0,1) : Plane) := by ext <;> simp
  calc
    ‖D w‖ = ‖w.1 • D (1,0) + w.2 • A (D (1,0))‖ := by
      conv_lhs => rw [hw, map_add, map_smul, map_smul, hD]
    _ ≤ ‖w.1‖ * ‖D (1,0)‖ + ‖w.2‖ * ‖A (D (1,0))‖ := by
      simpa only [norm_smul] using norm_add_le (w.1 • D (1,0)) (w.2 • A (D (1,0)))
    _ ≤ ‖w‖ * ‖D (1,0)‖ + ‖w‖ * (‖A‖ * ‖D (1,0)‖) :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_fst_le w) (norm_nonneg _))
        (mul_le_mul (norm_snd_le w) (A.le_opNorm _) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

 

theorem curvePrimitive_sq_integrable_of_compact_image {n : ℕ} {S T : ℝ}
    (hST : S < T) (hT : T < 1) {J : Phase n → End n}
    (hJs : Continuous J) (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, S < capacity x → J x = standardJ n)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (hh : ∀ z, PseudoHolomorphicAt J u z)
    {K : Set (Phase n)} (hK : IsCompact K) (huK : ∀ z, u z ∈ K)
    (hE : Integrable (curveDensity S T u)) :
    Integrable (fun z => ‖curvePrimitive S T u z‖^2) := by
  obtain ⟨c,hc,hcoerc⟩ := radialForm_compact_coercive hST hT hJs hJ houtside hK
  obtain ⟨A,hA,hAb⟩ := (hK.image (radialPrimitiveCLM_smooth hST).continuous).isBounded.exists_pos_norm_le
  obtain ⟨B,hB,hBb⟩ := (hK.image hJs).isBounded.exists_pos_norm_le
  let C := (A * (1 + B))^2 / c
  have hb (z : Plane) : ‖curvePrimitive S T u z‖^2 ≤ C * curveDensity S T u z := by
    have hzk : realCurve u z ∈ K := huK _
    have hpa : ‖radialPrimitiveCLM S T (realCurve u z)‖ ≤ A :=
      hAb _ (mem_image_of_mem _ hzk)
    have hjb : ‖J (realCurve u z)‖ ≤ B := hBb _ (mem_image_of_mem _ hzk)
    have hd := planarCR_opNorm_bound (fderiv ℝ (realCurve u) z)
      (J (realCurve u z)) (realCurve_CR (hh _))
    have hden : c * ‖fderiv ℝ (realCurve u) z (1,0)‖^2 ≤ curveDensity S T u z := by
      unfold curveDensity
      rw [realCurve_CR (hh _)]
      exact hcoerc _ hzk _
    have hpr : ‖curvePrimitive S T u z‖ ≤ A * (1+B) * ‖fderiv ℝ (realCurve u) z (1,0)‖ := by
      calc
        _ ≤ ‖radialPrimitiveCLM S T (realCurve u z)‖ * ‖fderiv ℝ (realCurve u) z‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ A * ((1+B) * ‖fderiv ℝ (realCurve u) z (1,0)‖) :=
          mul_le_mul hpa (hd.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
            (norm_nonneg _) hA.le
        _ = _ := by ring
    have hsq := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hpr
    dsimp [C]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg (A*(1+B)))
    nlinarith [sq_nonneg (A*(1+B)), sq_nonneg ‖fderiv ℝ (realCurve u) z (1,0)‖]
  apply (hE.const_mul C).mono'
    (((curvePrimitive_smooth hST hu).continuous.norm).pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change ‖‖curvePrimitive S T u z‖^2‖ ≤ C * curveDensity S T u z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hb z

 

theorem compact_image_finite_energy_constant {n : ℕ} {S T : ℝ}
    (hST : S < T) (hT : T < 1) {J : Phase n → End n}
    (hJs : Continuous J) (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, S < capacity x → J x = standardJ n)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (hh : ∀ z, PseudoHolomorphicAt J u z)
    {K : Set (Phase n)} (hK : IsCompact K) (huK : ∀ z, u z ∈ K)
    (hE : Integrable (curveDensity S T u)) : ∀ z, u z = u 0 := by
  have hβ2 := curvePrimitive_sq_integrable_of_compact_image hST hT hJs hJ houtside hu hh hK huK hE
  have hcurl : planarCurl (curvePrimitive S T u) = curveDensity S T u :=
    funext (curvePrimitive_curl hST hu)
  have he := integral_planarCurl_zero_of_sq_integrable (curvePrimitive_smooth hST hu)
    (by simpa only [hcurl] using hE) hβ2
  rw [hcurl] at he
  have hpos := curveDensity_nonneg hST hT hJ houtside hh
  have hden0 : curveDensity S T u = 0 :=
    ((curveDensity_smooth hST hu).continuous.ae_eq_iff_eq volume continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg hpos hE).mp he)
  have hd1 (z : Plane) : fderiv ℝ (realCurve u) z (1,0) = 0 := by
    by_contra hn
    have hp := radialForm_adapted_pos hST hT hJ houtside (realCurve u z) hn
    have hz : curveDensity S T u z = 0 := congrFun hden0 z
    unfold curveDensity at hz
    rw [realCurve_CR (hh _)] at hz
    linarith
  have hd (z : Plane) : fderiv ℝ (realCurve u) z = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : w = w.1 • ((1,0) : Plane) + w.2 • ((0,1) : Plane) := by ext <;> simp
    rw [hw, map_add, map_smul, map_smul, hd1, realCurve_CR (hh _), hd1, map_zero]
    simp
  intro z
  have hz := is_const_of_fderiv_eq_zero ((realCurve_smooth hu).differentiable (by simp))
    hd (Complex.equivRealProdCLM z) 0
  simpa only [realCurve, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, map_zero] using hz

end HigherDimensionalBallPacking.Rigidity

end

end OAI
