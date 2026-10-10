import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.KernelBounds

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open scoped ENNReal
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Set ExactSLEGenerator ExactSLEMain ExactSLEKernel
open scoped Classical NNReal ENNReal
theorem actual_mass_moment_bound (a : ℝ) (ha : 1/4<a) (m : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
    IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
    ∀ (K : Set ℂ), MeasurableSet K → Bornology.IsBounded K →
    ∀ c : ℝ, 0<c → (∀ z∈K, c≤2*z.im) →
    ∀ f : ℂ → ℝ, Measurable f → (∀ z∈K, 0≤f z) →
    (∃ B : ℝ, 0≤B ∧ ∀ z∈K, f z≤B) →
    let A := ∫⁻ x : Fin m → ℂ, (∏ i, ENNReal.ofReal (f (x i))) * kernel (alpha a) c x
      ∂Measure.pi (fun _ => volume.restrict K)
    A<∞ ∧ ∀ q : ℝ, 0<q → q≤1 →
      (∫⁻ b, (∫⁻ z in K, ENNReal.ofReal (f z)*massDensity a q b z)^m ∂W) ≤
        ENNReal.ofReal C*A := by
  obtain ⟨C,hC,hCb⟩ := actual_density_product_bound a ha m
  refine ⟨C,hC,?_⟩
  intro W hprob hW K hK hKb c hc hcK f hf hf0 hfB
  obtain ⟨B,hB,hBf⟩ := hfB
  let μ := volume.restrict K
  let ν := Measure.pi (fun _ : Fin m => μ)
  have hKae : ∀ᵐ x ∂ν, ∀ i, x i∈K := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin m => μ) (i:=i)).eventually (ae_restrict_mem hK)
  have halpha : alpha a<1 := by
    have ha0 : 0<a := by linarith
    have hp : 0<1/(4*a) := by positivity
    dsimp [alpha]; linarith
  have hkfin := capped_distance_kernel_integral (alpha a) c (alpha_pos ha) halpha hc m K hK hKb
  have hkm := measurable_kernel (alpha_pos ha).le c (ι:=Fin m)
  have hAfin : (∫⁻ x, (∏ i, ENNReal.ofReal (f (x i))) * kernel (alpha a) c x ∂ν)<∞ := by
    calc
      _ ≤ ∫⁻ x, (ENNReal.ofReal B)^m * kernel (alpha a) c x ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hKae] with x hx
        apply mul_le_mul' _ le_rfl
        have hp := Finset.prod_le_prod₀ (fun _ _ => (bot_le : (0:ℝ≥0∞)≤_))
          (fun i (_ : i∈Finset.univ) => ENNReal.ofReal_le_ofReal (hBf (x i) (hx i)))
        simpa using hp
      _ = (ENNReal.ofReal B)^m * ∫⁻ x, kernel (alpha a) c x ∂ν := lintegral_const_mul _ hkm
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hkfin
  refine ⟨hAfin,?_⟩
  intro q hq hq1
  have hd := massDensity_measurable a ha q hq hq1
  have hdz (b : ExactSLEGenerator.Driver) : Measurable (massDensity a q b) := hd.comp (measurable_const.prodMk measurable_id)
  have hdm (x : Fin m → ℂ) : Measurable (fun b => ∏ i, massDensity a q b (x i)) := by
    apply Finset.measurable_prod
    intro i hi
    exact hd.comp (measurable_id.prodMk measurable_const)
  have hprod (x : Fin m → ℂ) (hx : ∀ i,x i∈K) :
      (∫⁻ b, ∏ i, massDensity a q b (x i) ∂W) ≤ ENNReal.ofReal C*kernel (alpha a) c x := by
    have hz (i) : 0<(x i).im := by have := hcK (x i) (hx i); linarith
    by_cases hinj : Function.Injective x
    · let cap := fun i => cappedDistance c x i
      let target := fun i => 2*(x i).im*q
      have hcap (i) : 0<cap i := cappedDistance_pos hc x hinj i
      have ht (i) : 0<target i ∧ target i≤2*(x i).im := by
        refine ⟨mul_pos (mul_pos (by norm_num) (hz i)) hq,?_⟩
        dsimp [target]
        nlinarith [hz i]
      have hh := hCb W hW x hinj hz cap target
        (fun i => ⟨hcap i,(cappedDistance_le c x i).trans (hcK (x i) (hx i))⟩)
        (fun i j hij => by simpa [dist_eq_norm] using cappedDistance_le_dist c x i j hij.symm) ht
      have he (b : ExactSLEGenerator.Driver) (i) : massDensity a q b (x i)=
          ENNReal.ofReal (fullRadialDensity a b.1 (x i) (target i)) := by simp [massDensity,hz i,target]
      simp_rw [he]
      have hk : ENNReal.ofReal (C*∏ i, cap i^(-alpha a))=ENNReal.ofReal C*kernel (alpha a) c x := by
        rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hcap i).le _)]
        congr 1
        unfold kernel
        apply Finset.prod_congr rfl
        intro i hi
        exact (ENNReal.ofReal_rpow_of_pos (hcap i)).symm
      exact hh.trans_eq hk
    · rw [kernel_top_of_not_injective (alpha a) c (alpha_pos ha) hc x hinj,
        ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC))]
      exact le_top
  have hjoint : Measurable (fun p : ExactSLEGenerator.Driver × (Fin m → ℂ) =>
      ∏ i, ENNReal.ofReal (f (p.2 i))*massDensity a q p.1 (p.2 i)) := by
    apply Finset.measurable_prod
    intro i hi
    exact ((hf.comp ((measurable_pi_apply i).comp measurable_snd)).ennreal_ofReal).mul
      (hd.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  calc
    _ = ∫⁻ b, ∫⁻ x : Fin m → ℂ, ∏ i, ENNReal.ofReal (f (x i))*massDensity a q b (x i) ∂ν ∂W := by
      apply lintegral_congr
      intro b
      exact lintegral_power_pi μ _ (hf.ennreal_ofReal.mul (hdz b)) m
    _ = ∫⁻ x : Fin m → ℂ, ∫⁻ b, ∏ i, ENNReal.ofReal (f (x i))*massDensity a q b (x i) ∂W ∂ν :=
      lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal C*((∏ i, ENNReal.ofReal (f (x i)))*kernel (alpha a) c x) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hKae] with x hx
      simp_rw [Finset.prod_mul_distrib]
      rw [lintegral_const_mul _ (hdm x)]
      calc
        _ ≤ (∏ i, ENNReal.ofReal (f (x i)))*(ENNReal.ofReal C*kernel (alpha a) c x) := mul_le_mul' le_rfl (hprod x hx)
        _ = _ := by ring
    _ = _ := by
      have hfm : Measurable (fun x : Fin m → ℂ => ∏ i, ENNReal.ofReal (f (x i))) := by fun_prop
      exact lintegral_const_mul _ (hfm.mul hkm)
end ExactSLEGreen

open Filter Topology
noncomputable section
namespace ExactSLEMassExtraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem closed_convex_tail_intersection (X : ℕ → E)
    (C : ℝ) (hX : ∀ j, ‖X j‖ ≤ C) :
    ∃ v, ∀ k, v ∈ closure (convexHull ℝ (X '' Set.Ici k)) := by
  let K := fun k => closure (convexHull ℝ (X '' Set.Ici k))
  have hne (k) : (K k).Nonempty :=
    ⟨X k, subset_closure (subset_convexHull ℝ _ ⟨k, Set.mem_Ici.mpr le_rfl, rfl⟩)⟩
  have hcv (k) : Convex ℝ (K k) := (convex_convexHull ℝ _).closure
  have hcl (k) : IsClosed (K k) := isClosed_closure
  have hanti : Antitone K := by
    intro k l hkl
    exact closure_mono (convexHull_mono (Set.image_mono (Set.Ici_subset_Ici.mpr hkl)))
  have hex (k) := exists_norm_eq_iInf_of_complete_convex (hne k) (hcl k).isComplete (hcv k) (0 : E)
  choose y hy hmin using hex
  have hle (k) (w) (hw : w ∈ K k) : ‖y k‖ ≤ ‖w‖ := by
    have hb : BddBelow (Set.range (fun w : K k => ‖(0 : E) - w‖)) :=
      ⟨0, by rintro _ ⟨i, rfl⟩; exact norm_nonneg _⟩
    have := ciInf_le hb (⟨w, hw⟩ : K k)
    rw [← hmin] at this
    simpa using this
  have hbd (k) : ‖y k‖ ≤ C :=
    (hle k (X k) (subset_closure (subset_convexHull ℝ _ ⟨k, Set.mem_Ici.mpr le_rfl, rfl⟩))).trans (hX k)
  have hm : Monotone (fun k => ‖y k‖ ^ 2) := by
    intro k l hkl
    exact pow_le_pow_left₀ (norm_nonneg _) (hle k _ (hanti hkl (hy l))) 2
  have hb : BddAbove (Set.range (fun k => ‖y k‖ ^ 2)) := by
    refine ⟨C ^ 2, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd k) 2
  have hdiff (k l) (hkl : k ≤ l) : ‖y l - y k‖ ^ 2 ≤ ‖y l‖ ^ 2 - ‖y k‖ ^ 2 := by
    have hi := (norm_eq_iInf_iff_real_inner_le_zero (hcv k) (hy k)).mp (hmin k)
      (y l) (hanti hkl (hy l))
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
    rw [norm_sub_sq_real, ← real_inner_comm (y l) (y k)]
    linarith
  have hcy : CauchySeq y := by
    have hc := (tendsto_atTop_ciSup hm hb).cauchySeq
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hmn := hN m hm n hn
    rw [Real.dist_eq, abs_sub_lt_iff] at hmn
    rw [dist_eq_norm]
    rcases le_total m n with h | h
    · have := hdiff m n h
      rw [norm_sub_rev (y n) (y m)] at this
      nlinarith [norm_nonneg (y m - y n)]
    · have := hdiff n m h
      nlinarith [norm_nonneg (y m - y n)]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcy
  refine ⟨v, fun k => (hcl k).mem_of_tendsto hv ?_⟩
  exact (eventually_ge_atTop k).mono fun n hn => hanti hn (hy n)

omit [CompleteSpace E] in
theorem convex_tail_coefficients (X : ℕ → E) (k : ℕ) (v : E)
    (hv : v ∈ convexHull ℝ (X '' Set.Ici k)) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ),
      (∀ j ∈ s, k ≤ j) ∧ (∀ j ∈ s, 0 ≤ c j) ∧
      (∑ j ∈ s, c j = 1) ∧ ∑ j ∈ s, c j • X j = v := by
  classical
  obtain ⟨ι, inst, w, z, hw, hw1, hz, hzv⟩ := mem_convexHull_iff_exists_fintype.mp hv
  choose f hf hzf using hz
  let s := Finset.univ.image f
  let c := fun j => ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i
  have hmap : ∀ i ∈ (Finset.univ : Finset ι), f i ∈ s := by simp [s]
  refine ⟨s, c, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact hf i
  · intro j _
    exact Finset.sum_nonneg fun i _ => hw i
  · exact (Finset.sum_fiberwise_of_maps_to hmap w).trans hw1
  · calc
      ∑ j ∈ s, c j • X j = ∑ j ∈ s, ∑ i ∈ Finset.univ.filter (fun i => f i = j), w i • z i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show c j = _ from rfl, Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        rw [← hzf i, (Finset.mem_filter.mp hi).2]
      _ = ∑ i, w i • z i := Finset.sum_fiberwise_of_maps_to hmap _
      _ = v := hzv

theorem convex_tails_hilbert (X : ℕ → E)
    (hX : ∃ C : ℝ, ∀ j, ‖X j‖ ≤ C) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (v : E),
      (∀ k j, j ∈ s k → k ≤ j) ∧
      (∀ k j, j ∈ s k → 0 ≤ c k j) ∧
      (∀ k, ∑ j ∈ s k, c k j = 1) ∧
      Tendsto (fun k => ∑ j ∈ s k, c k j • X j) atTop (𝓝 v) := by
  rcases hX with ⟨C, hC⟩
  obtain ⟨v, hv⟩ := closed_convex_tail_intersection X C hC
  have hex (k) := Metric.mem_closure_iff.mp (hv k) (1 / ((k : ℝ) + 1)) (by positivity)
  choose u hu hdist using hex
  have hcoef (k) := convex_tail_coefficients X k (u k) (hu k)
  choose s c hs hc hsum heq using hcoef
  refine ⟨s, c, v, hs, hc, hsum, ?_⟩
  have ht : Tendsto (fun k => dist (u k) v) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun k => dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro k
    rw [dist_comm]
    exact (hdist k).le
  simpa only [heq] using (tendsto_iff_dist_tendsto_zero.mpr ht)

 

theorem common_convex_tails
    (X : ℕ → ℕ → E) (hX : ∀ i, ∃ C : ℝ, ∀ j, ‖X j i‖ ≤ C) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (v : ℕ → E),
      (∀ k j, j ∈ s k → k ≤ j) ∧
      (∀ k j, j ∈ s k → 0 ≤ c k j) ∧
      (∀ k, ∑ j ∈ s k, c k j = 1) ∧
      (∀ i, Tendsto (fun k => ∑ j ∈ s k, c k j • X j i) atTop (𝓝 (v i))) := by
  classical
  choose C hC using hX
  have hC0 (i) : 0 ≤ C i := (norm_nonneg (X 0 i)).trans (hC i 0)
  let w := fun i => (1 / 2 : ℝ) ^ i / (C i + 1)
  have hw (i) : 0 < w i := div_pos (pow_pos (by norm_num) _) (by linarith [hC0 i])
  have hnorm (j i) : ‖w i • X j i‖ ≤ (1 / 2 : ℝ) ^ i := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hw i)]
    change (1 / 2 : ℝ) ^ i / (C i + 1) * ‖X j i‖ ≤ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith [hC0 i])]
    exact mul_le_mul_of_nonneg_left (by linarith [hC i j]) (by positivity)
  have hsq (j i) : ‖w i • X j i‖ ^ 2 ≤ (1 / 2 : ℝ) ^ i := by
    have hu : (1 / 2 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp : 0 ≤ (1 / 2 : ℝ) ^ i := by positivity
    have hn := hnorm j i
    nlinarith [norm_nonneg (w i • X j i)]
  have hsumm (j) : Summable (fun i => ‖w i • X j i‖ ^ 2) :=
    .of_nonneg_of_le (fun _ => sq_nonneg _) (hsq j)
      (summable_geometric_of_abs_lt_one (by norm_num))
  let Y : ℕ → lp (fun _ : ℕ => E) 2 :=
    fun j => ⟨fun i => w i • X j i, memℓp_gen (by simpa using hsumm j)⟩
  have hY : ∀ j, ‖Y j‖ ≤ 2 := by
    intro j
    apply lp.norm_le_of_tsum_le (by norm_num) (by norm_num)
    change ∑' i, ‖w i • X j i‖ ^ (2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ)
    simp only [Real.rpow_two]
    have hh := (hsumm j).tsum_le_tsum (hsq j)
      (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
    have he : ∑' i : ℕ, (1 / 2 : ℝ) ^ i = 2 := by
      rw [tsum_geometric_of_abs_lt_one (by norm_num)]
      norm_num
    change ∑' i, ‖w i • X j i‖ ^ 2 ≤ 2 ^ 2
    rw [he] at hh
    linarith
  obtain ⟨s, c, v, hs, hc, hsum, ht⟩ := convex_tails_hilbert Y ⟨2, hY⟩
  refine ⟨s, c, fun i => (w i)⁻¹ • v i, hs, hc, hsum, fun i => ?_⟩
  have he := ((lp.evalCLM ℝ (fun _ : ℕ => E) 2 i).continuous.tendsto v).comp ht
  have him := he.const_smul ((w i)⁻¹)
  convert him using 1
  · ext k
    simp only [Function.comp_apply, map_sum, map_smul]
    change ∑ j ∈ s k, c k j • X j i =
      (w i)⁻¹ • ∑ j ∈ s k, c k j • (w i • X j i)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← smul_assoc, smul_smul]
    have hh : (w i)⁻¹ * c k j * w i = c k j := by
      field_simp [(hw i).ne']
    rw [smul_eq_mul, hh]
  · rfl

open MeasureTheory
open scoped ENNReal

theorem simultaneous_ae_subsequence {Ω F : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace F] (μ : Measure Ω) (f : ℕ → ℕ → Ω → F) (g : ℕ → Ω → F)
    (hf : ∀ i, TendstoInMeasure μ (fun n => f n i) atTop (g i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => f (ns n) i ω) atTop (𝓝 (g i ω)) := by
  classical
  let r := fun i => ExistsSeqTendstoAe.seqTendstoAeSeq (hf i)
  have hr (i) : StrictMono (r i) := ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono (hf i)
  let b := fun n => (Finset.range (n+1)).sup (fun i => r i n)
  have hb (n i) (hi : i ≤ n) : r i n ≤ b n := by
    exact Finset.le_sup (f := fun i => r i n) (Finset.mem_range.mpr (by omega))
  have hbm : Monotone b := by
    intro n m hnm
    apply Finset.sup_le
    intro i hi
    exact ((hr i).monotone hnm).trans (hb m i (by simp only [Finset.mem_range] at hi; omega))
  let ns := fun n => n + b n
  have hns : StrictMono ns := by
    intro n m hnm
    have hm := hbm hnm.le
    dsimp [ns]
    omega
  refine ⟨ns, hns, ae_all_iff.mpr fun i => ?_⟩
  let S := fun n => {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f (ns (n+i)) i ω) (g i ω)}
  have hS (n) : μ (S n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    apply ExistsSeqTendstoAe.seqTendstoAeSeq_spec (hf i) n (ns (n+i))
    exact ((hr i).monotone (by omega : n ≤ n+i)).trans
      ((hb (n+i) i (by omega)).trans (Nat.le_add_left _ _))
  have hfin : (∑' n, μ (S n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hS)
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top (n := 2))
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  apply (tendsto_add_atTop_iff_nat i).mp
  apply EMetric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)).eventually (gt_mem_nhds hε))
  refine ⟨max N K, fun n hn => ?_⟩
  exact (not_le.mp (hN n ((le_max_left _ _).trans hn))).trans
    (hK n ((le_max_right _ _).trans hn))

theorem coe_Lp_sum_smul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ℕ) (c : ℕ → ℝ) (X : ℕ → Lp ℝ 2 μ) :
    (fun ω => (∑ j ∈ s, c j • X j) ω) =ᵐ[μ] (fun ω => ∑ j ∈ s, c j * X j ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
    exact hω
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (c j • X j) (∑ i ∈ s, c i • X i),
      Lp.coeFn_smul (c j) (X j), ih] with ω h1 h2 h3
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, h3] using h1

 
theorem common_L2_convex_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → ℕ → Lp ℝ 2 μ) (hX : ∀ i, ∃ C : ℝ, ∀ j, ‖X j i‖ ≤ C) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (v : ℕ → Lp ℝ 2 μ),
      (∀ k j, j ∈ s k → k ≤ j) ∧
      (∀ k j, j ∈ s k → 0 ≤ c k j) ∧
      (∀ k, ∑ j ∈ s k, c k j = 1) ∧
      (∀ i, Tendsto (fun k => ∑ j ∈ s k, c k j • X j i) atTop (𝓝 (v i))) ∧
      (∀ᵐ ω ∂μ, ∀ i,
        Tendsto (fun k => ∑ j ∈ s k, c k j * X j i ω) atTop (𝓝 (v i ω))) := by
  obtain ⟨s, c, v, hs, hc, hsum, ht⟩ := common_convex_tails X hX
  let f := fun k i ω => (∑ j ∈ s k, c k j • X j i) ω
  obtain ⟨ns, hns, hae⟩ := simultaneous_ae_subsequence μ f (fun i ω => v i ω)
    (fun i => tendstoInMeasure_of_tendsto_Lp (ht i))
  refine ⟨s ∘ ns, c ∘ ns, v, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j hj
    exact (hns.id_le k).trans (hs (ns k) j hj)
  · exact fun k => hc (ns k)
  · exact fun k => hsum (ns k)
  · exact fun i => (ht i).comp hns.tendsto_atTop
  · have he : ∀ᵐ ω ∂μ, ∀ k i, f (ns k) i ω = ∑ j ∈ s (ns k), c (ns k) j * X j i ω :=
      ae_all_iff.mpr fun k => ae_all_iff.mpr fun i => coe_Lp_sum_smul μ _ _ _
    filter_upwards [hae, he] with ω hω heω
    intro i
    simpa only [Function.comp_apply, ← heω] using hω i

end ExactSLEMassExtraction

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
end ExactSLEGreen
end
end

end OAI
