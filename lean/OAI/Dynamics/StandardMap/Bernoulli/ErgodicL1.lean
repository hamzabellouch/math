import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.ReverseTailProjection

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter BoundedSubadditive
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

noncomputable def orbitAverage (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  birkhoffSum T f n x/(n : ℝ)

omit [IsProbabilityMeasure μ] in
lemma orbitAverage_integrable {T : X → X} (hT : MeasurePreserving T μ μ)
    {f : X → ℝ} (hf : Integrable f μ) (n : ℕ) : Integrable (orbitAverage T f n) μ := by
  exact (integrable_finsetSum _ (fun i _ => (hT.iterate i).integrable_comp_of_integrable hf)).div_const _

omit [MeasurableSpace X] in
lemma orbitAverage_sub (T : X → X) (f g : X → ℝ) (n : ℕ) (x : X) :
    orbitAverage T (f-g) n x=orbitAverage T f n x-orbitAverage T g n x := by
  simp only [orbitAverage,birkhoffSum,Pi.sub_apply,Finset.sum_sub_distrib,sub_div]

omit [MeasurableSpace X] in
lemma orbitAverage_abs_le (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    |orbitAverage T f n x|≤orbitAverage T (fun y => |f y|) n x := by
  rw [orbitAverage,abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ)≤n)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma integral_orbitAverage {T : X → X} (hT : MeasurePreserving T μ μ)
    {f : X → ℝ} (hf : Integrable f μ) {n : ℕ} (hn : 0<n) :
    (∫ x,orbitAverage T f n x ∂μ)=∫ x,f x ∂μ := by
  have him (i : ℕ) : Integrable (fun x => f (T^[i] x)) μ := (hT.iterate i).integrable_comp_of_integrable hf
  simp only [orbitAverage,birkhoffSum]
  rw [integral_div,integral_finsetSum _ (fun i _ => him i)]
  simp only [BoundedSubadditive.integral_comp (hT.iterate _) hf.aestronglyMeasurable,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')

omit [IsProbabilityMeasure μ] in
lemma orbitAverage_L1_contraction {T : X → X} (hT : MeasurePreserving T μ μ)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {n : ℕ} (hn : 0<n) :
    (∫ x,|orbitAverage T f n x-orbitAverage T g n x| ∂μ)≤∫ x,|f x-g x| ∂μ := by
  simp_rw [←orbitAverage_sub]
  calc
    _≤∫ x,orbitAverage T (fun y => |(f-g) y|) n x ∂μ :=
      integral_mono (orbitAverage_integrable hT (hf.sub hg) n).abs
        (orbitAverage_integrable hT (hf.sub hg).abs n) (orbitAverage_abs_le T (f-g) n)
    _=_ := integral_orbitAverage hT (hf.sub hg).abs hn

theorem ergodic_L1_unit {T : X → X} (hT : Ergodic T μ)
    {g : X → ℝ} (hg : Measurable g) (h0 : ∀ x,0≤g x) (h1 : ∀ x,g x≤1) :
    Tendsto (fun n => ∫ x,|orbitAverage T g n x-(∫ y,g y ∂μ)| ∂μ) atTop (𝓝 0) := by
  obtain ⟨G,hGm,hGb,hGT,hGconv,hGint⟩ := exists_bounded_birkhoff_limit hT.toMeasurePreserving hg h0 h1
  obtain ⟨c,hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hGm.aestronglyMeasurable
    (Filter.Eventually.of_forall hGT)
  have hmean : c=∫ x,g x ∂μ := by
    have hh := hGint univ MeasurableSet.univ preimage_univ
    rw [setIntegral_univ,setIntegral_univ,integral_congr_ae hc] at hh
    simpa using hh
  have gi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (h0 x)]; exact h1 x))
  have hm0 : 0≤∫ x,g x ∂μ := integral_nonneg h0
  have hm1 : (∫ x,g x ∂μ)≤1 := by
    simpa using integral_mono gi (integrable_const (1 : ℝ)) h1
  let f := observationCocycle g hT.toMeasurePreserving.measurable hg h0 h1
  have ha (n : ℕ) (x : X) : 0≤orbitAverage T g n x ∧ orbitAverage T g n x≤1 := f.average_bounds n x
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => |orbitAverage T g n x-(∫ y,g y ∂μ)|) μ :=
    ((f.measurable_average n).sub_const _).abs.aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ)) hmeas
    (integrable_const 1) (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_abs,abs_le]
      constructor <;> linarith [(ha n x).1,(ha n x).2])) (by
      filter_upwards [hGconv,hc] with x hx hxc
      have hGx : G x=∫ y,g y ∂μ := hxc.trans hmean
      have h := (hx.sub_const (∫ y,g y ∂μ)).abs
      simpa only [hGx,sub_self,abs_zero,orbitAverage] using h)
  simpa only [integral_zero] using ht

theorem ergodic_L1_bounded {T : X → X} (hT : Ergodic T μ)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0≤C) (hbound : ∀ x,|f x|≤C) :
    Tendsto (fun n => ∫ x,|orbitAverage T f n x-(∫ y,f y ∂μ)| ∂μ) atTop (𝓝 0) := by
  let d := 2*C+1
  have hd : 0<d := by dsimp [d]; positivity
  let g (x : X) := (f x+C)/d
  have hg : Measurable g := (hf.add_const C).div_const d
  have h0 (x : X) : 0≤g x := div_nonneg (by linarith [(abs_le.mp (hbound x)).1]) hd.le
  have h1 (x : X) : g x≤1 := by
    apply (div_le_one hd).mpr
    dsimp [d]
    linarith [(abs_le.mp (hbound x)).2]
  have fi : Integrable f μ := (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hmean : (∫ x,g x ∂μ)=((∫ x,f x ∂μ)+C)/d := by
    dsimp [g]
    rw [integral_div,integral_add fi (integrable_const C)]
    simp
  have hav (n : ℕ) (hn : 0<n) (x : X) :
      orbitAverage T f n x-(∫ y,f y ∂μ)=d*(orbitAverage T g n x-(∫ y,g y ∂μ)) := by
    have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    have he : birkhoffSum T g n x=(birkhoffSum T f n x+(n : ℝ)*C)/d := by
      simp only [birkhoffSum,g]
      rw [←Finset.sum_div,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [orbitAverage,orbitAverage,he,hmean]
    field_simp
    ring
  have ht := (ergodic_L1_unit hT hg h0 h1).const_mul d
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp_rw [hav n hn,abs_mul,abs_of_pos hd,integral_const_mul]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma ergodic_L1_error_bound {T : X → X} (hT : MeasurePreserving T μ μ)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {n : ℕ} (hn : 0<n) :
    (∫ x,|orbitAverage T f n x-(∫ y,f y ∂μ)| ∂μ)≤
      (∫ x,|f x-g x| ∂μ)+(∫ x,|orbitAverage T g n x-(∫ y,g y ∂μ)| ∂μ)+
      (∫ x,|f x-g x| ∂μ) := by
  have havf := orbitAverage_integrable hT hf n
  have havg := orbitAverage_integrable hT hg n
  have hi : Integrable (fun x => |orbitAverage T f n x-orbitAverage T g n x|) μ := (havf.sub havg).abs
  have hj : Integrable (fun x => |orbitAverage T g n x-(∫ y,g y ∂μ)|) μ := (havg.sub (integrable_const (∫ y,g y ∂μ))).abs
  have hij : Integrable (fun x => |orbitAverage T f n x-orbitAverage T g n x|+|orbitAverage T g n x-(∫ y,g y ∂μ)|) μ := hi.add hj
  have hc : |(∫ y,g y ∂μ)-(∫ y,f y ∂μ)|≤∫ x,|f x-g x| ∂μ := by
    rw [abs_sub_comm,←integral_sub hf hg]
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => f x-g x))
  calc
    _≤∫ x,|orbitAverage T f n x-orbitAverage T g n x|+
        |orbitAverage T g n x-(∫ y,g y ∂μ)|+|(∫ y,g y ∂μ)-(∫ y,f y ∂μ)| ∂μ := by
      apply integral_mono (havf.sub (integrable_const _)).abs ((hi.add hj).add (integrable_const _))
      intro x
      exact (abs_sub_le _ (∫ y,g y ∂μ) _).trans
        (add_le_add_left (abs_sub_le _ (orbitAverage T g n x) _) _)
    _=(∫ x,|orbitAverage T f n x-orbitAverage T g n x| ∂μ)+
        (∫ x,|orbitAverage T g n x-(∫ y,g y ∂μ)| ∂μ)+|(∫ y,g y ∂μ)-(∫ y,f y ∂μ)| := by
      rw [integral_add hij (integrable_const _),integral_add hi hj]
      simp
    _≤_ := add_le_add (add_le_add_left (orbitAverage_L1_contraction hT hf hg hn) _) hc

theorem ergodic_L1 {T : X → X} (hT : Ergodic T μ) {f : X → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x,|orbitAverage T f n x-(∫ y,f y ∂μ)| ∂μ) atTop (𝓝 0) := by
  classical
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => ha.trans_le (integral_nonneg (fun _ => abs_nonneg _)))
  intro ε hε
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt
    (by simp : (1 : ℝ≥0∞)≠⊤) (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0<ε/4)))
  have gi : Integrable g μ := memLp_one_iff_integrable.mp hgm
  have hi : ∫ x,|f x-g x| ∂μ<ε/4 := by
    simp_rw [←Real.norm_eq_abs]
    change (∫ x,‖(f-⇑g) x‖ ∂μ)<ε/4
    rw [integral_norm_eq_lintegral_enorm (hf.sub gi).aestronglyMeasurable]
    rw [eLpNorm_one_eq_lintegral_enorm (hf.sub gi).aestronglyMeasurable] at hg
    exact ENNReal.toReal_lt_of_lt_ofReal hg
  let C := ∑ y∈g.range,|y|
  have hC : 0≤C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb (x : X) : |g x|≤C := Finset.single_le_sum (fun _ _ => abs_nonneg _) (g.mem_range_self x)
  have ht := (ergodic_L1_bounded hT g.measurable hC hb).eventually (gt_mem_nhds (by linarith : 0<ε/2))
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  have hh := ergodic_L1_error_bound hT.toMeasurePreserving hf gi hn0
  linarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X : Type*} [MeasurableSpace X]

noncomputable def cesaroLawMass (e : X ≃ᵐ X) (η : Measure X) (N : ℕ) (D : Set X) : ℝ :=
  (∑ i∈Finset.range N,(η.map (e^[i])).real D)/(N : ℝ)

lemma iterateLawMass_density (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (hac : η≪μ) (i : ℕ)
    {D : Set X} (hD : MeasurableSet D) :
    (η.map (e^[i])).real D=∫ x in D,(η.rnDeriv μ (e.symm^[i] x)).toReal ∂μ := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hcomp (x : X) : f (e.symm^[i] (e^[i] x))=f x :=
    congrArg f ((show Function.LeftInverse (e.symm : X → X) e from e.symm_apply_apply).iterate i x)
  have hemb : MeasurableEmbedding (e^[i]) := by
    simpa only [funext (iterateEquiv_apply e i)] using (iterateEquiv e i).measurableEmbedding
  change (η.map (e^[i])).real D=∫ x in D,f (e.symm^[i] x) ∂μ
  rw [Measure.real,Measure.map_apply (e.measurable.iterate i) hD]
  calc
    _=∫ x in (e^[i]) ⁻¹' D,f x ∂μ := (setIntegral_toReal_rnDeriv hac _).symm
    _=∫ x in (e^[i]) ⁻¹' D,f (e.symm^[i] (e^[i] x)) ∂μ := by simp only [hcomp]
    _=_ := (he.iterate i).setIntegral_preimage_emb hemb (fun x => f (e.symm^[i] x)) D

lemma cesaroLawMass_density (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (hac : η≪μ) (N : ℕ)
    {D : Set X} (hD : MeasurableSet D) :
    cesaroLawMass e η N D=∫ x in D,orbitAverage e.symm (fun y => (η.rnDeriv μ y).toReal) N x ∂μ := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hf : Integrable f μ := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr (integrable_const 1)
  have hi (i : ℕ) : Integrable (fun x => f (e.symm^[i] x)) (μ.restrict D) :=
    (((he.symm e).iterate i).integrable_comp_of_integrable hf).integrableOn
  simp only [cesaroLawMass,iterateLawMass_density μ η e he hac _ hD,orbitAverage,birkhoffSum]
  rw [integral_div,integral_finsetSum _ (fun i _ => hi i)]

theorem cesaro_ac_uniform (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (hac : η≪μ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,0<N ∧ ∀ D : Set X,MeasurableSet D →
      |cesaroLawMass e η N D-μ.real D|<ε := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hf : Integrable f μ := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr (integrable_const 1)
  have hmean : ∫ x,f x ∂μ=1 := by simpa only [f,Measure.real,measure_univ,ENNReal.toReal_one] using integral_toReal_rnDeriv hac
  have ht := (ergodic_L1 he.symm hf).eventually (gt_mem_nhds hε)
  filter_upwards [ht,eventually_gt_atTop 0] with N hN hN0
  refine ⟨hN0,fun D hD => ?_⟩
  rw [cesaroLawMass_density μ η e he.toMeasurePreserving hac N hD]
  have hmu : μ.real D=∫ _x : X in D,(1 : ℝ) ∂μ := by simp
  rw [hmu,←integral_sub (orbitAverage_integrable he.symm.toMeasurePreserving hf N).integrableOn (integrable_const 1)]
  exact (abs_setIntegral_le_L1 μ ((orbitAverage_integrable he.symm.toMeasurePreserving hf N).sub (integrable_const 1)) D).trans_lt
    (by simpa only [Pi.sub_apply,hmean] using hN)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

omit [MeasurableSpace A] in
lemma remotePair_translate (e : X ≃ᵐ X) (α : X → A) (n i : ℕ) :
    remotePair e e.symm α (n+i) ∘ e^[i]=
      (Prod.map id (dropName (2*i))) ∘ remotePair e e.symm α n := by
  funext x
  apply Prod.ext
  · funext j
    change α (e.symm^[j+(n+i)] (e^[i] x))=α (e.symm^[j+n] x)
    rw [←Nat.add_assoc,Function.iterate_add_apply]
    rw [(show Function.LeftInverse (e.symm : X → X) e from e.symm_apply_apply).iterate i x]
  · funext j
    change α (e^[j+(n+i)] (e^[i] x))=α (e^[(j+2*i)+n] x)
    rw [←Function.iterate_add_apply]
    congr 2
    omega

lemma remoteProduct_drop (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {α : X → A} (hα : Measurable α) (i : ℕ) :
    (remoteProductLaw μ e e.symm α).map (Prod.map id (dropName i))=
      remoteProductLaw μ e e.symm α := by
  have : IsProbabilityMeasure (μ.map (tailName e.symm α 0)) := inferInstance
  have : IsProbabilityMeasure (μ.map (tailName e α 0)) := inferInstance
  rw [remoteProductLaw,←Measure.map_prod_map _ _ measurable_id (measurable_dropName i),Measure.map_id,
    stationary_drop_law μ he hα i]

lemma RemoteIndependent.translate {μ η : Measure X} [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {α : X → A} (hα : Measurable α)
    (h : RemoteIndependent μ η e e.symm α) (i : ℕ) :
    RemoteIndependent μ (η.map (e^[i])) e e.symm α := by
  intro ε hε
  have ht := (tendsto_sub_atTop_nat i).eventually (h ε hε)
  filter_upwards [ht,eventually_ge_atTop i] with n hn hni
  have hc := hn.map (measurable_id.prodMap (measurable_dropName (2*i)))
  rw [remoteProduct_drop μ e he hα (2*i)] at hc
  rw [Measure.map_map (measurable_id.prodMap (measurable_dropName (2*i)))
    (measurable_remotePair e.measurable e.symm.measurable hα (n-i))] at hc
  rw [←remotePair_translate e α (n-i) i,Nat.sub_add_cancel hni] at hc
  rw [Measure.map_map (measurable_remotePair e.measurable e.symm.measurable hα n) (e.measurable.iterate i)]
  exact hc

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma cesaroLawMass_close (e : X ≃ᵐ X) (η : Measure X) {N : ℕ} (hN : 0<N)
    (D : Set X) {b δ : ℝ} (h : ∀ i∈Finset.range N,|(η.map (e^[i])).real D-b|≤δ) :
    |cesaroLawMass e η N D-b|≤δ := by
  have hN' : (0 : ℝ)<N := by exact_mod_cast hN
  have heq : cesaroLawMass e η N D-b=
      (∑ i∈Finset.range N,((η.map (e^[i])).real D-b))/(N : ℝ) := by
    simp only [cesaroLawMass,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,sub_div]
    rw [mul_div_cancel_left₀ b hN'.ne']
  rw [heq,abs_div,abs_of_pos hN']
  calc
    _≤(∑ i∈Finset.range N,|(η.map (e^[i])).real D-b|)/(N : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hN'.le
    _≤(∑ _i∈Finset.range N,δ)/(N : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum h) hN'.le
    _=δ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_div_cancel_left₀ δ hN'.ne']

theorem weakBernoulli_of_ac_remote (μ η : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (hac : η≪μ)
    {α : X → A} (hα : Measurable α) (h : RemoteIndependent μ η e e.symm α) :
    WeakBernoulliProcess μ e α := by
  intro ε hε
  have hh : 0<ε/2 := by linarith
  obtain ⟨N,hN,happrox⟩ := (cesaro_ac_uniform μ η e he hac hh).exists
  have hall : ∀ᶠ n : ℕ in atTop,∀ i : Fin N,
      LawClose ((η.map (e^[i.val])).map (remotePair e e.symm α n))
        (remoteProductLaw μ e e.symm α) (ε/2) := by
    exact Filter.eventually_all.2 (fun i => h.translate e he.toMeasurePreserving hα i.val (ε/2) hh)
  filter_upwards [hall] with n hn D hD
  let C := remotePair e e.symm α n ⁻¹' D
  have hC : MeasurableSet C := hD.preimage (measurable_remotePair e.measurable e.symm.measurable hα n)
  have hav := cesaroLawMass_close e η hN C (b := (remoteProductLaw μ e e.symm α).real D)
    (δ := ε/2) (fun i hi => by
      have hc := hn ⟨i,Finset.mem_range.mp hi⟩ D hD
      simpa only [Measure.real,Measure.map_apply (measurable_remotePair e.measurable e.symm.measurable hα n) hD,C]
        using hc)
  have ha := happrox C hC
  rw [abs_sub_comm] at ha
  simp only [Measure.real,Measure.map_apply (measurable_remotePair e.measurable e.symm.measurable hα n) hD]
  change |μ.real C-(remoteProductLaw μ e e.symm α).real D|≤ε
  exact (abs_sub_le _ (cesaroLawMass e η N C) _).trans
    ((add_le_add ha.le hav).trans (by linarith))

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding
open scoped ENNReal
namespace ReversibleGraphRectangle
variable {k χ : ℝ} {B : ReversibleRectangleBlock k χ} {F : ReversibleGraphFamilies B}
    (R : ReversibleGraphRectangle F)

theorem weakBernoulli_of_good_names {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ)
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : Torus → A) (hα : Measurable α)
    (hf : GoodNames μ ((standardMap k)^[N]) α)
    (hb : GoodNames μ ((inverseMap k)^[N]) α) :
    WeakBernoulliProcess μ (iterateEquiv (standardMap_measurableEquiv k) N) α := by
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have heq' : (e.symm : Torus → Torus)=(inverseMap k)^[N] := funext (iterateEquiv_symm_apply _ N)
  have he : Ergodic e μ := by
    rw [heq]
    simpa only [Function.iterate_one] using herg 1 (by omega)
  let ζ := (B.carrierProbability.prod B.carrierProbability).map R.torusPoint
  have : IsProbabilityMeasure ζ := inferInstance
  apply weakBernoulli_of_ac_remote μ ζ e he hπ.absolutelyContinuous hα
  have htriv : ∀ E,TailEvent μ e α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
    rw [heq]
    exact R.tail_trivial_of_good_names hN μ herg hπ α hα hf hb
  have hfst : MeasurePreserving (Prod.fst : (B.coordinateCarrier×B.coordinateCarrier)×
      (B.coordinateCarrier×B.coordinateCarrier) → B.coordinateCarrier×B.coordinateCarrier)
      ((B.carrierProbability.prod B.carrierProbability).prod (B.carrierProbability.prod B.carrierProbability))
      (B.carrierProbability.prod B.carrierProbability) := measurePreserving_fst
  have hgood := hfst.quasiMeasurePreserving.ae (hπ.ae (hf.and hb))
  apply local_remote_independent B.carrierProbability B.carrierProbability μ hπ
    he.toMeasurePreserving (he.toMeasurePreserving.symm e) hα htriv
    (tail_trivial_symm μ e he.toMeasurePreserving hα htriv)
  · filter_upwards [hgood] with w hw
    rw [heq']
    exact hw.2 _ ((R.column_exponential w.1.1 w.2.1 w.1.2).iterate hN)
  · filter_upwards [hgood] with w hw
    rw [heq]
    exact hw.1 _ ((R.row_exponential w.1.1 w.1.2 w.2.2).iterate hN)

theorem exists_weakBernoulli_partitions {N : ℕ} (hN : 0<N)
    (μ : Measure Torus) [IsProbabilityMeasure μ]
    (herg : ∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) μ)
    (hπ : QuasiMeasurePreserving R.torusPoint (B.carrierProbability.prod B.carrierProbability) μ) :
    ∃ α : ℕ → ℕ → Torus → Bool,
      (∀ i j,Measurable (α i j)) ∧ Function.Injective (fun z => fun i j => α i j z) ∧
      ∀ M : ℕ,WeakBernoulliProcess μ (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M) := by
  obtain ⟨α,hm,hi,hgood⟩ := R.exists_good_K_partitions hN μ herg hπ
  exact ⟨α,hm,hi,fun M => R.weakBernoulli_of_good_names hN μ herg hπ _
    (measurable_joinedBinary hm M) (hgood M).1 (hgood M).2.1⟩

end ReversibleGraphRectangle

theorem actual_weakBernoulli_component (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ (N : ℕ),0<N ∧ ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea E)) ∧
      ∃ α : ℕ → ℕ → Torus → Bool,
        (∀ i j,Measurable (α i j)) ∧ Function.Injective (fun z => fun i j => α i j z) ∧
        ∀ M : ℕ,WeakBernoulliProcess (normalizedArea E)
          (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M) := by
  obtain ⟨B⟩ := exists_reversibleRectangleBlock k hk hχ hgap
  obtain ⟨F⟩ := reversible_graph_families B
  obtain ⟨R⟩ := reversible_graph_rectangle F hk
  obtain ⟨N,hN,E,hE,hEp,hErg,hπ⟩ := R.exists_totally_ergodic_rectangle hk
  let _ := normalizedArea_probability hEp
  obtain ⟨α,hm,hi,ht⟩ := R.exists_weakBernoulli_partitions hN (normalizedArea E) hErg hπ
  exact ⟨N,hN,E,hE,hEp,hErg,α,hm,hi,ht⟩

end StandardMapEntropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

omit [MeasurableSpace X] [MeasurableSpace A] in
lemma tailName_commute (T d : X → X) (α : X → A) (h : Function.Commute d T) (n : ℕ) :
    tailName T (α ∘ d) n=tailName T α n ∘ d := by
  funext x i
  exact congrArg α (h.iterate_right (i+n) x)

theorem WeakBernoulliProcess.translate {μ ν : Measure X} (e : X ≃ᵐ X)
    {d : X → X} (hd : MeasurePreserving d ν μ) (hde : Function.Commute d e)
    (hde' : Function.Commute d e.symm) {α : X → A} (hα : Measurable α)
    (h : WeakBernoulliProcess μ e α) : WeakBernoulliProcess ν e (α ∘ d) := by
  have ht (T : X → X) (hT : Measurable T) (hc : Function.Commute d T) (n : ℕ) :
      ν.map (tailName T (α ∘ d) n)=μ.map (tailName T α n) := by
    rw [tailName_commute T d α hc n,←Measure.map_map
      (measurable_tailName hT hα n) hd.measurable,hd.map_eq]
  have hp (n : ℕ) : ν.map (remotePair e e.symm (α ∘ d) n)=μ.map (remotePair e e.symm α n) := by
    have heq : remotePair e e.symm (α ∘ d) n=remotePair e e.symm α n ∘ d := by
      funext x
      exact Prod.ext (congrFun (tailName_commute e.symm d α hde' n) x)
        (congrFun (tailName_commute e d α hde n) x)
    rw [heq,←Measure.map_map (measurable_remotePair e.measurable e.symm.measurable hα n)
      hd.measurable,hd.map_eq]
  have hprod : remoteProductLaw ν e e.symm (α ∘ d)=remoteProductLaw μ e e.symm α := by
    simp only [remoteProductLaw,ht e e.measurable hde 0,ht e.symm e.symm.measurable hde' 0]
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simpa only [hp n,hprod] using hn

end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding BoundedSubadditive
open scoped ENNReal

theorem actual_cyclic_weakBernoulli_component (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (standardMap k ⁻¹' E=E) ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) ∧
      ∃ (N : ℕ) (hN : 0<N) (P : Fin N → Set Torus),
        (∀ j,MeasurableSet (P j)) ∧ ((⋃ j,P j) =ᵐ[area] E) ∧
        (∀ i j,i≠j → area (P i∩P j)=0) ∧
        (∀ j,(standardMap k '' P j) =ᵐ[area] P ⟨(j.val+1)%N,Nat.mod_lt _ hN⟩) ∧
        (∀ j,area (P j)=area E/(N : ℝ≥0∞) ∧ 0<area (P j)) ∧
        (∀ j,∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea (P j))) ∧
        (∀ j,∃ α : ℕ → ℕ → Torus → Bool,
          (∀ i r,Measurable (α i r)) ∧ Function.Injective (fun z => fun i r => α i r z) ∧
          ∀ M : ℕ,WeakBernoulliProcess (normalizedArea (P j))
            (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) := by
  obtain ⟨B⟩ := exists_reversibleRectangleBlock k hk hχ hgap
  obtain ⟨G⟩ := reversible_graph_families B
  obtain ⟨R⟩ := reversible_graph_rectangle G hk
  obtain ⟨F,hπ,hFH⟩ := R.powerAtoms_with_rectangle hk
  have he : MeasurePreserving (standardMap_measurableEquiv k) area area := measurePreserving_standardMap k
  obtain ⟨n,hn⟩ := F.exists_totally_ergodic_cycle he
  let C := F.cycle he n
  let P (j : Fin C.period) : Set Torus := ((standardMap_measurableEquiv k).symm^[j.val]) ⁻¹' F.atom n
  have hP (j : Fin C.period) : MeasurableSet (P j) :=
    (F.measurable n).preimage ((standardMap_measurableEquiv k).symm.measurable.iterate j.val)
  have hPmass (j : Fin C.period) : area (P j)=area (F.atom n) :=
    ((he.symm (standardMap_measurableEquiv k)).iterate j.val).measure_preimage (F.measurable n).nullMeasurableSet
  have hEerg : Ergodic (standardMap k) (normalizedArea (F.atom 0)) := by
    have hh := (F.ergodic 0).smul_measure (area (F.atom 0))⁻¹
    simp only [zero_add,Function.iterate_one] at hh
    exact hh
  have htotal (j : Fin C.period) (r : ℕ) (hr : 0<r) :
      Ergodic (((standardMap k)^[C.period])^[r]) (normalizedArea (P j)) :=
    (hn r hr j).smul_measure (area (P j))⁻¹
  have hbase (r : ℕ) (hr : 0<r) :
      Ergodic (((standardMap k)^[C.period])^[r]) (normalizedArea (F.atom n)) := by
    simpa only [P,Fin.val_zero,Function.iterate_zero,preimage_id_eq,id_eq] using htotal ⟨0,C.positive⟩ r hr
  let _ := normalizedArea_probability (F.positive n)
  obtain ⟨α,hα,hsep,hwb⟩ := R.exists_weakBernoulli_partitions C.positive (normalizedArea (F.atom n)) hbase (hπ n)
  refine ⟨F.atom 0,F.measurable 0,F.positive 0,?_,hEerg,
    positive_spectrum_on_ergodic_component k hk (F.measurable 0) hEerg hFH,
    C.period,C.positive,P,hP,C.cover,C.disjoint,C.forward,?_,htotal,?_⟩
  · have hh := F.invariant 0
    simp only [zero_add,Function.iterate_one] at hh
    exact hh
  · intro j
    rw [hPmass]
    exact ⟨(ENNReal.eq_div_iff (by exact_mod_cast C.positive.ne') (by simp)).mpr C.mass,F.positive n⟩
  · intro j
    let d : Torus → Torus := (standardMap_measurableEquiv k).symm^[j.val]
    have hd : MeasurePreserving d (normalizedArea (P j)) (normalizedArea (F.atom n)) := by
      unfold normalizedArea
      rw [hPmass]
      exact (((he.symm (standardMap_measurableEquiv k)).iterate j.val).restrict_preimage
        (F.measurable n)).smul_measure (area (F.atom n))⁻¹
    have hdi : Function.Injective d := (standardMap_measurableEquiv k).symm.injective.iterate j.val
    refine ⟨fun i r => α i r ∘ d,fun i r => (hα i r).comp hd.measurable,?_,?_⟩
    · intro x y hxy
      exact hdi (hsep hxy)
    · intro M
      have hc : Function.Commute (standardMap_measurableEquiv k).symm (standardMap_measurableEquiv k) :=
        fun x => (inverseMap_standardMap k x).trans (standardMap_inverseMap k x).symm
      have hde : Function.Commute d (iterateEquiv (standardMap_measurableEquiv k) C.period) := by
        simpa only [funext (iterateEquiv_apply (standardMap_measurableEquiv k) C.period)] using
          hc.iterate_iterate j.val C.period
      have hde' : Function.Commute d (iterateEquiv (standardMap_measurableEquiv k) C.period).symm := by
        have hc' : Function.Commute (standardMap_measurableEquiv k).symm (standardMap_measurableEquiv k).symm :=
          fun _ => rfl
        simpa only [funext (iterateEquiv_symm_apply (standardMap_measurableEquiv k) C.period)] using
          hc'.iterate_iterate j.val C.period
      exact (hwb M).translate _ hd hde hde' (measurable_joinedBinary hα M)

theorem eventually_actual_cyclic_weakBernoulli_component :
    ∃ k₀ : ℝ,0<k₀ ∧ ∀ k : ℝ,k₀≤k →
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (standardMap k ⁻¹' E=E) ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) ∧
      ∃ (N : ℕ) (hN : 0<N) (P : Fin N → Set Torus),
        (∀ j,MeasurableSet (P j)) ∧ ((⋃ j,P j) =ᵐ[area] E) ∧
        (∀ i j,i≠j → area (P i∩P j)=0) ∧
        (∀ j,(standardMap k '' P j) =ᵐ[area] P ⟨(j.val+1)%N,Nat.mod_lt _ hN⟩) ∧
        (∀ j,area (P j)=area E/(N : ℝ≥0∞) ∧ 0<area (P j)) ∧
        (∀ j,∀ r : ℕ,0<r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea (P j))) ∧
        (∀ j,∃ α : ℕ → ℕ → Torus → Bool,
          (∀ i r,Measurable (α i r)) ∧ Function.Injective (fun z => fun i r => α i r z) ∧
          ∀ M : ℕ,WeakBernoulliProcess (normalizedArea (P j))
            (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) := by
  obtain ⟨K,hK,hdef⟩ := eventually_meanDeficit_small (1/8 : ℝ) (by norm_num)
  refine ⟨K,hK,?_⟩
  intro k hk
  have hk0 : 0≤k := hK.le.trans hk
  obtain ⟨χ,hχ,hgap⟩ := exists_positive_spectral_gap k hk0
    (positive_standardLyapunov_of_deficit k hk0 (hdef k hk))
  exact actual_cyclic_weakBernoulli_component k hk0 hχ hgap

end StandardMapEntropy

end
end

end OAI
