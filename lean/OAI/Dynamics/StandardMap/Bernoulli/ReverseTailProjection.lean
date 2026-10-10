import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.IntegerDynamics

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

@[instance_reducible] def tailSigma (T : X → X) (α : X → A) (n : ℕ) : MeasurableSpace X :=
  MeasurableSpace.comap (tailName T α n) inferInstance

lemma tailSigma_le {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α) (n : ℕ) :
    tailSigma T α n ≤ (inferInstance : MeasurableSpace X) :=
  (measurable_tailName hT hα n).comap_le

omit [MeasurableSpace X] in
lemma tailSigma_antitone (T : X → X) (α : X → A) : Antitone (tailSigma T α) := by
  intro n m hnm E hE
  obtain ⟨D,hD,rfl⟩ := hE
  let S (v : ℕ → A) (j : ℕ) := v (j+m-n)
  have hS : Measurable S := Measurable.of_eval (fun j => measurable_pi_apply (j+m-n))
  refine ⟨S ⁻¹' D,hD.preimage hS,?_⟩
  ext x
  change (S (tailName T α n x)∈D) ↔ (tailName T α m x∈D)
  have hh : S (tailName T α n x)=tailName T α m x := by
    funext j
    simp only [S,tailName]
    congr 2
    omega
  rw [hh]

lemma tailEvent_of_aestronglyMeasurable (μ : Measure X) (T : X → X) (α : X → A)
    {f : X → ℝ} (hf : ∀ n,AEStronglyMeasurable[tailSigma T α n] f μ) (r : ℝ) :
    TailEvent μ T α {x | f x<r} := by
  intro n
  have hset := (hf n).measurable_mk (measurableSet_Iio (a := r))
  obtain ⟨D,hD,hpre⟩ := hset
  refine ⟨D,hD,?_⟩
  filter_upwards [(hf n).ae_eq_mk] with x hx
  change (f x<r)=(tailName T α n x∈D)
  have hh : (tailName T α n x∈D) ↔ (hf n).mk f x<r := by
    change (x∈tailName T α n ⁻¹' D) ↔ (x∈(hf n).mk f ⁻¹' Iio r)
    rw [hpre]
  exact propext (by rw [hx]; exact hh.symm)

lemma ae_constant_of_trivial_thresholds (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : ∀ r : ℚ,(∀ᵐ x ∂μ,f x<(r : ℝ)) ∨ (∀ᵐ x ∂μ,¬f x<(r : ℝ))) :
    ∃ c : ℝ,f=ᵐ[μ](fun _ => c) := by
  have hr (r : ℚ) : ∃ b : Prop,∀ᵐ x ∂μ,(f x<(r : ℝ) ↔ b) := by
    rcases hf r with h|h
    · exact ⟨True,h.mono (fun _ hx => by simp only [hx])⟩
    · exact ⟨False,h.mono (fun _ hx => by simp only [hx])⟩
  choose b hb using hr
  have hall := ae_all_iff.mpr hb
  obtain ⟨x₀,hx₀⟩ := hall.exists
  refine ⟨f x₀,hall.mono ?_⟩
  intro x hx
  exact eq_of_forall_lt_rat_iff_lt (fun r => (hx r).trans (hx₀ r).symm)

theorem tail_condExpL2_limit (μ : Measure X) {T : X → X} {α : X → A}
    (hT : Measurable T) (hα : Measurable α) (f : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ,(∀ n,AEStronglyMeasurable[tailSigma T α n] g μ) ∧
      Tendsto (fun n => (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)) atTop (𝓝 g) := by
  let K (n : ℕ) := lpMeas ℝ ℝ (tailSigma T α n) 2 μ
  let (n : ℕ) : Fact (tailSigma T α n ≤ (inferInstance : MeasurableSpace X)) := ⟨tailSigma_le hT hα n⟩
  have (n : ℕ) : (K n).HasOrthogonalProjection := by dsimp only [K]; infer_instance
  have hK : Antitone K := by
    intro n m hnm f hf
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      (AEStronglyMeasurable.mono (tailSigma_antitone T α hnm) (mem_lpMeas_iff_aestronglyMeasurable.mp hf))
  have hc (n : ℕ) : IsClosed (K n : Set (Lp ℝ 2 μ)) := isClosed_aestronglyMeasurable (tailSigma_le hT hα n)
  obtain ⟨g,hg,ht⟩ := decreasing_projection_limit K hK hc f
  refine ⟨g,fun n => mem_lpMeas_iff_aestronglyMeasurable.mp (hg n),?_⟩
  exact ht

theorem tail_condExpL2_constant_limit (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (f : Lp ℝ 2 μ) :
    ∃ (g : Lp ℝ 2 μ) (c : ℝ),g=ᵐ[μ](fun _ => c) ∧
      Tendsto (fun n => (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)) atTop (𝓝 g) := by
  obtain ⟨g,hg,ht⟩ := tail_condExpL2_limit μ hT hα f
  obtain ⟨c,hc⟩ := ae_constant_of_trivial_thresholds μ g (fun r =>
    htriv _ (tailEvent_of_aestronglyMeasurable μ T α hg r))
  exact ⟨g,c,hc,ht⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

noncomputable def constL2 (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) : Lp ℝ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) c

lemma constL2_ae (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) :
    constL2 μ c=ᵐ[μ](fun _ : X => c) := by
  simpa only [constL2,indicator_univ] using
    (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ) (hμs := measure_ne_top μ univ) (c := c))

lemma inner_constL2_one (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    inner ℝ (constL2 μ 1) f=∫ x,f x ∂μ := by
  simpa only [constL2,setIntegral_univ] using (L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ univ) f)

theorem tail_condExpL2_mean_limit (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ))
      atTop (𝓝 (constL2 μ (∫ x,f x ∂μ))) := by
  obtain ⟨g,c,hc,ht⟩ := tail_condExpL2_constant_limit μ hT hα htriv f
  have hi (n : ℕ) : inner ℝ (constL2 μ 1) (condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)=∫ x,f x ∂μ := by
    rw [inner_constL2_one]
    simpa only [setIntegral_univ] using
      (integral_condExpL2_eq_of_fin_meas_real (hm := tailSigma_le hT hα n) f MeasurableSet.univ (measure_ne_top μ univ))
  have hl : inner ℝ (constL2 μ 1) g=∫ x,f x ∂μ :=
    tendsto_nhds_unique (tendsto_const_nhds.inner ht) (by simpa only [hi] using tendsto_const_nhds)
  have hcg : inner ℝ (constL2 μ 1) g=c := by
    rw [inner_constL2_one,integral_congr_ae hc]
    simp
  have hmean : c=∫ x,f x ∂μ := hcg.symm.trans hl
  have heq : g=constL2 μ (∫ x,f x ∂μ) :=
    Lp.ext (hc.trans (by simpa only [hmean] using (constL2_ae μ c).symm))
  rwa [heq] at ht

lemma norm_indicatorConstLp_one_le (μ : Measure X) [IsProbabilityMeasure μ]
    {C : Set X} (hC : MeasurableSet C) :
    ‖indicatorConstLp 2 hC (measure_ne_top μ C) (1 : ℝ)‖ ≤ 1 := by
  rw [norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul]
  exact Real.rpow_le_one (measureReal_nonneg) measureReal_le_one (by positivity)

lemma tail_covariance_projection_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (f : Lp ℝ 2 μ) (n : ℕ) {C : Set X} (hC : MeasurableSet[tailSigma T α n] C) :
    |(∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)| ≤
      ‖(condExpL2 ℝ ℝ (tailSigma_le hT hα n) f : Lp ℝ 2 μ)-constL2 μ (∫ x,f x ∂μ)‖ := by
  let hm := tailSigma_le hT hα n
  let v : Lp ℝ 2 μ := indicatorConstLp 2 (hm C hC) (measure_ne_top μ C) 1
  let p : Lp ℝ 2 μ := condExpL2 ℝ ℝ hm f
  let c : Lp ℝ 2 μ := constL2 μ (∫ x,f x ∂μ)
  have hv : AEStronglyMeasurable[tailSigma T α n] v μ :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (mem_lpMeas_indicatorConstLp (𝕜 := ℝ) hm hC (measure_ne_top μ C))
  have hp : inner ℝ v p=inner ℝ v f := by
    rw [real_inner_comm p v,real_inner_comm f v]
    exact inner_condExpL2_eq_inner_fun hm f v hv
  have hvf : inner ℝ v f=∫ x in C,f x ∂μ := L2.inner_indicatorConstLp_one _ _ f
  have hvc : inner ℝ v c=μ.real C*(∫ x,f x ∂μ) := by
    rw [show inner ℝ v c=∫ x in C,c x ∂μ from L2.inner_indicatorConstLp_one _ _ c]
    rw [integral_congr_ae (ae_restrict_of_ae (constL2_ae μ (∫ x,f x ∂μ)))]
    simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,Measure.real]
  have he : (∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)=inner ℝ v (p-c) := by
    rw [inner_sub_right,hp,hvf,hvc]
  rw [he]
  exact (abs_real_inner_le_norm v (p-c)).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_indicatorConstLp_one_le μ (hm C hC)))

theorem uniform_tail_covariance_small (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (f : Lp ℝ 2 μ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ C : Set X,MeasurableSet[tailSigma T α n] C →
      |(∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)|<ε := by
  have ht := ((tail_condExpL2_mean_limit μ hT hα htriv f).sub_const (constL2 μ (∫ x,f x ∂μ))).norm
  simp only [sub_self,norm_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn C hC
  exact (tail_covariance_projection_bound μ hT hα f n hC).trans_lt hn

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma abs_setIntegral_le_L1 (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ) (C : Set X) :
    |∫ x in C,f x ∂μ| ≤ ∫ x,|f x| ∂μ := by
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral hf.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))

theorem uniform_tail_covariance_small_L1 (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    {f : X → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ C : Set X,MeasurableSet[tailSigma T α n] C →
      |(∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)|<ε := by
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hf).exists_simpleFunc_eLpNorm_sub_lt
    (by simp : (1 : ℝ≥0∞)≠⊤) (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith : 0<ε/4)))
  have hg2 : MemLp g 2 μ := SimpleFunc.memLp_of_finite_measure_preimage 2
    (fun y _ => measure_lt_top μ (g ⁻¹' {y}))
  have gi : Integrable g μ := memLp_one_iff_integrable.mp hgm
  have hi : ∫ x,|f x-g x| ∂μ<ε/4 := by
    simp_rw [← Real.norm_eq_abs]
    change (∫ x,‖(f-⇑g) x‖ ∂μ)<ε/4
    rw [integral_norm_eq_lintegral_enorm (hf.sub gi).aestronglyMeasurable]
    rw [eLpNorm_one_eq_lintegral_enorm (hf.sub gi).aestronglyMeasurable] at hg
    exact ENNReal.toReal_lt_of_lt_ofReal hg
  have ht := uniform_tail_covariance_small μ hT hα htriv (hg2.toLp g) (by linarith : 0<ε/2)
  filter_upwards [ht] with n hn C hC
  have hgc := hg2.coeFn_toLp
  have hgn := hn C hC
  rw [integral_congr_ae (ae_restrict_of_ae hgc),integral_congr_ae hgc] at hgn
  have hdiff : |(∫ x in C,f x ∂μ)-(∫ x in C,g x ∂μ)|≤∫ x,|f x-g x| ∂μ := by
    rw [← integral_sub hf.integrableOn gi.integrableOn]
    exact abs_setIntegral_le_L1 μ (hf.sub gi) C
  have hmean : |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)|≤∫ x,|f x-g x| ∂μ := by
    rw [←integral_sub hf gi]
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => f x-g x))
  have hmul : |μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ))|≤∫ x,|f x-g x| ∂μ := by
    rw [abs_mul,abs_of_nonneg measureReal_nonneg]
    exact (mul_le_of_le_one_left (abs_nonneg _) measureReal_le_one).trans hmean
  have htri := abs_add_le ((∫ x in C,f x ∂μ)-(∫ x in C,g x ∂μ))
    (((∫ x in C,g x ∂μ)-μ.real C*(∫ x,g x ∂μ))-μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ)))
  have htri' := abs_sub_le ((∫ x in C,g x ∂μ)-μ.real C*(∫ x,g x ∂μ)) 0
    (μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ)))
  simp only [sub_zero,zero_sub,abs_neg] at htri'
  have heq : (∫ x in C,f x ∂μ)-μ.real C*(∫ x,f x ∂μ)=
      ((∫ x in C,f x ∂μ)-(∫ x in C,g x ∂μ))+
      (((∫ x in C,g x ∂μ)-μ.real C*(∫ x,g x ∂μ))-μ.real C*((∫ x,f x ∂μ)-(∫ x,g x ∂μ))) := by ring
  rw [heq]
  linarith

theorem ac_remote_tail_law (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hac : η≪μ) {T : X → X} {α : X → A} (hT : Measurable T) (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ D : Set (ℕ → A),MeasurableSet D →
      |(η.map (tailName T α n)).real D-(μ.map (tailName T α n)).real D|<ε := by
  let f : X → ℝ := fun x => (η.rnDeriv μ x).toReal
  have hf : Integrable f μ := by
    simpa only [mul_one] using (integrable_toReal_rnDeriv_mul_iff (f := fun _ => (1 : ℝ)) hac).mpr (integrable_const 1)
  have hmean : ∫ x,f x ∂μ=1 := by
    simpa [f,Measure.real] using
      (integral_toReal_rnDeriv_mul (f := fun _ => (1 : ℝ)) hac)
  filter_upwards [uniform_tail_covariance_small_L1 μ hT hα htriv hf hε] with n hn D hD
  have hC : MeasurableSet[tailSigma T α n] (tailName T α n ⁻¹' D) := ⟨D,hD,rfl⟩
  have hi : ∫ x in tailName T α n ⁻¹' D,f x ∂μ=η.real (tailName T α n ⁻¹' D) := by
    simpa only [mul_one,integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,Measure.real] using
      (setIntegral_toReal_rnDeriv_mul (f := fun _ => (1 : ℝ)) hac ((measurable_tailName hT hα n) hD))
  have hh := hn _ hC
  rw [hmean,mul_one,hi] at hh
  simpa only [Measure.real,Measure.map_apply (measurable_tailName hT hα n) hD] using hh

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma LawClose.mono {μ ν : Measure X} {ε δ : ℝ} (h : LawClose μ ν ε) (hεδ : ε≤δ) :
    LawClose μ ν δ := fun D hD => (h D hD).trans hεδ

def remotePair (T S : X → X) (α : X → A) (n : ℕ) (x : X) : (ℕ → A)×(ℕ → A) :=
  (tailName S α n x,tailName T α n x)

lemma measurable_remotePair {T S : X → X} {α : X → A}
    (hT : Measurable T) (hS : Measurable S) (hα : Measurable α) (n : ℕ) :
    Measurable (remotePair T S α n) :=
  (measurable_tailName hS hα n).prodMk (measurable_tailName hT hα n)

noncomputable def remoteProductLaw (μ : Measure X) (T S : X → X) (α : X → A) :
    Measure ((ℕ → A)×(ℕ → A)) :=
  (μ.map (tailName S α 0)).prod (μ.map (tailName T α 0))

def RemoteIndependent (μ η : Measure X) (T S : X → X) (α : X → A) : Prop :=
  ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
    LawClose (η.map (remotePair T S α n)) (remoteProductLaw μ T S α) ε

def WeakBernoulliProcess (μ : Measure X) (e : X ≃ᵐ X) (α : X → A) : Prop :=
  RemoteIndependent μ μ e e.symm α

lemma stationary_tail_law (μ : Measure X) {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} (hα : Measurable α) (n : ℕ) :
    μ.map (tailName T α n)=μ.map (tailName T α 0) := by
  have heq : tailName T α n=(tailName T α 0) ∘ T^[n] := by
    funext x i
    simp only [tailName,Function.comp_apply,Nat.add_zero,←Function.iterate_add_apply]
  rw [heq,←Measure.map_map (measurable_tailName hT.measurable hα 0) (hT.measurable.iterate n),
    (hT.iterate n).map_eq]

lemma ac_stationary_tail_law (μ η : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hac : η≪μ) {T : X → X} (hT : MeasurePreserving T μ μ) {α : X → A} (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n : ℕ in atTop,
      LawClose (η.map (tailName T α n)) (μ.map (tailName T α 0)) ε := by
  filter_upwards [ac_remote_tail_law μ η hac hT.measurable hα htriv hε] with n hn D hD
  rw [←stationary_tail_law μ hT hα n]
  exact (hn D hD).le

lemma tail_trivial_symm (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    [Fintype A] [MeasurableSingletonClass A] {α : X → A} (hα : Measurable α)
    (htriv : ∀ E,TailEvent μ e α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E)) :
    ∀ E,TailEvent μ e.symm α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E) := by
  intro E hE
  exact htriv E (hE.reverse e.symm (he.symm e) hα)

def dropName (k : ℕ) (v : ℕ → A) (i : ℕ) : A := v (i+k)
lemma measurable_dropName (k : ℕ) : Measurable (dropName (A := A) k) :=
  Measurable.of_eval (fun i => measurable_pi_apply (i+k))

lemma stationary_drop_law (μ : Measure X) {T : X → X} (hT : MeasurePreserving T μ μ)
    {α : X → A} (hα : Measurable α) (k : ℕ) :
    (μ.map (tailName T α 0)).map (dropName k)=μ.map (tailName T α 0) := by
  rw [Measure.map_map (measurable_dropName k) (measurable_tailName hT.measurable hα 0)]
  have hcomp : dropName k ∘ tailName T α 0=tailName T α k := by
    funext x i
    simp only [dropName,Function.comp_apply,tailName,Nat.add_zero]
  rw [hcomp,stationary_tail_law μ hT hα k]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

lemma measurePreserving_exchange_first {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (η : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    MeasurePreserving (fun w : (A×B)×(A×B) => ((w.2.1,w.1.2),(w.1.1,w.2.2)))
      ((ν.prod η).prod (ν.prod η)) ((ν.prod η).prod (ν.prod η)) := by
  have ht : MeasurePreserving (fun w : (A×B)×A => ((w.2,w.1.2),w.1.1))
      ((ν.prod η).prod ν) ((ν.prod η).prod ν) :=
    ((measurePreserving_prodAssoc ν η ν).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id ν).prod (measurePreserving_swap (μ := ν) (ν := η))).comp
        (measurePreserving_swap (μ := ν.prod η) (ν := ν)))
  exact (measurePreserving_prodAssoc (ν.prod η) ν η).comp
    ((ht.prod (MeasurePreserving.id η)).comp
      ((measurePreserving_prodAssoc (ν.prod η) ν η).symm MeasurableEquiv.prodAssoc))

theorem product_remote_two_tail_independence {A B X C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    [MeasurableSpace C] [MeasurableEq C]
    (ν : Measure A) (η : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    {π : A×B → X} (hπ : Measurable π) {T S : X → X} (hT : Measurable T) (hS : Measurable S)
    {α : X → C} (hα : Measurable α)
    (hpast : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (S^[n] (π w.1))=α (S^[n] (π (w.2.1,w.1.2))))
    (hfuture : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (T^[n] (π w.1))=α (T^[n] (π (w.1.1,w.2.2)))) :
    ∃ δ : ℕ → ℝ,Tendsto δ atTop (𝓝 0) ∧ (∀ n,0≤δ n) ∧ ∀ n : ℕ,
      LawClose ((ν.prod η).map (fun p => (tailName S α n (π p),tailName T α n (π p))))
        (((ν.prod η).map (fun p => tailName S α n (π p))).prod
          ((ν.prod η).map (fun p => tailName T α n (π p)))) (δ n) := by
  let κ := (ν.prod η).prod (ν.prod η)
  let p : (A×B)×(A×B) → X := fun w => π w.1
  let q : (A×B)×(A×B) → X := fun w => π (w.2.1,w.1.2)
  let r : (A×B)×(A×B) → X := fun w => π (w.1.1,w.2.2)
  have hp : Measurable p := hπ.comp measurable_fst
  have hq : Measurable q := hπ.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hr : Measurable r := hπ.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  let Ds n := {w | tailName S α n (p w)≠tailName S α n (q w)}
  let Dt n := {w | tailName T α n (p w)≠tailName T α n (r w)}
  let δ n := κ.real (Ds n)+κ.real (Dt n)
  have hds := tail_disagreement_tendsto_zero κ hS hα hp hq hpast
  have hdt := tail_disagreement_tendsto_zero κ hT hα hp hr hfuture
  refine ⟨δ,by simpa only [add_zero] using hds.add hdt,fun _ => add_nonneg measureReal_nonneg measureReal_nonneg,?_⟩
  intro n D hD
  let s : A×B → (ℕ → C) := fun w => tailName S α n (π w)
  let t : A×B → (ℕ → C) := fun w => tailName T α n (π w)
  have hs : Measurable s := (measurable_tailName hS hα n).comp hπ
  have ht : Measurable t := (measurable_tailName hT hα n).comp hπ
  let P : (A×B)×(A×B) → (ℕ → C)×(ℕ → C) := fun w => (s w.1,t w.1)
  let Q : (A×B)×(A×B) → (ℕ → C)×(ℕ → C) := fun w => (s (w.2.1,w.1.2),t (w.1.1,w.2.2))
  have hP : Measurable P := (hs.prodMk ht).comp measurable_fst
  have harr := measurePreserving_exchange_first ν η
  have hQ : Measurable Q := (hs.prodMap ht).comp harr.measurable
  have hmapP : κ.map P=(ν.prod η).map (fun w => (s w,t w)) := by
    have hfst : MeasurePreserving (Prod.fst : (A×B)×(A×B) → A×B) κ (ν.prod η) := measurePreserving_fst
    rw [←hfst.map_eq,Measure.map_map (hs.prodMk ht) measurable_fst]
    rfl
  have hmapQ : κ.map Q=((ν.prod η).map s).prod ((ν.prod η).map t) := by
    calc
      κ.map Q=κ.map (Prod.map s t) := by
        change κ.map (Prod.map s t ∘ (fun w : (A×B)×(A×B) => ((w.2.1,w.1.2),(w.1.1,w.2.2))))=_
        rw [←Measure.map_map (hs.prodMap ht) harr.measurable,harr.map_eq]
      _=_ := (Measure.map_prod_map (ν.prod η) (ν.prod η) hs ht).symm
  have h := law_distance_le_disagreement κ hP hQ hD
  rw [hmapP,hmapQ] at h
  apply h.trans
  calc
    κ.real {w | P w≠Q w}≤κ.real (Ds n∪Dt n) := measureReal_mono (by
      intro w hw
      change (tailName S α n (p w)≠tailName S α n (q w)) ∨ (tailName T α n (p w)≠tailName T α n (r w))
      simpa only [mem_ofPred_eq,P,Q,s,t,p,q,r,ne_eq,Prod.mk.injEq,not_and_or] using hw)
    _≤δ n := measureReal_union_le _ _

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

theorem local_remote_independent {A B X C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    [MeasurableSpace C] [MeasurableEq C]
    (ν : Measure A) (η : Measure B) (μ : Measure X)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    {π : A×B → X} (hπ : QuasiMeasurePreserving π (ν.prod η) μ)
    {T S : X → X} (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    {α : X → C} (hα : Measurable α)
    (htrivT : ∀ E,TailEvent μ T α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (htrivS : ∀ E,TailEvent μ S α E → (∀ᵐ x ∂μ,x∈E) ∨ (∀ᵐ x ∂μ,x∉E))
    (hpast : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (S^[n] (π w.1))=α (S^[n] (π (w.2.1,w.1.2))))
    (hfuture : ∀ᵐ w : (A×B)×(A×B) ∂(ν.prod η).prod (ν.prod η),∀ᶠ n : ℕ in atTop,
      α (T^[n] (π w.1))=α (T^[n] (π (w.1.1,w.2.2)))) :
    RemoteIndependent μ ((ν.prod η).map π) T S α := by
  obtain ⟨δ,hd,hδ,hclose⟩ := product_remote_two_tail_independence ν η hπ.measurable hT.measurable hS.measurable hα hpast hfuture
  let ζ := (ν.prod η).map π
  have : IsProbabilityMeasure ζ := inferInstance
  have (n : ℕ) : IsProbabilityMeasure (ζ.map (tailName S α n)) := inferInstance
  have (n : ℕ) : IsProbabilityMeasure (ζ.map (tailName T α n)) := inferInstance
  have : IsProbabilityMeasure (μ.map (tailName S α 0)) := inferInstance
  have : IsProbabilityMeasure (μ.map (tailName T α 0)) := inferInstance
  intro ε hε
  have hthird : 0<ε/3 := by linarith
  filter_upwards [hd.eventually (gt_mem_nhds hthird),
    ac_stationary_tail_law μ ζ hπ.absolutelyContinuous hT hα htrivT hthird,
    ac_stationary_tail_law μ ζ hπ.absolutelyContinuous hS hα htrivS hthird] with n hn htn hsn
  have hjoin : LawClose (ζ.map (remotePair T S α n))
      ((ζ.map (tailName S α n)).prod (ζ.map (tailName T α n))) (δ n) := by
    simpa only [ζ,Measure.map_map (measurable_remotePair hT.measurable hS.measurable hα n) hπ.measurable,
      Measure.map_map (measurable_tailName hS.measurable hα n) hπ.measurable,
      Measure.map_map (measurable_tailName hT.measurable hα n) hπ.measurable,Function.comp_def,remotePair]
      using hclose n
  exact ((hjoin.mono hn.le).triangle (hsn.prod htn)).mono (by linarith)

end HyperbolicCoding

end
end

end OAI
