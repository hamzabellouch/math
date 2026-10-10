import OAI.Dynamics.StandardMap.WeightIdentification

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def capF (α : ℝ) (d : DistanceArray) : ℝ := entropyCap α (arrayShortfall 0 (dyadicInt 1) d)
noncomputable def capFpos (α : ℝ) (d : DistanceArray) : ℝ := entropyCap α (max (arrayShortfall 0 (dyadicInt 1) d) 0)
lemma continuous_capF (α : ℝ) : Continuous (capF α) := (entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)
lemma continuous_capFpos (α : ℝ) : Continuous (capFpos α) := (entropyCap_contDiff α).continuous.comp ((continuous_arrayShortfall _ _).max continuous_const)
lemma shortfall_one_max_mem (d : DistanceArray) : max (arrayShortfall 0 (dyadicInt 1) d) 0∈Icc (0:ℝ) 1 := by
  refine ⟨le_max_right _ _,max_le ?_ (by norm_num)⟩
  have hh := d.property.1 0 (dyadicInt 1)
  convert! sub_le_self (1:ℝ) hh using 1
  simp only [arrayShortfall,dyadicInt_val,ZeroMemClass.coe_zero,Int.cast_one,sub_zero,div_one]
lemma capFpos_nonneg {α : ℝ} (hα : 0≤α) (hα1 : α≤1) (d : DistanceArray) : 0≤capFpos α d :=
  (entropyCap_bounds hα hα1 (shortfall_one_max_mem d)).1
lemma capF_sample_integral (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) (α : ℝ) :
    (∫d,capF α d ∂sampleLaw k hk n hn)=(∫d,capFpos α d ∂sampleLaw k hk n hn) := by
  rw [integral_sampleLaw _ _ _ _ _ (continuous_capF α),integral_sampleLaw _ _ _ _ _ (continuous_capFpos α)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold capF capFpos
  dsimp only
  rw [shortfall_sample_aligned k hk z n hn 0 (dyadicInt 1) 0 n hn (by simp) (by simp)]
  rw [max_eq_left (torusShortfall_mem k hk z 0 n hn).1]
lemma capF_scale_integral (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε) (α : ℝ) :
    (∫d,capF α d ∂scaleLaw k hk p l ε)=(∫d,capFpos α d ∂scaleLaw k hk p l ε) := by
  rw [integral_scaleLaw _ _ _ _ _ hε _ (continuous_capF α),integral_scaleLaw _ _ _ _ _ hε _ (continuous_capFpos α)]
  simp_rw [capF_sample_integral]
lemma vague_integrable_tendsto_bound {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) [∀i,IsFiniteMeasureOnCompacts (μ i)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hconv : ∀g:C_c(X,ℝ),Tendsto (fun i => ∫x,g x ∂μ i) l (𝓝 (∫x,g x ∂ν)))
    (f:X→ℝ) (hf:Continuous f) (h0:∀x,0≤f x) (a:ι→ℝ) (A:ℝ) (hA:0≤A)
    (ha:Tendsto a l (𝓝 A)) (hi:∀i,Integrable f (μ i)) (hb:∀ᶠi in l,(∫x,f x ∂μ i)≤a i) :
    Integrable f ν ∧ (∫x,f x ∂ν)≤A := by
  have hcc : ∀g:C_c(X,ℝ),(∀x,0≤g x) → (∀x,g x≤f x) → (∫x,g x ∂ν)≤A := by
    intro g hg hgf
    apply le_of_tendsto_of_tendsto (hconv g) ha
    filter_upwards [hb] with i hiA
    exact (integral_mono (g.continuous.integrable_of_hasCompactSupport (μ := μ i) g.hasCompactSupport) (hi i) hgf).trans hiA
  have hL := lintegral_le_of_cc_le ν f hf h0 A hcc
  have hiν : Integrable f ν := ⟨hf.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hiν,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hiν (Eventually.of_forall h0)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff hA).mp hL
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminal_cap_bounds {α : ℝ} (hα : 0≤α) (hα1 : α≤1) {C : ℝ}
    (hb : ∀u∈Icc (0:ℝ) 1,entropyCap α u≤C*u) (i : ℕ) :
    α/10000≤(∫d,capFpos α d ∂S.terminalLaw i) ∧ (∫d,capFpos α d ∂S.terminalLaw i)≤C := by
  have hi := (continuous_capFpos α).integrable_of_hasCompactSupport (μ := S.terminalLaw i) (HasCompactSupport.of_compactSpace _)
  have hh : Integrable (fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0) (S.terminalLaw i) := ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const).integrable_of_hasCompactSupport (μ := S.terminalLaw i) (HasCompactSupport.of_compactSpace _)
  constructor
  · have he := integral_mono (hh.const_mul (α/10000)) hi (fun d => entropyCap_lower hα hα1 (shortfall_one_max_mem d))
    simpa only [integral_const_mul,S.terminal_shortfall_max_integral i,mul_one] using he
  · have he := integral_mono hi (hh.const_mul C) (fun d => hb _ (shortfall_one_max_mem d))
    simpa only [integral_const_mul,S.terminal_shortfall_max_integral i,mul_one] using he
lemma exists_terminal_cap_limit {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    ∃H:ℝ,0<H ∧ Tendsto (fun i => ∫d,capF α d ∂S.terminalLaw i) (L.filter:Filter ℕ) (𝓝 H) ∧
      Integrable (fun d:NonAffineArray => capF α d.val) L.terminal ∧
      (∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα.le hα1
  let a : ℕ→ℝ := fun i => ∫d,capFpos α d ∂S.terminalLaw i
  have hmem : ∀i,a i∈Icc (α/10000) C := S.terminal_cap_bounds hα.le hα1 hb
  obtain ⟨H,hH,ht⟩ := (isCompact_Icc : IsCompact (Icc (α/10000) C)).ultrafilter_le_nhds (L.filter.map a) (by
    rw [Filter.le_principal_iff]
    change Icc (α/10000) C∈Filter.map a (L.filter:Filter ℕ)
    exact Filter.mem_map.mpr (Eventually.of_forall hmem))
  have hH0 : 0<H := (div_pos hα (by norm_num)).trans_le hH.1
  have ht' : Tendsto a (L.filter:Filter ℕ) (𝓝 H) := ht
  obtain ⟨hi,hle⟩ := vague_integrable_tendsto_bound L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (fun d => capFpos α d.val) ((continuous_capFpos α).comp continuous_subtype_val)
    (fun d => capFpos_nonneg hα.le hα1 d.val) a H hH0.le ht'
    (fun i => integrable_nonaffinePart _ _ (continuous_capFpos α)) (Eventually.of_forall (fun i =>
      integral_nonaffinePart_le _ _ (continuous_capFpos α) (capFpos_nonneg hα.le hα1)))
  have he : (fun d:NonAffineArray => capFpos α d.val)=ᵐ[L.terminal] (fun d => capF α d.val) := by
    filter_upwards [S.unit_aeterminal L] with d hd
    unfold capFpos capF
    rw [max_eq_left (shortfall_unit_mem d.val hd _ _ (by norm_num)).1]
  refine ⟨H,hH0,?_,hi.congr he,by rw [←integral_congr_ae he]; exact hle⟩
  convert! ht' using 1
  funext i
  exact capF_scale_integral _ _ _ _ _ (S.epsilon_pos i) α
end CriticalScaleSequence
end StandardMapEntropy

end OAI
