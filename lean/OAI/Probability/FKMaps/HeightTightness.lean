import OAI.Probability.FKMaps.HeightBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def codeEmbedding (N : ℕ) : Code N ↪ (Fin N → ℕ) :=
  ⟨fun d => bridgeEmbedding N ⟨d.val,d.property.1⟩, fun _ _ h =>
    Subtype.ext (congrArg (fun b : Bridge N => b.val) ((bridgeEmbedding N).injective h))⟩

lemma CriticalEvenOffspring.code_probability_le_stream (p : CriticalEvenOffspring) (n : ℕ)
    (E : Set (Code (2*n+1))) (A : Set (ℕ → ℕ))
    (hEA : ∀ d ∈ E, ∀ x, streamPrefix (2*n+1) x=codeEmbedding (2*n+1) d → x∈A) :
    (p.codeLaw n).real E ≤ p.streamLaw.real A / codePartition p (2*n+1) := by
  classical
  let N := 2*n+1
  let C : Code N → Set (ℕ → ℕ) := fun d => if d∈E then
    streamPrefix N ⁻¹' {codeEmbedding N d} else ∅
  have hm (d) : MeasurableSet (C d) := by
    dsimp [C]
    split_ifs
    · exact (measurableSet_singleton _).preimage (measurable_streamPrefix N)
    · exact MeasurableSet.empty
  have hd : Pairwise (fun d e => Disjoint (C d) (C e)) := by
    intro d e hde
    dsimp [C]
    split_ifs <;> try simp
    exact (Set.disjoint_singleton.mpr ((codeEmbedding N).injective.ne hde)).preimage _
  have he (d : Code N) : p.streamLaw.real (C d) = if d∈E then codeWeight p d else 0 := by
    dsimp [C]
    split_ifs
    · rw [(p.streamPrefix_hasLaw N).measurePreserving (measurable_streamPrefix N) |>.measureReal_preimage
        (measurableSet_singleton _).nullMeasurableSet]
      exact p.iid_bridge_singleton ⟨d.val,d.property.1⟩
    · simp
  have hb : (∑ d : Code N, if d∈E then codeWeight p d else 0) ≤ p.streamLaw.real A := by
    rw [← show p.streamLaw.real (⋃ d, C d)=∑ d : Code N, if d∈E then codeWeight p d else 0 by
      rw [measureReal_iUnion_fintype hd hm]; simp only [he]]
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rintro x ⟨_,⟨d,rfl⟩,hx⟩
    dsimp [C] at hx
    split_ifs at hx with hE
    · exact hEA d hE x hx
    · exact hx.elim
  rw [← integral_indicator_one (μ := p.codeLaw n) (show MeasurableSet E from trivial),p.code_integral]
  apply (le_div_iff₀ (codePartition_odd_pos p n)).mpr
  have heq : (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      E.indicator (fun _ => (1:ℝ)) d)*codePartition p (2*n+1)=
      ∑ d : Code (2*n+1), if d∈E then codeWeight p d else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [Set.indicator]
    split_ifs
    · field_simp [(codePartition_odd_pos p n).ne']
    · simp
  change (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
    E.indicator (fun _ => (1:ℝ)) d)*codePartition p (2*n+1) ≤ _
  rw [heq]
  exact hb

lemma recordHeight_congr_prefix {S T : ℕ → ℤ} {N j : ℕ} (hj : j ≤ N)
    (hST : ∀ k ≤ N, S k=T k) : recordHeight S 0 j=recordHeight T 0 j := by
  unfold recordHeight
  congr 1
  ext k
  simp only [mem_reverseRecords]
  constructor <;> rintro ⟨hk0,hkj,hk⟩ <;> refine ⟨hk0,hkj,?_⟩ <;> intro r hkr hrj
  · rw [← hST k (by omega),← hST r (by omega)]
    exact hk r hkr hrj
  · rw [hST k (by omega),hST r (by omega)]
    exact hk r hkr hrj

def codeHeightModulusFailure {N : ℕ} (m : ℕ) (c : ℝ) : Set (Code N) :=
  {d | ∃ a b, a ≤ b ∧ b ≤ N ∧
    (∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → (walk d.val u:ℝ)-(walk d.val v:ℝ)<c) ∧
    ¬(height d.val b ≤ height d.val a+m ∧ height d.val a ≤ height d.val b+m)}

lemma codeHeightModulusFailure_stream {N m : ℕ} {c : ℝ} {d : Code N}
    (hd : d∈codeHeightModulusFailure m c) {x : ℕ → ℕ}
    (hx : streamPrefix N x=codeEmbedding N d) : x∈heightModulusFailure N m c := by
  have hS (k : ℕ) (hk : k ≤ N) : integerSum x k=walk d.val k := by
    rw [← integerSum_arrayStream_prefix N x hk,hx]
    exact integerSum_arrayStream_bridge ⟨d.val,d.property.1⟩ hk
  have hH (k : ℕ) (hk : k ≤ N) : recordHeight (integerSum x) 0 k=height d.val k :=
    (recordHeight_congr_prefix hk hS).trans (height_eq_recordHeight d.val hk).symm
  obtain ⟨a,b,hab,hb,hosc,hbad⟩ := hd
  refine ⟨a,b,hab,hb,?_,?_⟩
  · intro u v hau hub hav hvb
    rw [hS u (by omega),hS v (by omega)]
    exact hosc u v hau hub hav hvb
  · simpa only [hH b hb,hH a (hab.trans hb)] using hbad

lemma CriticalEvenOffspring.code_height_modulus_bound (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0<c ∧ 0<ρ ∧ ρ<1 ∧ ∀ n m : ℕ,
      (p.codeLaw n).real (codeHeightModulusFailure m (c*m)) ≤
        ((2*n+1:ℕ)+1:ℝ)*ρ^m/codePartition p (2*n+1) := by
  obtain ⟨c,ρ,hc,hr0,hr1,hb⟩ := p.height_modulus_probability
  refine ⟨c,ρ,hc,hr0,hr1,fun n m => ?_⟩
  apply (p.code_probability_le_stream n _ _ (fun _ hd _ hx => codeHeightModulusFailure_stream hd hx)).trans
  apply div_le_div_of_nonneg_right _ (codePartition_nonneg p _)
  have hnn : 0 ≤ ((2*n+1:ℕ)+1:ℝ)*ρ^m := by positivity
  have hh' : p.streamLaw (heightModulusFailure (2*n+1) m (c*m)) ≤
      ENNReal.ofReal (((2*n+1:ℕ)+1:ℝ)*ρ^m) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((2*n+1:ℕ)+1:ℝ)),
      show ((2*n+1:ℕ):ℝ)+1=((2*n+1+1:ℕ):ℝ) by push_cast; rfl,
      ENNReal.ofReal_natCast]
    exact hb (2*n+1) m
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh'
  simpa only [measureReal_def,ENNReal.toReal_ofReal hnn] using hh

lemma CriticalEvenOffspring.code_geometric_vanish (p : CriticalEvenOffspring)
    {ε ρ : ℝ} (hε : 0<ε) (hρ : 0 ≤ ρ) (hρ1 : ρ<1) :
    Tendsto (fun n => ((2*n+1:ℕ)+1:ℝ)*ρ^⌈ε*Real.sqrt ((2*n+1:ℕ):ℝ)⌉₊ /
      codePartition p (2*n+1)) atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun n => Real.sqrt ((2*n+1:ℕ):ℝ)
  have hs0 (n) : 0 ≤ s n := Real.sqrt_nonneg _
  have h5 := polynomial_geometric_ceil odd_sqrt_tendsto hs0 hε hρ hρ1 5
  have h3 := polynomial_geometric_ceil odd_sqrt_tendsto hs0 hε hρ hρ1 3
  have hpos : 0 < 2/(p.sigma*Real.sqrt (2*Real.pi)) :=
    div_pos (by norm_num) (mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity)))
  have ht := (h5.add h3).div p.codePartition_asymptotic hpos.ne'
  simp only [zero_add,zero_div] at ht
  convert ht using 1
  funext n
  have hs : s n^2=((2*n+1:ℕ):ℝ) := Real.sq_sqrt (by positivity)
  have hsne : s n≠0 := (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))).ne'
  dsimp only [Pi.div_apply]
  rw [show (2*n+1:ℝ)=((2*n+1:ℕ):ℝ) by push_cast; rfl]
  change (((2*n+1:ℕ):ℝ)+1)*ρ^⌈ε*s n⌉₊/codePartition p (2*n+1)=
    ((s n)^5*ρ^⌈ε*s n⌉₊+(s n)^3*ρ^⌈ε*s n⌉₊)/
      (((2*n+1:ℕ):ℝ)*s n*codePartition p (2*n+1))
  have he : (s n)^5*ρ^⌈ε*s n⌉₊+(s n)^3*ρ^⌈ε*s n⌉₊ =
      (((2*n+1:ℕ):ℝ)+1)*ρ^⌈ε*s n⌉₊ * (((2*n+1:ℕ):ℝ)*s n) := by
    calc
      _ = ((s n)^2+1)*ρ^⌈ε*s n⌉₊*((s n)^2*s n) := by ring
      _ = _ := by rw [hs]
  rw [he]
  push_cast
  rw [mul_comm _ (codePartition p (2*n+1)),mul_div_mul_right]
  exact mul_ne_zero (by positivity) hsne

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

abbrev ClosePairs (δ : ℝ) := {st : unitInterval × unitInterval // dist st.1 st.2 ≤ δ}

instance (δ : ℝ) : CompactSpace (ClosePairs δ) :=
  isCompact_iff_compactSpace.mp ((isClosed_le (continuous_fst.dist continuous_snd) continuous_const).isCompact)

def oscillationPath (δ : ℝ) (f : C(unitInterval,ℝ)) : C(ClosePairs δ,ℝ) :=
  ⟨fun st => f st.val.1-f st.val.2, by fun_prop⟩

def pathOscillation (δ : ℝ) (f : C(unitInterval,ℝ)) : ℝ := ‖oscillationPath δ f‖

lemma pathOscillation_nonneg (δ : ℝ) (f : C(unitInterval,ℝ)) : 0 ≤ pathOscillation δ f := norm_nonneg _

lemma pathOscillation_le {δ M : ℝ} (hM : 0 ≤ M) (f : C(unitInterval,ℝ))
    (h : ∀ s t, dist s t ≤ δ → |f s-f t| ≤ M) : pathOscillation δ f ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro st
  exact h st.val.1 st.val.2 st.property

lemma sub_le_pathOscillation {δ : ℝ} (f : C(unitInterval,ℝ)) {s t : unitInterval}
    (hst : dist s t ≤ δ) : |f s-f t| ≤ pathOscillation δ f :=
  (oscillationPath δ f).norm_coe_le_norm ⟨(s,t),hst⟩

lemma pathOscillation_lipschitz (δ : ℝ) : LipschitzWith 2 (pathOscillation δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  apply (dist_norm_norm_le (oscillationPath δ f) (oscillationPath δ g)).trans
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro st
  change |(f st.val.1-f st.val.2)-(g st.val.1-g st.val.2)| ≤ (2:ℝ≥0)*‖f-g‖
  have h1 := (f-g).norm_coe_le_norm st.val.1
  have h2 := (f-g).norm_coe_le_norm st.val.2
  change |f st.val.1-g st.val.1| ≤ ‖f-g‖ at h1
  change |f st.val.2-g st.val.2| ≤ ‖f-g‖ at h2
  have ht := abs_sub ((f-g) st.val.1) ((f-g) st.val.2)
  simp only [ContinuousMap.sub_apply] at ht
  have he : (f st.val.1-f st.val.2)-(g st.val.1-g st.val.2)=
      (f st.val.1-g st.val.1)-(f st.val.2-g st.val.2) := by ring
  rw [he]
  change _ ≤ 2*‖f-g‖
  linarith

lemma pathOscillation_vanish (f : C(unitInterval,ℝ)) :
    Tendsto (fun j : ℕ => pathOscillation (1/(j+1:ℝ)) f) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε/2) (by positivity)
  have ht : Tendsto (fun j : ℕ => 1/(j+1:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with j hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (pathOscillation_nonneg _ _)]
  apply lt_of_le_of_lt (pathOscillation_le (by positivity : 0 ≤ ε/2) f ?_) (by linarith)
  intro s t hst
  exact (hd (hst.trans_lt hj)).le


local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

def oscillationGauge (δ ε : ℝ) (f : C(unitInterval,ℝ)) := min 1 (pathOscillation δ f/ε)

lemma oscillationGauge_continuous (δ ε : ℝ) : Continuous (oscillationGauge δ ε) :=
  continuous_const.min ((pathOscillation_lipschitz δ).continuous.div_const ε)

lemma oscillationGauge_nonneg (δ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (f : C(unitInterval,ℝ)) :
    0 ≤ oscillationGauge δ ε f := le_min (by norm_num) (div_nonneg (pathOscillation_nonneg _ _) hε)

lemma oscillationGauge_abs_le (δ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (f : C(unitInterval,ℝ)) :
    |oscillationGauge δ ε f| ≤ 1 := by
  rw [abs_of_nonneg (oscillationGauge_nonneg δ hε f)]
  exact min_le_left _ _

lemma oscillationGauge_integral_vanish {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun j : ℕ => ∫ ω, oscillationGauge (1/(j+1:ℝ)) ε (X ω) ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (F := fun j ω => oscillationGauge (1/(j+1:ℝ)) ε (X ω)) (f := fun _=>0)
    (fun j => ((oscillationGauge_continuous _ ε).measurable.comp_aemeasurable hX).aestronglyMeasurable)
    (integrable_const _) (fun _ => ae_of_all μ (fun _ => oscillationGauge_abs_le _ hε.le _)) (by
      apply ae_of_all
      intro ω
      have ht := tendsto_const_nhds.min ((pathOscillation_vanish (X ω)).div_const ε)
        (f := fun _ : ℕ => (1:ℝ))
      simpa only [oscillationGauge,zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1)] using ht)
  simpa only [integral_zero] using hh

lemma oscillation_probability_le_gauge {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : Measurable X) (δ : ℝ) {ε : ℝ} (hε : 0<ε) :
    μ.real {ω | ε<pathOscillation δ (X ω)} ≤ ∫ ω,oscillationGauge δ ε (X ω) ∂μ := by
  have hg : Integrable (fun ω => oscillationGauge δ ε (X ω)) μ :=
    Integrable.of_bound ((oscillationGauge_continuous _ _).measurable.comp hX).aestronglyMeasurable 1
      (ae_of_all μ (fun _ => oscillationGauge_abs_le _ hε.le _))
  let E := {ω | ε<pathOscillation δ (X ω)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const ((pathOscillation_lipschitz δ).continuous.measurable.comp hX)
  rw [← integral_indicator_one hE]
  apply integral_mono ((integrable_const (1:ℝ)).indicator hE) hg
  intro ω
  by_cases hω : ω∈E
  · rw [Set.indicator_of_mem hω]
    exact le_min le_rfl ((le_div_iff₀ hε).mpr (by simpa using hω.le))
  · rw [Set.indicator_of_notMem hω]
    exact oscillationGauge_nonneg δ hε.le _

lemma continuousPath_modulus_tight {Ω : ℕ → Type*} {Ω' : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n, Measure (Ω n)} {ν : Measure Ω'} [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n, Ω n → C(unitInterval,ℝ)} {Y : Ω' → C(unitInterval,ℝ)}
    (h : TendstoInDistribution X atTop Y μ ν) (hXm : ∀ n, Measurable (X n))
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ n in atTop,
      (μ n).real {ω | ε<pathOscillation δ (X n ω)} ≤ η := by
  obtain ⟨j,hj⟩ := ((oscillationGauge_integral_vanish h.aemeasurable_limit hε).eventually
    (gt_mem_nhds (half_pos hη))).exists
  refine ⟨1/(j+1:ℝ),by positivity,?_⟩
  have ht := integral_tendsto_of_tendstoInDistribution h (oscillationGauge_continuous (1/(j+1:ℝ)) ε)
    (oscillationGauge_abs_le _ hε.le)
  filter_upwards [ht.eventually (gt_mem_nhds (hj.trans (half_lt_self hη)))] with n hn
  exact (oscillation_probability_le_gauge (hXm n) _ hε).trans hn.le

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma height_pair_control {N m a b : ℕ} {c : ℝ} {d : Code N}
    (hgood : d∉codeHeightModulusFailure m c) (hb : b ≤ N)
    (hosc : ∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → (walk d.val u:ℝ)-(walk d.val v:ℝ)<c)
    {u v : ℕ} (hau : a ≤ u) (hub : u ≤ b) (hav : a ≤ v) (hvb : v ≤ b) :
    |(height d.val u:ℝ)-(height d.val v:ℝ)| ≤ m := by
  have hh {j k : ℕ} (hjk : j ≤ k) (haj : a ≤ j) (hkb : k ≤ b) :
      height d.val k ≤ height d.val j+m ∧ height d.val j ≤ height d.val k+m := by
    by_contra hn
    exact hgood ⟨j,k,hjk,hkb.trans hb,fun s t hjs hsk hjt htk =>
      hosc s t (haj.trans hjs) (hsk.trans hkb) (haj.trans hjt) (htk.trans hkb),hn⟩
  obtain h₁|h₁ := le_total u v
  · have hh' := hh h₁ hau hvb
    have h2 : (height d.val v:ℝ) ≤ height d.val u+m := by exact_mod_cast hh'.1
    have h3 : (height d.val u:ℝ) ≤ height d.val v+m := by exact_mod_cast hh'.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · have hh' := hh h₁ hav hub
    have h2 : (height d.val u:ℝ) ≤ height d.val v+m := by exact_mod_cast hh'.1
    have h3 : (height d.val v:ℝ) ≤ height d.val u+m := by exact_mod_cast hh'.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma error_le_error_add {w₁ w₂ h₁ h₂ ν a b : ℝ} (hν : 0 ≤ ν)
    (hw : |w₁-w₂| ≤ a) (hh : |h₁-h₂| ≤ b) :
    |w₁-ν*h₁| ≤ |w₂-ν*h₂|+a+ν*b := by
  have he : w₁-ν*h₁=(w₂-ν*h₂)+(w₁-w₂)-ν*(h₁-h₂) := by ring
  rw [he]
  have ht := (abs_sub ((w₂-ν*h₂)+(w₁-w₂)) (ν*(h₁-h₂))).trans
    (add_le_add (abs_add_le (w₂-ν*h₂) (w₁-w₂)) le_rfl)
  rw [abs_mul,abs_of_nonneg hν] at ht
  nlinarith

lemma badHeightFraction_interval_lower {N r a : ℕ} (har : a+r ≤ N)
    {ν t : ℝ} (d : Code N)
    (hbad : ∀ k<r, t< |(walk d.val (a+k):ℝ)-ν*height d.val (a+k)|) :
    (r:ℝ)/(N:ℝ) ≤ badHeightFraction ν t d := by
  classical
  let f : Fin r → Fin N := fun k => ⟨a+k.val,by omega⟩
  let S := Finset.univ.filter (fun k : Fin N => t< |(walk d.val k.val:ℝ)-ν*height d.val k.val|)
  have hm : ∀ k : Fin r, f k∈S := fun k => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad k.val k.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hh := congrArg Fin.val hij
    dsimp [f] at hh
    exact Fin.ext (by omega)
  have hc : r ≤ S.card := by
    have hh := Finset.card_le_card (show Finset.univ.image f ⊆ S by
      intro k hk
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
      exact hm i)
    simpa only [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin] using hh
  unfold badHeightFraction
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [← Finset.sum_filter]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using (show (r:ℝ) ≤ S.card by exact_mod_cast hc)

lemma uniform_error_of_average {N m r : ℕ} {ν c a t : ℝ} (d : Code N)
    (hν : 0 ≤ ν) (hr : r ≤ N) (hgood : d∉codeHeightModulusFailure m c)
    (hosc : ∀ u v, u ≤ N → v ≤ N → (u:ℤ)-v ≤ r → (v:ℤ)-u ≤ r →
       |(walk d.val u:ℝ)-(walk d.val v:ℝ)| ≤ a)
    (hac : a<c)
    (havg : badHeightFraction ν t d < (r:ℝ)/(N:ℝ)) :
    ∀ j<N, |(walk d.val j:ℝ)-ν*height d.val j| ≤ t+a+ν*m := by
  intro j hj
  by_contra hn
  have hjbad : t+a+ν*m< |(walk d.val j:ℝ)-ν*height d.val j| := lt_of_not_ge hn
  let b := min j (N-r)
  have hbj : b ≤ j := min_le_left _ _
  have hbr : b+r ≤ N := by have := min_le_right j (N-r); dsimp [b]; omega
  have hjbr : j ≤ b+r := by dsimp [b]; omega
  have hw (u v : ℕ) (hbu : b ≤ u) (hub : u ≤ b+r) (hbv : b ≤ v) (hvb : v ≤ b+r) :
      |(walk d.val u:ℝ)-(walk d.val v:ℝ)| ≤ a := hosc u v (by omega) (by omega) (by omega) (by omega)
  have hlocal : ∀ u v, b ≤ u → u ≤ b+r → b ≤ v → v ≤ b+r →
      (walk d.val u:ℝ)-(walk d.val v:ℝ)<c := by
    intro u v hbu hub hbv hvb
    exact (le_abs_self _).trans_lt ((hw u v hbu hub hbv hvb).trans_lt hac)
  have hfrac := badHeightFraction_interval_lower (ν := ν) (t := t) hbr d (fun k hk => ?_)
  · exact (not_lt_of_ge hfrac) havg
  have hH := height_pair_control hgood hbr hlocal hbj hjbr (by omega : b ≤ b+k) (by omega : b+k ≤ b+r)
  have hW := hw j (b+k) hbj hjbr (by omega) (by omega)
  have he := error_le_error_add hν hW hH
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

lemma CriticalEvenOffspring.codeWalk_converges (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => walkPolygon p.sigma d.val) atTop
      (fun ω => vervaat (bridgePath B ω)) p.codeLaw P := by
  have hX (n : ℕ) : AEMeasurable (fun d : Code (2*n+1) => walkPolygon p.sigma d.val) (p.codeLaw n) :=
    (measurable_of_countable _).aemeasurable
  have hY := (p.iidVervaat_CLT hB).aemeasurable_limit
  refine ⟨hX,hY,?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  change Tendsto (fun n => ∫ f,F f ∂(p.codeLaw n).map (fun d => walkPolygon p.sigma d.val)) atTop
    (𝓝 (∫ f,F f ∂P.map (fun ω => vervaat (bridgePath B ω))))
  simp_rw [integral_map (hX _) F.continuous.aestronglyMeasurable,
    integral_map hY F.continuous.aestronglyMeasurable,p.code_integral]
  exact p.codeWalk_CLT hB F

lemma gridPoint_dist_le {N r u v : ℕ} (_hN : 0<N) (hu : u ≤ N) (hv : v ≤ N)
    (huv : (u:ℤ)-v ≤ r) (hvu : (v:ℤ)-u ≤ r) :
    dist (gridPoint N ⟨u,by omega⟩) (gridPoint N ⟨v,by omega⟩) ≤ (r:ℝ)/(N:ℝ) := by
  change |(u:ℝ)/(N:ℝ)-(v:ℝ)/(N:ℝ)| ≤ (r:ℝ)/(N:ℝ)
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply abs_le.mpr
  constructor
  · have hh : (v:ℝ)-(u:ℝ) ≤ r := by exact_mod_cast hvu
    linarith
  · exact_mod_cast huv

lemma walk_grid_oscillation {N r : ℕ} (hN : 0<N) {σ δ θ : ℝ} (hσ : 0<σ)
    (d : Code N) (hr : (r:ℝ)/(N:ℝ) ≤ δ)
    (hosc : pathOscillation δ (walkPolygon σ d.val) ≤ θ) :
    ∀ u v, u ≤ N → v ≤ N → (u:ℤ)-v ≤ r → (v:ℤ)-u ≤ r →
      |(walk d.val u:ℝ)-(walk d.val v:ℝ)| ≤ θ*(σ*Real.sqrt N) := by
  intro u v hu hv huv hvu
  have hp := (sub_le_pathOscillation (walkPolygon σ d.val) ((gridPoint_dist_le hN hu hv huv hvu).trans hr)).trans hosc
  simp only [walkPolygon,interpolation_gridPoint hN] at hp
  rw [← sub_div,abs_div,abs_of_pos (mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)))] at hp
  exact (div_le_iff₀ (mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)))).mp hp

lemma floor_fraction_bounds {δ : ℝ} (hδ : 0<δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : 0<N)
    (hlarge : 2 ≤ δ*N) :
    ⌊δ*N⌋₊ ≤ N ∧ (⌊δ*N⌋₊:ℝ)/(N:ℝ) ≤ δ ∧ δ/2 ≤ (⌊δ*N⌋₊:ℝ)/(N:ℝ) := by
  have hN0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hfloor := Nat.floor_le (mul_nonneg hδ.le hN0.le)
  have hfloor' := Nat.lt_floor_add_one (δ*N)
  constructor
  · exact_mod_cast hfloor.trans (mul_le_of_le_one_left hN0.le hδ1)
  constructor
  · exact (div_le_iff₀ hN0).mpr hfloor
  · apply (le_div_iff₀ hN0).mpr
    linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

lemma CriticalEvenOffspring.bad_fraction_markov (p : CriticalEvenOffspring) (n : ℕ) (ν a : ℝ)
    {t : ℝ} (ht : 0<t) :
    (p.codeLaw n).real {d | t ≤ badHeightFraction ν a d} ≤
      (∫ d,badHeightFraction ν a d ∂p.codeLaw n)/t := by
  apply (le_div_iff₀ ht).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := p.codeLaw n) (f := badHeightFraction ν a)
    (ae_of_all _ (fun d => badHeightFraction_nonneg ν a d)) (Integrable.of_finite) t
  simpa only [mul_comm] using hh

/-- Exact conditioned critical finite-variance height/walk coupling, uniformly
at every depth-first vertex. Only the stated second moment is used. -/
theorem CriticalEvenOffspring.uniform_height_error_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {d | ∃ j<2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |(walk d.val j:ℝ)-(p.variance/2)*height d.val j|})
      atTop (𝓝 0) := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hmod⟩ := p.code_height_modulus_bound
  let ν := p.variance/2
  have hν : 0<ν := half_pos p.variance_pos
  let κ := ε/(8*ν)
  have hκ : 0<κ := div_pos hε (by positivity)
  have hκeq : ν*κ=ε/8 := by dsimp [κ]; field_simp
  let θ := min (ε/(4*p.sigma)) (c*κ/(2*p.sigma))
  have hσ := p.sigma_pos
  have hθ : 0<θ := lt_min (div_pos hε (by positivity)) (div_pos (mul_pos hc hκ) (by positivity))
  have hθε : θ*p.sigma ≤ ε/4 := by
    calc
      _ ≤ (ε/(4*p.sigma))*p.sigma := mul_le_mul_of_nonneg_right (min_le_left _ _) hσ.le
      _ = _ := by field_simp
  have hθc : θ*p.sigma ≤ c*κ/2 := by
    calc
      _ ≤ (c*κ/(2*p.sigma))*p.sigma := mul_le_mul_of_nonneg_right (min_le_right _ _) hσ.le
      _ = _ := by field_simp
  have hgeo := p.code_geometric_vanish hκ hρ.le hρ1
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  intro η hη
  obtain ⟨δ₀,hδ₀,hwalk⟩ := continuousPath_modulus_tight (p.codeWalk_converges hB)
    (fun _ => measurable_of_countable _) hθ (by positivity : 0<η/3)
  let δ := min δ₀ 1
  have hδ : 0<δ := lt_min hδ₀ (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hmean := (p.average_height_error_limit (by positivity : 0<ε/4)).div_const (δ/2)
  simp only [zero_div] at hmean
  have hlargeν : ∀ᶠ n in atTop, ν ≤ ε/8*Real.sqrt ((2*n+1:ℕ):ℝ) :=
    (odd_sqrt_tendsto.const_mul_atTop (by positivity : 0<ε/8)).eventually_ge_atTop ν
  have hlarger : ∀ᶠ n in atTop, 2 ≤ δ*((2*n+1:ℕ):ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp odd_size_tendsto).const_mul_atTop hδ).eventually_ge_atTop 2
  filter_upwards [hwalk,hlargeν,hlarger,
    hgeo.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/3)),
    hmean.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/3))] with n hwn hνn hrn hgn han
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let m := ⌈κ*s⌉₊
  let r := ⌊δ*N⌋₊
  have hN : 0<N := by dsimp [N]; omega
  have hs : 0<s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hmν : ν*m ≤ ε/4*s := by
    have hm := (Nat.ceil_lt_add_one (mul_nonneg hκ.le hs.le)).le
    have hh := mul_le_mul_of_nonneg_left hm hν.le
    have he := congrArg (fun t : ℝ => t*s) hκeq
    change ν ≤ ε/8*s at hνn
    dsimp [m]
    nlinarith
  have hcm : θ*(p.sigma*s)<c*m := by
    have hm : κ*s ≤ (m:ℝ) := Nat.le_ceil _
    have hh := mul_le_mul_of_nonneg_left hm hc.le
    have hth := mul_le_mul_of_nonneg_right hθc hs.le
    have hcs : 0<c*κ*s := by positivity
    nlinarith
  have hθεs : θ*(p.sigma*s) ≤ ε/4*s := by nlinarith [mul_le_mul_of_nonneg_right hθε hs.le]
  have hr := floor_fraction_bounds hδ hδ1 hN hrn
  let A := {d : Code N | θ<pathOscillation δ₀ (walkPolygon p.sigma d.val)}
  let C := codeHeightModulusFailure m (c*m) (N := N)
  let D := {d : Code N | δ/2 ≤ badHeightFraction ν (ε/4*s) d}
  have hsub : {d : Code N | ∃ j<N, ε*s< |(walk d.val j:ℝ)-ν*height d.val j|} ⊆ (A ∪ C) ∪ D := by
    intro d hd
    by_contra hn
    have hh : ¬d∈A ∧ ¬d∈C ∧ ¬d∈D := by simpa only [Set.mem_union,not_or,and_assoc] using hn
    have hw : pathOscillation δ₀ (walkPolygon p.sigma d.val) ≤ θ := not_lt.mp hh.1
    have havg : badHeightFraction ν (ε/4*s) d < (r:ℝ)/(N:ℝ) :=
      (lt_of_not_ge hh.2.2).trans_le hr.2.2
    have hu := uniform_error_of_average d hν.le hr.1 hh.2.1
      (walk_grid_oscillation hN p.sigma_pos d (hr.2.1.trans hδδ₀) hw) hcm havg
    obtain ⟨j,hj,hjbad⟩ := hd
    have hjle := hu j hj
    linarith
  have hb := (measureReal_mono (μ := p.codeLaw n) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le (A ∪ C) D).trans (add_le_add (measureReal_union_le A C) le_rfl))
  have hA : (p.codeLaw n).real A ≤ η/3 := hwn
  have hC : (p.codeLaw n).real C < η/3 := (hmod n m).trans_lt hgn
  have hD : (p.codeLaw n).real D < η/3 :=
    (p.bad_fraction_markov n ν (ε/4*s) (half_pos hδ)).trans_lt han
  exact hb.trans_lt (by linarith)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩

/-- Converging together with varying sample spaces and actual probability laws. -/
theorem tendstoInDistribution_of_close {E Ω' : Type*} {Ω : ℕ → Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n, Measure (Ω n)} {ν : Measure Ω'} [∀ n, IsProbabilityMeasure (μ n)]
    [IsProbabilityMeasure ν] {X Y : ∀ n, Ω n → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X atTop Z μ ν)
    (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hclose : ∀ ε>0, Tendsto (fun n => (μ n).real {ω | ε < dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z μ ν := by
  refine ⟨hY,hXZ.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  have hZ := hXZ.aemeasurable_limit
  have hmid := tendsto_iff_forall_lipschitz_integral_tendsto.mp hXZ.tendsto F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ x,F x ∂(μ n).map (Y n)) atTop (𝓝 (∫ x,F x ∂ν.map Z))
  change Tendsto (fun n => ∫ x,F x ∂(μ n).map (X n)) atTop (𝓝 (∫ x,F x ∂ν.map Z)) at hmid
  simp_rw [integral_map (hY _) hL.continuous.aestronglyMeasurable,
    integral_map hZ hL.continuous.aestronglyMeasurable]
  simp_rw [integral_map (hXZ.forall_aemeasurable _) hL.continuous.aestronglyMeasurable,
    integral_map hZ hL.continuous.aestronglyMeasurable] at hmid
  have hM0 : 0≤M := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure ν
    simpa using hM (Z ω) (Z ω)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(4*((L:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hLd : (L:ℝ)*δ ≤ ε/4 := by
    dsimp [δ]; rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0<4*((L:ℝ)+1))]
    nlinarith [L.coe_nonneg]
  have htail := (hclose (δ/2) (half_pos hδ)).const_mul M
  simp only [mul_zero] at htail
  filter_upwards [htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/4)),
    (Metric.tendsto_nhds.mp hmid) (ε/4) (by positivity)] with n hn hnmid
  have he := integral_lipschitz_approx_bound (hY n) (hXZ.forall_aemeasurable n) hM hL hδ.le
  have hs : (μ n).real {ω | δ ≤ dist (Y n ω) (X n ω)} ≤
      (μ n).real {ω | δ/2 < dist (X n ω) (Y n ω)} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change δ ≤ dist (Y n ω) (X n ω) at hω
    change δ/2 < dist (X n ω) (Y n ω)
    rw [dist_comm] at hω
    exact lt_of_lt_of_le (by linarith) hω
  have hh := mul_le_mul_of_nonneg_left hs hM0
  have ht := abs_sub_le (∫ ω,F (Y n ω) ∂μ n) (∫ ω,F (X n ω) ∂μ n) (∫ ω,F (Z ω) ∂ν)
  rw [Real.dist_eq] at hnmid ⊢
  linarith

def diagonalPath (f : C(unitInterval,ℝ)) : C(unitInterval,ℝ×ℝ) := f.prodMk f

lemma diagonalPath_lipschitz : LipschitzWith 1 diagonalPath := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le (dist_nonneg)).mpr
  intro t
  change max (dist (f t) (g t)) (dist (f t) (g t)) ≤ dist f g
  simpa only [max_self] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t

lemma jointCode_close {N : ℕ} (hN : 0<N) (p : CriticalEvenOffspring) (d : Code N)
    {ε : ℝ} (hε : 0≤ε)
    (h : ∀ j≤N, |(walk d.val j:ℝ)-(p.variance/2)*height d.val j| ≤ ε*p.sigma*Real.sqrt N) :
    dist (diagonalPath (walkPolygon p.sigma d.val)) (jointCode p.sigma d) ≤ ε := by
  have hs := p.sigma_pos
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hsq : p.sigma^2=p.variance := Real.sq_sqrt p.variance_pos.le
  have hb := interpolation_diff_bound N
    (fun i => (walk d.val i.val:ℝ)/(p.sigma*Real.sqrt N))
    (fun i => p.sigma*height d.val i.val/(2*Real.sqrt N)) hε (fun i => ?_)
  · apply (ContinuousMap.dist_le hε).mpr
    intro t
    change max (dist (walkPolygon p.sigma d.val t) (walkPolygon p.sigma d.val t))
      (dist (walkPolygon p.sigma d.val t)
        (interpolation N (fun i => p.sigma*height d.val i.val/(2*Real.sqrt N)) t)) ≤ ε
    rw [dist_self,max_eq_right (dist_nonneg)]
    exact (ContinuousMap.dist_apply_le_dist t).trans (by simpa only [walkPolygon,dist_eq_norm] using hb)
  have he : (walk d.val i.val:ℝ)/(p.sigma*Real.sqrt N)-
      p.sigma*height d.val i.val/(2*Real.sqrt N) =
      ((walk d.val i.val:ℝ)-(p.variance/2)*height d.val i.val)/(p.sigma*Real.sqrt N) := by
    field_simp
    nlinarith [congrArg (fun x : ℝ => x*(height d.val i.val:ℝ)) hsq]
  rw [he,abs_div,abs_of_pos (mul_pos hs hsqrt)]
  apply (div_le_iff₀ (mul_pos hs hsqrt)).mpr
  simpa only [mul_assoc] using h i.val (Nat.le_of_lt_succ i.isLt)

lemma CriticalEvenOffspring.joint_diagonal_close (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {d | ε <
      dist (diagonalPath (walkPolygon p.sigma d.val)) (jointCode p.sigma d)}) atTop (𝓝 0) := by
  have hsmall := p.uniform_height_error_limit hB (mul_pos hε p.sigma_pos)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsmall
  have hlarge : ∀ᶠ n in atTop, 1 ≤ (ε*p.sigma)*Real.sqrt ((2*n+1:ℕ):ℝ) :=
    (odd_sqrt_tendsto.const_mul_atTop (mul_pos hε p.sigma_pos)).eventually_ge_atTop 1
  filter_upwards [hlarge] with n hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro d hd
  by_contra hh
  have he : ∀ j<2*n+1, |(walk d.val j:ℝ)-(p.variance/2)*height d.val j| ≤
      (ε*p.sigma)*Real.sqrt ((2*n+1:ℕ):ℝ) := by simpa only [Set.mem_ofPred_eq,not_exists,not_and,not_lt] using hh
  apply not_lt_of_ge (jointCode_close (by omega) p d hε.le (fun j hj => ?_)) hd
  by_cases hj' : j<2*n+1
  · exact he j hj'
  · have hjj : j=2*n+1 := by omega
    subst j
    simpa only [d.property.1,height_terminal,Nat.cast_zero,mul_zero,sub_zero,Int.cast_neg,
      Int.cast_one,abs_neg,abs_one] using hn

/-- Full joint walk/height convergence to the same Vervaat bridge excursion.
Identification with the standard Bessel3 excursion uses its finite-dimensional laws. -/
theorem CriticalEvenOffspring.jointCode_vervaat_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => jointCode p.sigma d) atTop
      (fun ω => diagonalPath (vervaat (bridgePath B ω))) p.codeLaw P := by
  have hc := (p.codeWalk_converges hB).continuous_comp diagonalPath_lipschitz.continuous
  exact tendstoInDistribution_of_close hc (fun _ => (measurable_of_countable _).aemeasurable)
    (fun _ hε => p.joint_diagonal_close hB hε)

end FKCRT.TreeCoding
end

end OAI
