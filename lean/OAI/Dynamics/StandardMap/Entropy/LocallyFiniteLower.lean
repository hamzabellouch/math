import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.PhysicalVolume

namespace OAI

section
section
namespace StandardMapEntropy.LocalCoding
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def codeFiber (f : Ω → Ω) (p : Ω → ι) (N : ℕ) (x : Ω) : Set Ω :=
  {y | ∀ i : ℕ,i≤N → p (f^[i] y)=p (f^[i] x)}

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [MeasurableSpace Ω] in
lemma masked_history_none_iff (f : Ω → Ω) (p : Ω → ι) (S : ι → Finset ι) (A : Finset ι) (N : ℕ) (x : Ω) :
    Entropy.history (maskedState A (reach S A N) f p) (N+1) x=(fun _ => none) ↔ p x∉A := by
  constructor
  · intro hx
    have h0 := congrFun hx ⟨0,by omega⟩
    exact (maskedState_zero_none A _ (base_subset_reach S A N) f p x).mp h0
  · intro hx
    funext i
    exact maskedState_of_not_mem A _ f p i.val hx

omit [IsProbabilityMeasure μ] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma masked_history_small_atoms (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → ι) (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) (A : Finset ι) (N : ℕ) (I : ℝ)
    (hsmall : ∀ᵐ x ∂μ, μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-I)))
    (v : Fin (N+1) → Option (reach S A N)) (hv : v≠fun _ => none) :
    Entropy.mass μ (Entropy.history (maskedState A (reach S A N) f p) (N+1)) v≤Real.exp (-I) := by
  let q := Entropy.history (maskedState A (reach S A N) f p) (N+1)
  by_cases hz : μ (q ⁻¹' {v})=0
  · change (μ (q ⁻¹' {v})).toReal ≤ _
    rw [hz,ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · obtain ⟨x,hx,hpath,hsm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hz
      (((ae_transition_orbit μ f hf p S hS).and hsmall).filter_mono Measure.absolutelyContinuous_restrict.ae_le)
    have hA : p x∈A := by
      by_contra hnot
      exact hv (hx.symm.trans ((masked_history_none_iff f p S A N x).mpr hnot))
    have hsub : q ⁻¹' {v}⊆codeFiber f p N x := by
      intro y hy i hi
      have hr : p (f^[i] x)∈reach S A N := reach_mono S A hi
        (path_mem_reach S A (fun j => p (f^[j] x)) hA hpath i)
      have he : maskedState A (reach S A N) f p i y=truncate (reach S A N) (p (f^[i] x)) := by
        have ht := congrFun (hy.trans hx.symm) ⟨i,by omega⟩
        exact ht.trans (maskedState_of_mem A _ f p i hA)
      rw [truncate_some _ _ hr] at he
      by_cases hyA : p y∈A
      · rw [maskedState_of_mem A _ f p i hyA] at he
        exact (truncate_eq_some_iff _ _ _).mp he
      · rw [maskedState_of_not_mem A _ f p i hyA] at he
        cases he
    have hle := (measure_mono hsub).trans hsm
    exact (ENNReal.toReal_mono (by simp) hle).trans_eq (ENNReal.toReal_ofReal (Real.exp_pos _).le)

lemma masked_history_entropy_lower (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → ι) (hp : Measurable p) (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x))
    (A : Finset ι) (N : ℕ) (I : ℝ)
    (hsmall : ∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-I))) :
    (1-(μ {x | p x∉A}).toReal)*I≤
      Entropy.obs μ (Entropy.history (maskedState A (reach S A N) f p) (N+1)) := by
  have hh := Entropy.obs_lower_small_atoms μ _
    (Entropy.history_measurable _ (measurable_maskedState A _ f p hf.measurable hp) _)
    (fun _ => none) I (masked_history_small_atoms μ f hf p S hS A N I hsmall)
  have he : (Entropy.history (maskedState A (reach S A N) f p) (N+1)) ⁻¹' {fun _ => none}={x | p x∉A} := by
    ext x
    exact masked_history_none_iff f p S A N x
  simpa only [Entropy.mass,he] using hh

omit [DecidableEq ι] in
lemma tendsto_code_tail (p : Ω → ι) (hp : Measurable p) :
    Tendsto (fun A : Finset ι => (μ {x | p x∉A}).toReal) atTop (𝓝 0) := by
  have hm : Monotone (fun A : Finset ι => {x : Ω | p x∈A}) := fun A B h x hx => h hx
  have hu : (⋃ A : Finset ι,{x : Ω | p x∈A})=univ := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq,mem_univ,iff_true]
    exact ⟨{p x},Finset.mem_singleton_self _⟩
  have ht := tendsto_measure_iUnion_atTop (μ:=μ) hm
  rw [hu,measure_univ] at ht
  have hr := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
  have hc := (tendsto_const_nhds (x:=(1 : ℝ))).sub hr
  convert hc using 1
  · funext A
    have hset : MeasurableSet {x : Ω | p x∈A} := hp A.measurableSet
    rw [show {x : Ω | p x∉A}={x | p x∈A}ᶜ from rfl,measure_compl hset (measure_ne_top _ _),measure_univ,
      ENNReal.toReal_sub_of_le (show μ {x | p x∈A}≤1 by simpa only [measure_univ] using (measure_mono (μ:=μ) (subset_univ {x | p x∈A}))) ENNReal.one_ne_top,ENNReal.toReal_one]
    rfl
  · norm_num

lemma lower_rate_truncation (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → ι) (hp : Measurable p)
    (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) {D : ℕ} (hD : 0<D)
    (hcard : ∀ x,(S x).card≤D) (a b : ℝ)
    (hsmall : ∀ N : ℕ,∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-(a*(N : ℝ)-b))))
    (A K : Finset ι) :
    (1-(μ {x | p x∉A}).toReal)*a≤Entropy.rate μ f (truncate K ∘ p)+(μ {x | p x∉K}).toReal*Real.log (D : ℝ) := by
  let t := (μ {x | p x∉K}).toReal*Real.log (D : ℝ)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hdiv (c : ℝ) : Tendsto (fun n : ℕ => c/((n : ℝ)+1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have hratio : Tendsto (fun n : ℕ => (n : ℝ)/((n : ℝ)+1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x:=(1 : ℝ))).sub (hdiv 1)
    convert h using 1
    · funext n; field_simp; ring
    · ring_nf
  have hl := (tendsto_const_nhds (x:=1-(μ {x | p x∉A}).toReal)).mul ((hratio.const_mul a).sub (hdiv b))
  have hr := (((Entropy.rate_tendsto μ f hf (truncate K ∘ p) ((measurable_truncate K).comp hp)).comp
    (tendsto_add_atTop_nat 1)).add (hdiv (Real.log ((A.card : ℝ)+1)))).add (hratio.mul_const t)
  have hl' := hl
  simp only [mul_one,sub_zero] at hl'
  have hr' := hr
  simp only [add_zero,one_mul] at hr'
  apply le_of_tendsto_of_tendsto hl' hr'
  apply Filter.Eventually.of_forall
  intro n
  have hh := (masked_history_entropy_lower μ f hf p hp S hS A n (a*(n : ℝ)-b) (hsmall n)).trans
    (masked_history_entropy_upper μ f hf p hp S hS hD hcard A K n)
  have hd : (0 : ℝ)<(n : ℝ)+1 := by positivity
  have hh' := div_le_div_of_nonneg_right hh hd.le
  convert hh' using 1 <;> simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one,t] <;> field_simp

theorem lower_of_finite_rate_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → ι) (hp : Measurable p)
    (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) {D : ℕ} (hD : 0<D)
    (hcard : ∀ x,(S x).card≤D) (a b c : ℝ)
    (hsmall : ∀ N : ℕ,∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-(a*(N : ℝ)-b))))
    (hc : ∀ K : Finset ι,Entropy.rate μ f (truncate K ∘ p)≤c) : a≤c := by
  have hK (K : Finset ι) : a≤c+(μ {x | p x∉K}).toReal*Real.log (D : ℝ) := by
    have ht := ((tendsto_const_nhds (x:=(1 : ℝ))).sub (tendsto_code_tail μ p hp)).mul_const a
    have hh := le_of_tendsto' ht (fun A : Finset ι =>
      (lower_rate_truncation μ f hf p hp S hS hD hcard a b hsmall A K).trans (add_le_add (hc K) le_rfl))
    simpa only [sub_zero,one_mul] using hh
  have hh := ge_of_tendsto' (((tendsto_code_tail μ p hp).mul_const (Real.log (D : ℝ))).const_add c) hK
  simpa only [zero_mul,add_zero] using hh

end StandardMapEntropy.LocalCoding

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma complexProjection_sub (z w : ℂ) : complexProjection (z-w)=complexProjection z-complexProjection w := by
  ext <;> simp only [complexProjection,Complex.sub_re,Complex.sub_im,Prod.fst_sub,Prod.snd_sub,QuotientAddGroup.mk_sub]

lemma adaptive_rep_radius (k χ ε δ : ℝ) (hδ : 0<δ) {z w : Torus}
    (h : adaptiveLabel (codingLevel k χ ε δ hδ) z=adaptiveLabel (codingLevel k χ ε δ hδ) w) :
    ‖complexRep z-complexRep w‖≤2*codingRadius k χ ε δ w := by
  have hh := adaptiveLabel_rep_close h
  rw [adaptiveLabel_level h] at hh
  exact hh.trans (by simpa only [←mul_div_assoc,mul_one] using
    mul_le_mul_of_nonneg_left (codingLevel_size k χ ε δ hδ w) (by norm_num : (0 : ℝ)≤2))

lemma adaptive_lift_difference (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hδ : 0<δ)
    (N : ℕ) (x y : Torus)
    (hword : ∀ j : ℕ,j≤N → adaptiveLabel (codingLevel k χ ε δ hδ) ((standardMap k)^[j] y)=
      adaptiveLabel (codingLevel k χ ε δ hδ) ((standardMap k)^[j] x)) :
    ∀ j : ℕ,j≤N → (standardLift k)^[j] (complexRep y)-(standardLift k)^[j] (complexRep x)=
      complexRep ((standardMap k)^[j] y)-complexRep ((standardMap k)^[j] x) := by
  let L := 9*growthBase k
  have hL : 0≤L := by have hg := growthBase_ge_four k hk; dsimp [L]; linarith
  have hr (z : Torus) : (1+L)*codingRadius k χ ε δ z≤1/100 := by
    change (1+9*growthBase k)*codingRadius k χ ε δ z≤1/100
    simpa only [abs_of_nonneg (show 0≤9*growthBase k from hL)] using codingRadius_small k χ ε hδ z
  have hr0 (z : Torus) : codingRadius k χ ε δ z≤1/100 := by
    have hp := (codingRadius_pos k χ ε hδ z).le
    nlinarith [hr z,mul_nonneg hL hp]
  have hrL (z : Torus) : L*codingRadius k χ ε δ z≤1/100 := by
    have hp := (codingRadius_pos k χ ε hδ z).le
    linarith [hr z]
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have ihj := ih (by omega)
    let d := (standardLift k)^[j+1] (complexRep y)-(standardLift k)^[j+1] (complexRep x)
    let e := complexRep ((standardMap k)^[j+1] y)-complexRep ((standardMap k)^[j+1] x)
    have hd : ‖d‖≤L*(2*codingRadius k χ ε δ ((standardMap k)^[j] x)) := by
      dsimp only [d]
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      apply (standardLift_lipschitz_bound k hk _ _).trans
      rw [ihj]
      exact mul_le_mul_of_nonneg_left (adaptive_rep_radius k χ ε δ hδ (hword j (by omega))) hL
    have he : ‖e‖≤2*codingRadius k χ ε δ ((standardMap k)^[j+1] x) :=
      adaptive_rep_radius k χ ε δ hδ (hword (j+1) hj)
    have hclose : ‖d-e‖<1 := by
      have hh := (norm_sub_le d e).trans (add_le_add hd he)
      nlinarith [hrL ((standardMap k)^[j] x),hr0 ((standardMap k)^[j+1] x)]
    have hproj : complexProjection d=complexProjection e := by
      simp only [d,e,complexProjection_sub,complexProjection_iterate,complexProjection_complexRep]
    exact complexProjection_eq_of_close hproj hclose

lemma adaptive_codeFiber_trapped (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hδ : 0<δ)
    (x : Torus) (hx : ∀ j : ℕ,FineRegular k χ ε ((standardMap k)^[j] x)) (N : ℕ) :
    ∀ y∈LocalCoding.codeFiber (standardMap k) (adaptiveLabel (codingLevel k χ ε δ hδ)) N x,
      complexRep y∈fineLiftTrapped k χ ε δ (complexRep x) N := by
  intro y hy j hj
  have hd := adaptive_lift_difference k hk χ ε δ hδ N x y hy j hj
  change ‖fineInverse k χ ε δ (complexProjection ((standardLift k)^[j] (complexRep x)))
    ((standardLift k)^[j] (complexRep y)-(standardLift k)^[j] (complexRep x))‖≤1
  rw [complexProjection_iterate,complexProjection_complexRep,hd]
  have hb := (fineInverse k χ ε δ ((standardMap k)^[j] x)).le_opNorm (complexRep ((standardMap k)^[j] y)-complexRep ((standardMap k)^[j] x))
  have hdist := adaptive_rep_radius k χ ε δ hδ (hy j hj)
  have hh := hb.trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
  have hc := fineInverse_codingRadius k χ ε hδ ((standardMap k)^[j] x) (hx j)
  nlinarith

lemma measurableSet_codeFiber {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (f : Torus → Torus) (hf : Measurable f) (p : Torus → ι) (hp : Measurable p) (N : ℕ) (x : Torus) :
    MeasurableSet (LocalCoding.codeFiber f p N x) := by
  have he : LocalCoding.codeFiber f p N x=⋂ j : ℕ,⋂ _ : j≤N,(p ∘ f^[j]) ⁻¹' {p (f^[j] x)} := by
    ext y; simp only [LocalCoding.codeFiber,mem_ofPred_eq,mem_iInter,mem_preimage,mem_singleton_iff,Function.comp_apply]
  rw [he]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => (hp.comp (hf.iterate j)) (measurableSet_singleton _)))

theorem adaptive_codeFiber_volume (k : ℝ) (hk : 0≤k) (χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) :
    ∃ C : ℝ,0<C ∧ ∀ x : Torus,(∀ j : ℕ,FineRegular k χ ε ((standardMap k)^[j] x)) → ∀ N : ℕ,
      area (LocalCoding.codeFiber (standardMap k) (adaptiveLabel (codingLevel k χ ε δ hδ)) N x)≤
        ENNReal.ofReal (C*(Real.exp (-χ+ε)+δ)^N) := by
  obtain ⟨C,hC,hbound⟩ := exists_fineVolumeFactor_bound k χ ε hδ
  refine ⟨4*C,by positivity,?_⟩
  intro x hx N
  apply (area_le_volume_of_complexRep_subset
    (measurableSet_codeFiber _ (measurePreserving_standardMap k).measurable _
      (measurable_adaptiveLabel _ (measurable_codingLevel k χ ε δ hδ)) N x)
    (adaptive_codeFiber_trapped k hk χ ε δ hδ x hx N)).trans
  have hreg (j : ℕ) : FineRegular k χ ε (complexProjection ((standardLift k)^[j] (complexRep x))) := by
    simpa only [complexProjection_iterate,complexProjection_complexRep] using hx j
  apply (fineLiftTrapped_volume k χ ε δ hδ hq (complexRep x) hreg N).trans
  apply ENNReal.ofReal_le_ofReal
  simp only [complexProjection_complexRep]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound x) (by norm_num)) (by positivity)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

lemma exists_fine_parameters {a χ : ℝ} (ha : 0<a) (haχ : a<χ) :
    ∃ ε δ : ℝ,0<ε ∧ 0<δ ∧ Real.exp (-χ+ε)+δ<Real.exp (-a) ∧ Real.exp (-a)<1 := by
  let ε := (χ-a)/2
  have hε : 0<ε := by dsimp [ε]; linarith
  have hgap : Real.exp (-χ+ε)<Real.exp (-a) := Real.exp_lt_exp.mpr (by dsimp [ε]; linarith)
  refine ⟨ε,(Real.exp (-a)-Real.exp (-χ+ε))/2,hε,by linarith,by linarith,?_⟩
  exact Real.exp_lt_one_iff.mpr (by linarith)

lemma exists_spectral_rate_code (k : ℝ) (hk : 0≤k) (a χ : ℝ) (ha : 0<a) (haχ : a<χ) :
    ∃ (p : Torus → AdaptiveSymbol) (S : AdaptiveSymbol → Finset AdaptiveSymbol) (D : ℕ) (b : ℝ),
      Measurable p ∧ 0<D ∧ (∀ s,(S s).card≤D) ∧ 0≤b ∧
      (∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),p (standardMap k z)∈S (p z)) ∧
      (∀ N : ℕ,∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
        area (LocalCoding.codeFiber (standardMap k) p N z)≤ENNReal.ofReal (Real.exp (-((N : ℝ)*a-b)))) := by
  obtain ⟨ε,δ,hε,hδ,hq,hq1⟩ := exists_fine_parameters ha haχ
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (Real.exp (2*ε)) (show (1 : ℝ)<2 by norm_num)
  obtain ⟨M,hM⟩ := exists_nat_ge (2*(9*growthBase k)*(2 : ℝ)^J)
  obtain ⟨C,hC,hvolume⟩ := adaptive_codeFiber_volume k hk χ ε δ hδ (hq.trans hq1)
  let p := adaptiveLabel (codingLevel k χ ε δ hδ)
  let S := adaptiveSuccessors k (codingLevel k χ ε δ hδ) J M
  let b := max 0 (Real.log C)
  have hCb : C≤Real.exp b := by
    rw [←Real.exp_log hC]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  refine ⟨p,S,(2*J+1)*(2*M+3)^2,b,measurable_adaptiveLabel _ (measurable_codingLevel k χ ε δ hδ),
    by positivity,adaptiveSuccessors_card k _ J M,le_max_left _ _,?_,?_⟩
  · filter_upwards [ae_fineRegular k hk (ha.trans haχ) hε] with z hz
    have hj := codingLevel_step k χ ε δ hδ z hz J hJ.le
    exact adaptive_successor_mem k hk _ J M hM z hj.1 hj.2
  · intro N
    filter_upwards [ae_fineRegular_all_iterates k hk (ha.trans haχ) hε] with z hz
    apply (hvolume z (fun n => (hz n).1) N).trans
    apply ENNReal.ofReal_le_ofReal
    have hpow : (Real.exp (-χ+ε)+δ)^N≤(Real.exp (-a))^N :=
      pow_le_pow_left₀ (by positivity) hq.le _
    calc
      C*(Real.exp (-χ+ε)+δ)^N ≤ Real.exp b*(Real.exp (-a))^N :=
        mul_le_mul hCb hpow (by positivity) (Real.exp_pos _).le
      _ = Real.exp (-((N : ℝ)*a-b)) := by
        rw [←Real.exp_nat_mul,←Real.exp_add]
        congr 1
        ring
end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
lemma obs_lower_information (p : Ω → α) (hp : Measurable p) (I : α → ℝ)
    (hsmall : ∀ a : α,mass μ p a≤Real.exp (-I a)) :
    (∫ x,I (p x) ∂μ)≤obs μ p := by
  rw [←sum_mass_mul_integral μ p hp I]
  apply Finset.sum_le_sum
  intro a _
  by_cases hz : mass μ p a=0
  · simp only [hz,zero_mul,Real.negMulLog_zero,le_refl]
  · have hpos : 0 < mass μ p a := lt_of_le_of_ne (mass_nonneg μ p a) (Ne.symm hz)
    have hh := Real.log_le_log hpos (hsmall a)
    rw [Real.log_exp] at hh
    unfold Real.negMulLog
    nlinarith [mass_nonneg μ p a]
end StandardMapEntropy.Entropy

namespace StandardMapEntropy.LocalCoding
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [MeasurableSpace Ω] in
lemma masked_history_atom_subset (f : Ω → Ω) (p : Ω → ι) (S : ι → Finset ι)
    (A : Finset ι) (N : ℕ) (x : Ω) (hA : p x∈A)
    (hpath : ∀ j : ℕ,p (f^[j+1] x)∈S (p (f^[j] x))) :
    (Entropy.history (maskedState A (reach S A N) f p) (N+1)) ⁻¹'
      {Entropy.history (maskedState A (reach S A N) f p) (N+1) x}⊆codeFiber f p N x := by
  intro y hy i hi
  have hr : p (f^[i] x)∈reach S A N := reach_mono S A hi
    (path_mem_reach S A (fun j => p (f^[j] x)) hA hpath i)
  have he : maskedState A (reach S A N) f p i y=truncate (reach S A N) (p (f^[i] x)) := by
    exact (congrFun hy ⟨i,by omega⟩).trans (maskedState_of_mem A _ f p i hA)
  rw [truncate_some _ _ hr] at he
  by_cases hyA : p y∈A
  · rw [maskedState_of_mem A _ f p i hyA] at he
    exact (truncate_eq_some_iff _ _ _).mp he
  · rw [maskedState_of_not_mem A _ f p i hyA] at he
    cases he

def initialInformation (w : ι → ℝ) (N : ℕ) (b : ℝ) (R : Finset ι)
    (v : Fin (N+1) → Option R) : ℝ :=
  (v ⟨0,by omega⟩).elim 0 (fun a => (N : ℝ)*w a.val-b)
omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [MeasurableSpace Ω] in
lemma initialInformation_history (w : ι → ℝ) (f : Ω → Ω) (p : Ω → ι)
    (A : Finset ι) (S : ι → Finset ι) (N : ℕ) (b : ℝ) (x : Ω) :
    initialInformation w N b (reach S A N) (Entropy.history (maskedState A (reach S A N) f p) (N+1) x)=
      if p x∈A then (N : ℝ)*w (p x)-b else 0 := by
  by_cases hx : p x∈A
  · simp only [initialInformation,Entropy.history,maskedState_of_mem A _ f p 0 hx,Function.iterate_zero,
      Function.id_def,truncate_some _ _ (base_subset_reach S A N hx),Option.elim_some,hx,↓reduceIte]
  · simp only [initialInformation,Entropy.history,maskedState_of_not_mem A _ f p 0 hx,Option.elim_none,hx,↓reduceIte]

lemma masked_history_weighted_small (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → ι) (hp : Measurable p) (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x))
    (A : Finset ι) (N : ℕ) (w : ι → ℝ) (b : ℝ)
    (hsmall : ∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-((N : ℝ)*w (p x)-b))))
    (v : Fin (N+1) → Option (reach S A N)) :
    Entropy.mass μ (Entropy.history (maskedState A (reach S A N) f p) (N+1)) v≤
      Real.exp (-initialInformation w N b (reach S A N) v) := by
  let q := Entropy.history (maskedState A (reach S A N) f p) (N+1)
  by_cases hz : μ (q ⁻¹' {v})=0
  · change (μ (q ⁻¹' {v})).toReal≤_
    rw [hz,ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · obtain ⟨x,hx,hpath,hsm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hz
      (((ae_transition_orbit μ f hf p S hS).and hsmall).filter_mono Measure.absolutelyContinuous_restrict.ae_le)
    change q x=v at hx
    rw [←hx,initialInformation_history]
    by_cases hA : p x∈A
    · rw [ite_eq_left hA]
      have hsub : q ⁻¹' {v}⊆codeFiber f p N x := by
        rw [←hx]; exact masked_history_atom_subset f p S A N x hA hpath
      have hle := (measure_mono hsub).trans hsm
      rw [←hx] at hle
      exact (ENNReal.toReal_mono (by simp) hle).trans_eq (ENNReal.toReal_ofReal (Real.exp_pos _).le)
    · rw [ite_eq_right hA,neg_zero,Real.exp_zero]
      exact Entropy.mass_le_one μ _ (Entropy.history_measurable _
        (measurable_maskedState A _ f p hf.measurable hp) _) _

lemma masked_history_weighted_lower (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → ι) (hp : Measurable p) (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x))
    (A : Finset ι) (N : ℕ) (w : ι → ℝ) (hw : Integrable (w ∘ p) μ) (b : ℝ) (hb : 0≤b)
    (hsmall : ∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-((N : ℝ)*w (p x)-b)))) :
    (N : ℝ)*(∫ x in {x | p x∈A},w (p x) ∂μ)-b≤
      Entropy.obs μ (Entropy.history (maskedState A (reach S A N) f p) (N+1)) := by
  have hs : MeasurableSet {x : Ω | p x∈A} := hp A.measurableSet
  have hh := Entropy.obs_lower_information μ _ (Entropy.history_measurable _
    (measurable_maskedState A _ f p hf.measurable hp) _) (initialInformation w N b (reach S A N))
    (masked_history_weighted_small μ f hf p hp S hS A N w b hsmall)
  simp only [initialInformation_history] at hh
  have he : (fun x : Ω => if p x∈A then (N : ℝ)*w (p x)-b else 0)=
      {x : Ω | p x∈A}.indicator (fun x => (N : ℝ)*w (p x)-b) := by
    funext x
    simp only [indicator_apply,mem_ofPred_eq]
  have hwi : Integrable (fun x => (N : ℝ)*w (p x)) μ := hw.const_mul _
  rw [he,integral_indicator hs,integral_sub hwi.integrableOn (integrable_const _),
    integral_const_mul,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hh
  have hm : (μ {x : Ω | p x∈A}).toReal≤1 := by
    exact (ENNReal.toReal_mono ENNReal.one_ne_top (by simpa only [measure_univ] using (measure_mono (μ:=μ) (subset_univ {x : Ω | p x∈A})))).trans_eq (by simp)
  simpa only [one_mul] using (sub_le_sub_left (mul_le_mul_of_nonneg_right hm hb) _).trans hh

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
lemma tendsto_integral_code_truncation (p : Ω → ι) (hp : Measurable p) (w : ι → ℝ)
    (hw : Integrable (w ∘ p) μ) :
    Tendsto (fun A : Finset ι => ∫ x in {x | p x∈A},w (p x) ∂μ) atTop (𝓝 (∫ x,w (p x) ∂μ)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun x => ‖w (p x)‖)
    (F:=fun A : Finset ι => {x | p x∈A}.indicator (fun x => w (p x)))
    (Filter.Eventually.of_forall (fun A => (hw.indicator (hp A.measurableSet)).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun A => ae_of_all _ (fun x => norm_indicator_le_norm_self _ x))) hw.norm
    (ae_of_all _ (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ({p x} : Finset ι)] with A hA
      exact (indicator_of_mem (hA (Finset.mem_singleton_self _)) _).symm))
  have he (A : Finset ι) : (∫ x, {x | p x∈A}.indicator (fun x => w (p x)) x ∂μ)=
      ∫ x in {x | p x∈A},w (p x) ∂μ := integral_indicator (hp A.measurableSet)
  simp_rw [he] at ht
  exact ht

lemma weighted_lower_rate_truncation (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → ι) (hp : Measurable p)
    (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) {D : ℕ} (hD : 0<D)
    (hcard : ∀ x,(S x).card≤D) (w : ι → ℝ) (hw : Integrable (w ∘ p) μ) (b : ℝ) (hb : 0≤b)
    (hsmall : ∀ N : ℕ,∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-((N : ℝ)*w (p x)-b))))
    (A K : Finset ι) :
    (∫ x in {x | p x∈A},w (p x) ∂μ)≤Entropy.rate μ f (truncate K ∘ p)+(μ {x | p x∉K}).toReal*Real.log (D : ℝ) := by
  let t := (μ {x | p x∉K}).toReal*Real.log (D : ℝ)
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hdiv (c : ℝ) : Tendsto (fun n : ℕ => c/((n : ℝ)+1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have hratio : Tendsto (fun n : ℕ => (n : ℝ)/((n : ℝ)+1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x:=(1 : ℝ))).sub (hdiv 1)
    convert h using 1
    · funext n; field_simp; ring
    · ring_nf
  have hl := (hratio.mul_const (∫ x in {x | p x∈A},w (p x) ∂μ)).sub (hdiv b)
  have hr := (((Entropy.rate_tendsto μ f hf (truncate K ∘ p) ((measurable_truncate K).comp hp)).comp
    (tendsto_add_atTop_nat 1)).add (hdiv (Real.log ((A.card : ℝ)+1)))).add (hratio.mul_const t)
  simp only [one_mul,sub_zero] at hl
  simp only [add_zero,one_mul] at hr
  apply le_of_tendsto_of_tendsto hl hr
  apply Filter.Eventually.of_forall
  intro n
  have hh := (masked_history_weighted_lower μ f hf p hp S hS A n w hw b hb (hsmall n)).trans
    (masked_history_entropy_upper μ f hf p hp S hS hD hcard A K n)
  have hd : (0 : ℝ)<(n : ℝ)+1 := by positivity
  have hh' := div_le_div_of_nonneg_right hh hd.le
  convert hh' using 1 <;> simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one,t] <;> field_simp

theorem weighted_lower_of_finite_rate_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → ι) (hp : Measurable p) (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x))
    {D : ℕ} (hD : 0<D) (hcard : ∀ x,(S x).card≤D)
    (w : ι → ℝ) (hw : Integrable (w ∘ p) μ) (b c : ℝ) (hb : 0≤b)
    (hsmall : ∀ N : ℕ,∀ᵐ x ∂μ,μ (codeFiber f p N x)≤ENNReal.ofReal (Real.exp (-((N : ℝ)*w (p x)-b))))
    (hc : ∀ K : Finset ι,Entropy.rate μ f (truncate K ∘ p)≤c) : (∫ x,w (p x) ∂μ)≤c := by
  have hK (K : Finset ι) : (∫ x,w (p x) ∂μ)≤c+(μ {x | p x∉K}).toReal*Real.log (D : ℝ) := by
    exact le_of_tendsto' (tendsto_integral_code_truncation μ p hp w hw) (fun A : Finset ι =>
      (weighted_lower_rate_truncation μ f hf p hp S hS hD hcard w hw b hb hsmall A K).trans (add_le_add (hc K) le_rfl))
  have hh := ge_of_tendsto' (((tendsto_code_tail μ p hp).mul_const (Real.log (D : ℝ))).const_add c) hK
  simpa only [zero_mul,add_zero] using hh
end StandardMapEntropy.LocalCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma rate_equiv (f : Ω → Ω) (p : Ω → α) (e : α ≃ β) : rate μ f (e ∘ p)=rate μ f p := by
  have he (n : ℕ) : obs μ (word f (e ∘ p) n)=obs μ (word f p n) := by
    have hword : word f (e ∘ p) n=(Equiv.piCongrRight (fun _ : Fin n => e)) ∘ word f p n := rfl
    rw [hword,obs_equiv]
  simp only [rate,he]
end StandardMapEntropy.Entropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma finite_rate_le_metricEntropy {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Torus) [IsProbabilityMeasure μ] (f : Torus → Torus) (hf : MeasurePreserving f μ μ)
    (p : Torus → α) (hp : Measurable p) : ENNReal.ofReal (Entropy.rate μ f p)≤ metricEntropy μ f := by
  let : Nonempty α := ⟨p (0,0)⟩
  have hcard : Fintype.card α-1+1=Fintype.card α := Nat.sub_add_cancel (Fintype.card_pos)
  let e : α ≃ Fin (Fintype.card α-1+1) := (Fintype.equivFin α).trans (finCongr hcard.symm)
  let q : FinitePartition (Fintype.card α-1) := ⟨e ∘ p,(measurable_of_countable e).comp hp⟩
  have hle : partitionEntropy μ f q≤ metricEntropy μ f := le_iSup_of_le _ (le_iSup_of_le q le_rfl)
  rw [partitionEntropy_eq_ofReal_rate μ f hf q] at hle
  exact (congrArg ENNReal.ofReal (Entropy.rate_equiv μ f p e)).symm.le.trans hle
end StandardMapEntropy

end
end

end OAI
