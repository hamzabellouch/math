import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.LocallyFiniteLower

namespace OAI

section
section
namespace StandardMapEntropy.LocalCoding
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {ι β : Type*} [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
variable [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
variable {Ω : Type*} [MeasurableSpace Ω]
noncomputable def taggedCode (u : Ω → β) (p : β → Ω → ι) (x : Ω) : β×ι := (u x,p (u x) x)
omit [DecidableEq ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma measurable_taggedCode (u : Ω → β) (hu : Measurable u) (p : β → Ω → ι)
    (hp : ∀ j,Measurable (p j)) : Measurable (taggedCode u p) := by
  have hm : Measurable (fun w : β×Ω => p w.1 w.2) :=
    measurable_from_prod_countable_right (f:=fun w : β×Ω => p w.1 w.2) hp
  exact hu.prodMk (hm.comp (hu.prodMk measurable_id))
omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace Ω] in
lemma invariant_iterate (f : Ω → Ω) (u : Ω → β) (hu : ∀ x,u (f x)=u x) (n : ℕ) (x : Ω) :
    u (f^[n] x)=u x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',hu,ih]
noncomputable def taggedSuccessors (S : β → ι → Finset ι) (a : β×ι) : Finset (β×ι) := by
  classical
  exact (S a.1 a.2).image (fun b => (a.1,b))
omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma taggedSuccessors_card (S : β → ι → Finset ι) {D : ℕ} (hD : ∀ j a,(S j a).card≤D) (a : β×ι) :
    (taggedSuccessors S a).card≤D := by
  classical
  exact Finset.card_image_le.trans (hD a.1 a.2)
omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace Ω] in
lemma tagged_transition (f : Ω → Ω) (u : Ω → β) (hu : ∀ x,u (f x)=u x)
    (p : β → Ω → ι) (S : β → ι → Finset ι) (x : Ω)
    (hx : p (u x) (f x)∈S (u x) (p (u x) x)) :
    taggedCode u p (f x)∈taggedSuccessors S (taggedCode u p x) := by
  classical
  simp only [taggedCode,hu,taggedSuccessors]
  exact Finset.mem_image.mpr ⟨p (u x) (f x),hx,rfl⟩
omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace Ω] in
lemma tagged_codeFiber_subset (f : Ω → Ω) (u : Ω → β) (hu : ∀ x,u (f x)=u x)
    (p : β → Ω → ι) (N : ℕ) (x : Ω) :
    codeFiber f (taggedCode u p) N x⊆codeFiber f (p (u x)) N x := by
  intro y hy i hi
  have hj := congrArg Prod.fst (hy i hi)
  have hh := congrArg Prod.snd (hy i hi)
  simp only [taggedCode,invariant_iterate f u hu] at hh hj
  rwa [hj] at hh

lemma integrable_finite_observable (μ : Measure Ω) [IsFiniteMeasure μ] (u : Ω → β)
    (hu : Measurable u) (a : β → ℝ) : Integrable (a ∘ u) μ := by
  apply Integrable.of_bound (((measurable_of_countable a).comp hu).aestronglyMeasurable) (∑ j : β,‖a j‖)
  exact ae_of_all _ (fun x => Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_univ (u x)))
end StandardMapEntropy.LocalCoding

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

theorem entropy_lower_finite_bin_coding {ι β : Type*} [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Torus) [IsProbabilityMeasure μ] (f : Torus → Torus) (hf : MeasurePreserving f μ μ)
    (u : Torus → β) (hu : Measurable u) (hinv : ∀ x,u (f x)=u x)
    (p : β → Torus → ι) (hp : ∀ j,Measurable (p j)) (S : β → ι → Finset ι)
    (hS : ∀ᵐ x ∂μ,p (u x) (f x)∈S (u x) (p (u x) x))
    {D : ℕ} (hD : 0<D) (hcard : ∀ j a,(S j a).card≤D) (a : β → ℝ) (b : ℝ) (hb : 0≤b)
    (hsmall : ∀ N : ℕ,∀ᵐ x ∂μ,μ (LocalCoding.codeFiber f (p (u x)) N x)≤
      ENNReal.ofReal (Real.exp (-((N : ℝ)*a (u x)-b)))) :
    ENNReal.ofReal (∫ x,a (u x) ∂μ)≤ metricEntropy μ f := by
  classical
  by_cases htop : metricEntropy μ f=∞
  · rw [htop]; exact le_top
  let q := LocalCoding.taggedCode u p
  have hq := LocalCoding.measurable_taggedCode u hu p hp
  let w : β×ι → ℝ := fun v => a v.1
  have hw : Integrable (w ∘ q) μ := LocalCoding.integrable_finite_observable μ u hu a
  have hs : ∀ᵐ x ∂μ,q (f x)∈LocalCoding.taggedSuccessors S (q x) := by
    filter_upwards [hS] with x hx
    exact LocalCoding.tagged_transition f u hinv p S x hx
  have hm (N : ℕ) : ∀ᵐ x ∂μ,μ (LocalCoding.codeFiber f q N x)≤
      ENNReal.ofReal (Real.exp (-((N : ℝ)*w (q x)-b))) := by
    filter_upwards [hsmall N] with x hx
    exact (measure_mono (LocalCoding.tagged_codeFiber_subset f u hinv p N x)).trans hx
  have hc (K : Finset (β×ι)) : Entropy.rate μ f (LocalCoding.truncate K ∘ q)≤(metricEntropy μ f).toReal := by
    have hh := finite_rate_le_metricEntropy μ f hf (LocalCoding.truncate K ∘ q)
      ((LocalCoding.measurable_truncate K).comp hq)
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hh
  have hh := LocalCoding.weighted_lower_of_finite_rate_bound μ f hf q hq (LocalCoding.taggedSuccessors S)
    hs hD (LocalCoding.taggedSuccessors_card S hcard) w hw b (metricEntropy μ f).toReal hb hm hc
  exact (ENNReal.ofReal_le_iff_le_toReal htop).mpr hh
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

theorem entropy_lower_finite_spectral_bins {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (k : ℝ) (hk : 0≤k) (u : Torus → β) (hu : Measurable u)
    (hinv : ∀ x,u (standardMap k x)=u x) (a χ : β → ℝ) (ha : ∀ j,0≤a j)
    (hgap : ∀ j,0<a j → a j<χ j)
    (hL : ∀ x,0<a (u x) → χ (u x)<standardLyapunov k hk x) :
    ENNReal.ofReal (∫ x,a (u x) ∂area)≤ metricEntropy area (standardMap k) := by
  classical
  have hcode (j : β) :
      ∃ (p : Torus → AdaptiveSymbol) (S : AdaptiveSymbol → Finset AdaptiveSymbol) (D : ℕ) (b : ℝ),
        Measurable p ∧ 0<D ∧ (∀ s,(S s).card≤D) ∧ 0≤b ∧
        (∀ᵐ z ∂area,u z=j → p (standardMap k z)∈S (p z)) ∧
        (∀ N : ℕ,∀ᵐ z ∂area,u z=j → area (LocalCoding.codeFiber (standardMap k) p N z)≤
          ENNReal.ofReal (Real.exp (-((N : ℝ)*a j-b)))) := by
    by_cases hj : 0<a j
    · obtain ⟨p,S,D,b,hp,hD,hcard,hb,hS,hsmall⟩ := exists_spectral_rate_code k hk (a j) (χ j) hj (hgap j hj)
      refine ⟨p,S,D,b,hp,hD,hcard,hb,?_,?_⟩
      · have hh := (ae_restrict_iff' (measurableSet_spectralGapRegion k hk (χ j))).mp hS
        filter_upwards [hh] with z hz he
        apply hz
        have ht := hL z (by simpa only [he] using hj)
        simpa only [spectralGapRegion,he,mem_ofPred_eq] using ht
      · intro N
        have hh := (ae_restrict_iff' (measurableSet_spectralGapRegion k hk (χ j))).mp (hsmall N)
        filter_upwards [hh] with z hz he
        apply hz
        have ht := hL z (by simpa only [he] using hj)
        simpa only [spectralGapRegion,he,mem_ofPred_eq] using ht
    · have haz : a j=0 := le_antisymm (le_of_not_gt hj) (ha j)
      refine ⟨fun _ => (0,0),fun _ => {(0,0)},1,0,measurable_const,by omega,?_,le_rfl,?_,?_⟩
      · intro s; simp
      · exact ae_of_all _ (fun z _ => Finset.mem_singleton_self _)
      · intro N
        apply ae_of_all
        intro z _
        rw [haz,mul_zero,sub_zero,neg_zero,Real.exp_zero,ENNReal.ofReal_one]
        simpa only [measure_univ] using measure_mono (μ:=area) (subset_univ (LocalCoding.codeFiber (standardMap k) (fun _ => ((0,0) : AdaptiveSymbol)) N z))
  choose p S D b hp hD hcard hb hS hsmall using hcode
  let B := ∑ j : β,b j
  let R := 1+∑ j : β,D j
  have hbB (j : β) : b j≤B := Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ j)
  have hDB (j : β) : D j≤R := (Finset.single_le_sum (fun j _ => Nat.zero_le (D j)) (Finset.mem_univ j)).trans (Nat.le_add_left _ _)
  refine entropy_lower_finite_bin_coding area (standardMap k) (measurePreserving_standardMap k)
    u hu hinv p hp S ?_ (show 0<R by dsimp [R]; omega) (fun j s => (hcard j s).trans (hDB j)) a B
    (Finset.sum_nonneg (fun j _ => hb j)) ?_
  · have hall := (ae_all_iff.mpr hS)
    filter_upwards [hall] with z hz
    exact hz (u z) rfl
  · intro N
    have hall := (ae_all_iff.mpr (fun j => hsmall j N))
    filter_upwards [hall] with z hz
    apply (hz (u z) rfl).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith [hbB (u z)]
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma exists_lower_spectral_bins (L : Torus → ℝ) (hL : Measurable L) (hL0 : ∀ z,0≤L z)
    (B : ℝ) (hB : ∀ z,L z≤B) (τ : ℝ) (hτ : 0<τ) :
    ∃ (m : ℕ) (u : Torus → Fin m) (a χ : Fin m → ℝ),
      Measurable u ∧ (∀ f : Torus → Torus,(∀ z,L (f z)=L z) → ∀ z,u (f z)=u z) ∧
      (∀ j,0≤a j) ∧ (∀ j,0<a j → a j<χ j) ∧
      (∀ z,0<a (u z) → χ (u z)<L z) ∧ (∀ z,a (u z)≤L z ∧ L z≤a (u z)+3*τ) := by
  let m := Nat.floor (B/τ)+1
  let u : Torus → Fin m := fun z => ⟨Nat.floor (L z/τ),Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (hB z) hτ.le))⟩
  let a : Fin m → ℝ := fun j => max 0 (((j.val : ℝ)-2)*τ)
  let χ : Fin m → ℝ := fun j => ((j.val : ℝ)-1)*τ
  have hfloor (z : Torus) : (u z).val=Nat.floor (L z/τ) := rfl
  have hlow (z : Torus) : ((u z).val : ℝ)*τ≤L z :=
    (le_div_iff₀ hτ).mp (Nat.floor_le (div_nonneg (hL0 z) hτ.le))
  have hupp (z : Torus) : L z<(((u z).val : ℝ)+1)*τ :=
    (div_lt_iff₀ hτ).mp (Nat.lt_floor_add_one (L z/τ))
  refine ⟨m,u,a,χ,?_,?_,?_,?_,?_,?_⟩
  · apply measurable_to_countable'
    intro j
    have he : u ⁻¹' {j}=(fun z => Nat.floor (L z/τ)) ⁻¹' {j.val} := by
      ext z
      simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,u]
    rw [he]
    exact (hL.div_const τ).nat_floor (measurableSet_singleton _)
  · intro f hf z
    apply Fin.ext
    simp only [u,hf]
  · intro j; exact le_max_left _ _
  · intro j hj
    have hpos : 0<((j.val : ℝ)-2)*τ := by
      exact (lt_max_iff.mp hj).resolve_left (lt_irrefl 0)
    change max 0 (((j.val : ℝ)-2)*τ)<((j.val : ℝ)-1)*τ
    rw [max_eq_right hpos.le]
    nlinarith
  · intro z _
    change (((u z).val : ℝ)-1)*τ<L z
    nlinarith [hlow z]
  · intro z
    constructor
    · apply max_le (hL0 z)
      nlinarith [hlow z]
    · have hh : (((u z).val : ℝ)-2)*τ≤a (u z) := le_max_right _ _
      linarith [hupp z]
end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def wordPack (n m : ℕ) : (Fin (n*m) → α) ≃ (Fin n → Fin m→α) :=
  ((Equiv.piCongrLeft (fun _ : Fin (n*m) => α) finProdFinEquiv).symm).trans
    (Equiv.curry (Fin n) (Fin m) α)
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma wordPack_apply (f : Ω → Ω) (p : Ω → α) (n m : ℕ) (x : Ω) :
    wordPack n m (word f p (n*m) x)=word (f^[m]) (word f p m) n x := by
  funext i j
  simp only [wordPack,Equiv.trans_apply,Equiv.curry_apply,word]
  change p (f^[j.val+m*i.val] x)=p (f^[j.val] ((f^[m])^[i.val] x))
  rw [Function.iterate_add_apply,Function.iterate_mul]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_pack (f : Ω → Ω) (p : Ω → α) (n m : ℕ) :
    obs μ (word (f^[m]) (word f p m) n)=obs μ (word f p (n*m)) := by
  have h := obs_equiv μ (word f p (n*m)) (wordPack n m)
  simpa only [Function.comp_def,wordPack_apply] using h
lemma rate_power_word (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (m : ℕ) (hm : 0 < m) :
    rate μ (f^[m]) (word f p m)=(m : ℝ)*rate μ f p := by
  have ht : Tendsto (fun n : ℕ => n*m) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hm) tendsto_id
  have h := ((rate_tendsto μ f hf p hp).comp ht).const_mul (m : ℝ)
  have h' : Tendsto (fun n : ℕ => obs μ (word (f^[m]) (word f p m) n)/(n : ℝ))
      atTop (𝓝 ((m : ℝ)*rate μ f p)) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [obs_word_pack]
    dsimp only [Function.comp_def]
    have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    have hm0 : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
  exact tendsto_nhds_unique (rate_tendsto μ (f^[m]) (hf.iterate m) (word f p m)
    (word_measurable f hf.measurable p hp m)) h'

omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma word_eval_zero (f : Ω → Ω) (p : Ω → α) (n : ℕ) :
    (fun v : Fin (n+1)→α => v 0) ∘ word f p (n+1)=p := by
  funext x
  simp only [Function.comp_def,word,Fin.val_zero,Function.iterate_zero,Function.id_def]
lemma obs_word_markov_step (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (n : ℕ) :
    obs μ (word f p (n+2))≤obs μ (word f p (n+1))+cond μ p (p ∘ f) := by
  have hs := obs_word_split μ f p 1 (n+1)
  have hp1 : word f p 1=(fun x (_ : Fin 1) => p x) := by
    funext x i
    simp only [word,Fin.val_eq_zero,Function.iterate_zero,Function.id_def]
  have hc := cond_factor_right μ p ((word f p (n+1)) ∘ f) (fun v : Fin (n+1)→α => v 0)
    hp ((word_measurable f hf.measurable p hp (n+1)).comp hf.measurable)
  have he : (fun v : Fin (n+1)→α => v 0) ∘ ((word f p (n+1)) ∘ f)=p ∘ f :=
    congrArg (fun g => g ∘ f) (word_eval_zero f p n)
  rw [he] at hc
  have hpair : obs μ (fun x => (word f p 1 x,word f p (n+1) (f x)))=
      obs μ (fun x => (p x,word f p (n+1) (f x))) := by
    have hh := obs_equiv μ (fun x => (word f p 1 x,word f p (n+1) (f x)))
      (Equiv.prodCongr (Equiv.funUnique (Fin 1) α) (Equiv.refl (Fin (n+1)→α)))
    simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
      Equiv.funUnique_apply,word,Fin.default_eq_zero,Fin.val_zero,Function.iterate_zero,Function.id_def] using hh.symm
  have hobs := obs_comp_preserving μ f hf (word f p (n+1)) (word_measurable f hf.measurable p hp (n+1))
  have hn : 1+(n+1)=n+2 := by omega
  rw [hn] at hs
  simp only [Function.iterate_one] at hs
  rw [hs,hpair]
  unfold cond at hc
  change _≤_+((obs μ (fun x => (p x,(p ∘ f) x)))-obs μ (p ∘ f))
  dsimp only [Function.comp_def] at hc hobs ⊢
  linarith
lemma obs_word_markov_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (n : ℕ) :
    obs μ (word f p (n+1))≤obs μ p+(n : ℝ)*cond μ p (p ∘ f) := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,add_zero,obs_word_one μ f p hp,le_refl]
  | succ n ih =>
    have h := obs_word_markov_step μ f hf p hp n
    have he : (n+1 : ℕ)+1=n+2 := by omega
    rw [he]
    push_cast
    linarith
lemma rate_le_oneStep (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) : rate μ f p≤cond μ p (p ∘ f) := by
  have hseq := (rate_tendsto μ f hf p hp).comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun n : ℕ => (obs μ p-cond μ p (p ∘ f))/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_mono (fun n : ℕ => le_add_of_nonneg_right (show (0 : ℝ)≤1 by norm_num)) tendsto_natCast_atTop_atTop)
  have hlim := h0.const_add (cond μ p (p ∘ f))
  apply le_of_tendsto_of_tendsto hseq (show Tendsto
    (fun n : ℕ => cond μ p (p ∘ f)+(obs μ p-cond μ p (p ∘ f))/((n : ℝ)+1))
    atTop (𝓝 (cond μ p (p ∘ f))) from by simpa only [add_zero] using hlim)
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  rw [Nat.cast_add,Nat.cast_one]
  have h := div_le_div_of_nonneg_right (obs_word_markov_bound μ f hf p hp n)
    (show 0≤(n : ℝ)+1 by positivity)
  dsimp only [Function.comp_def] at h ⊢
  convert h using 1
  field_simp
  ring

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

lemma grid_rate_derivative_upper (k : ℝ) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hLip : ∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
       standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖)
    (Q : ℕ) (hQ : 0<Q) (hQC : 4*C≤(Q : ℝ)) :
    Entropy.rate area ((standardMap k)^[n]) (gridLabel Q hQ)≤
      Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)+2*C/(Q : ℝ) := by
  classical
  let p := gridLabel Q hQ
  let f := (standardMap k)^[n]
  have hp : Measurable p := measurable_gridLabel Q hQ
  have hf : MeasurePreserving f area area := (measurePreserving_standardMap k).iterate n
  let anchor : Fin (Q*Q+1) → Torus := fun b => if h : ∃ z,p z=b then h.choose else (0,0)
  have hanchor (z : Torus) : p (anchor (p z))=p z := by
    simp only [anchor,dite_eq_left (show ∃ w,p w=p z from ⟨z,rfl⟩)]
    exact (show ∃ w,p w=p z from ⟨z,rfl⟩).choose_spec
  choose S hsize hcover using (fun b => standard_iterate_grid_cover k n hC hLip Q hQ hQC (anchor b))
  have hcardpos (b : Fin (Q*Q+1)) : 0<(S b).card :=
    Finset.card_pos.mpr ⟨p (f (anchor b)),hcover b (anchor b) rfl⟩
  have hlogcard (b : Fin (Q*Q+1)) :
      Real.log ((S b).card : ℝ)≤Real.log 1000+Real.log ‖standardDerivativeProduct k (anchor b) n‖ := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr (hcardpos b)) (hsize b)
    rwa [Real.log_mul (by norm_num : (1000 : ℝ)≠0)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k (anchor b) n)))] at hh
  have htransition : Entropy.cond area p (p ∘ f)=Entropy.cond area (p ∘ f) p := by
    unfold Entropy.cond
    rw [Entropy.obs_pair_swap area p (p ∘ f),Entropy.obs_comp_preserving area f hf p hp]
  have hu := Entropy.cond_support_bound area (p ∘ f) p (hp.comp hf.measurable) hp S
    (fun z => hcover (p z) z (hanchor z).symm)
  rw [Entropy.sum_mass_mul_integral area p hp (fun b => Real.log ((S b).card : ℝ))] at hu
  have hi : Integrable (fun z => Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖+2*C/(Q : ℝ)) area :=
    ((integrable_const _).add (integrable_log_standardDerivativeProduct k n)).add (integrable_const _)
  have hpoint (z : Torus) : Real.log ((S (p z)).card : ℝ)≤
      Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖+2*C/(Q : ℝ) := by
    have hh := standard_iterate_grid_log_variation k n hC hLip Q hQ (hanchor z).symm
    exact (hlogcard (p z)).trans (by linarith)
  have hint := integral_mono_of_nonneg (μ:=area) (f:=fun z => Real.log ((S (p z)).card : ℝ))
    (ae_of_all _ (fun z => Real.log_nonneg (by exact_mod_cast (hcardpos (p z))))) hi (ae_of_all _ hpoint)
  have he : (∫ z,Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖+2*C/(Q : ℝ) ∂area)=
      Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)+2*C/(Q : ℝ) := by
    rw [integral_add (f:=fun z : Torus => Real.log 1000+Real.log ‖standardDerivativeProduct k z n‖)
      (g:=fun _ : Torus => 2*C/(Q : ℝ)) ((integrable_const _).add (integrable_log_standardDerivativeProduct k n)) (integrable_const _),
      integral_add (f:=fun _ : Torus => Real.log (1000 : ℝ)) (g:=fun z => Real.log ‖standardDerivativeProduct k z n‖)
        (integrable_const _) (integrable_log_standardDerivativeProduct k n)]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [he] at hint
  exact (Entropy.rate_le_oneStep area f hf p hp).trans (htransition ▸ hu.trans hint)

lemma eventually_grid_rate_derivative_upper (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ ε : ℝ,0<ε → ∃ Q₀ : ℕ,∀ Q : ℕ,Q₀≤Q → ∀ hQ : 0<Q,
      Entropy.rate area ((standardMap k)^[n]) (gridLabel Q hQ)≤
        Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)+ε := by
  obtain ⟨B,C,hB,hC,hbound,hLip⟩ := standardLift_iterate_control k hk n
  intro ε hε
  obtain ⟨Q₀,hQ₀⟩ := exists_nat_gt (max (4*C) (2*C/ε))
  refine ⟨Q₀,?_⟩
  intro Q hQQ hQ
  have hQQ' : (Q₀ : ℝ)≤Q := by exact_mod_cast hQQ
  have hQC : 4*C≤(Q : ℝ) := (le_max_left _ _).trans (hQ₀.le.trans hQQ')
  have hQε : 2*C/ε≤(Q : ℝ) := (le_max_right _ _).trans (hQ₀.le.trans hQQ')
  have herr : 2*C/(Q : ℝ)≤ε := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hQ)).mpr
    have hh := (div_le_iff₀ hε).mp hQε
    simpa only [mul_comm] using hh
  exact (grid_rate_derivative_upper k n hC hLip Q hQ hQC).trans (add_le_add le_rfl herr)

lemma metricEntropy_iterate_derivative_upper (k : ℝ) (hk : 0≤k) (n : ℕ) :
    metricEntropy area ((standardMap k)^[n])≤
      ENNReal.ofReal (Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)) :=
  metricEntropy_le_of_grid_rates _ ((measurePreserving_standardMap k).iterate n) _
    (eventually_grid_rate_derivative_upper k hk n)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

lemma finite_rate_le_of_grid_rates {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : Torus → Torus) (hf : MeasurePreserving f area area) (b : ℝ)
    (hb : ∀ ε : ℝ,0<ε → ∃ Q₀ : ℕ,∀ Q : ℕ,Q₀≤Q → ∀ hQ : 0<Q,
      Entropy.rate area f (gridLabel Q hQ)≤b+ε) (p : Torus → α) (hp : Measurable p) :
    Entropy.rate area f p≤b := by
  let : Nonempty α := ⟨p (0,0)⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,hsmall⟩ := Entropy.cond_small_of_diameter area p hp (ε/2) (by positivity)
  obtain ⟨Q₀,hupper⟩ := hb (ε/2) (by positivity)
  obtain ⟨Q,hQbig⟩ := exists_nat_gt (max (Q₀ : ℝ) (max 1 δ⁻¹))
  have hQpos : (0 : ℝ)<Q := lt_trans zero_lt_one ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hQbig))
  have hQ : 0<Q := by exact_mod_cast hQpos
  have hQQ : Q₀≤Q := by exact_mod_cast ((le_max_left _ _).trans hQbig.le)
  have hm : 1/(Q : ℝ)<δ := (div_lt_iff₀ hQpos).mpr (by
    have hDQ : δ⁻¹<(Q : ℝ) := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hQbig)
    have hv := mul_lt_mul_of_pos_left hDQ hδ
    rw [mul_inv_cancel₀ hδ.ne'] at hv
    simpa only [mul_comm] using hv)
  have hs := hsmall (gridLabel Q hQ) (measurable_gridLabel Q hQ)
    (fun x y h => (gridLabel_dist_le Q hQ h).trans_lt hm)
  have hu := hupper Q hQQ hQ
  have hc := Entropy.rate_comparison area f hf p (gridLabel Q hQ) hp (measurable_gridLabel Q hQ)
  linarith

lemma standardDerivative_average_bounds (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) :
    0≤Real.log ‖standardDerivativeProduct k z n‖/(n : ℝ) ∧
    Real.log ‖standardDerivativeProduct k z n‖/(n : ℝ)≤Real.log (9*growthBase k) := by
  have hD : 1≤9*growthBase k := by have hg := growthBase_ge_four k hk; linarith
  have hp := standardDerivativeProduct_norm_ge_one k z n
  refine ⟨div_nonneg (Real.log_nonneg hp) (Nat.cast_nonneg _),?_⟩
  by_cases hn : n=0
  · subst n
    simpa only [Nat.cast_zero,div_zero] using Real.log_nonneg hD
  · have hnpos : (0 : ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hp) (standardDerivativeProduct_norm_bound k hk z n)
    rw [Real.log_pow] at hlog
    exact (div_le_iff₀ hnpos).mpr (by simpa only [mul_comm] using hlog)

lemma tendsto_integral_standardDerivative_average (k : ℝ) (hk : 0≤k) :
    Tendsto (fun n : ℕ => (∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area)/(n : ℝ))
      atTop (𝓝 (∫ z,standardLyapunov k hk z ∂area)) := by
  have ht := tendsto_integral_of_dominated_convergence (μ:=area) (fun _ : Torus => Real.log (9*growthBase k))
    (fun n => ((integrable_log_standardDerivativeProduct k n).div_const (n : ℝ)).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (standardDerivative_average_bounds k hk z n).1]
      exact (standardDerivative_average_bounds k hk z n).2)) (ae_standardLyapunov_rate k hk)
  simpa only [integral_div] using ht

theorem metricEntropy_le_integral_standardLyapunov (k : ℝ) (hk : 0≤k) :
    metricEntropy area (standardMap k)≤ENNReal.ofReal (∫ z,standardLyapunov k hk z ∂area) := by
  have htin : Tendsto (fun n : ℕ =>
      (Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z n‖ ∂area))/(n : ℝ))
      atTop (𝓝 (∫ z,standardLyapunov k hk z ∂area)) := by
    have hh := (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => Real.log 1000/(n : ℝ)) atTop (𝓝 0)).add
        (tendsto_integral_standardDerivative_average k hk)
    simpa only [add_div,zero_add] using hh
  apply iSup_le
  intro r
  apply iSup_le
  intro p
  rw [partitionEntropy_eq_ofReal_rate area _ (measurePreserving_standardMap k) p]
  apply ENNReal.ofReal_le_ofReal
  apply ge_of_tendsto htin
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have hu := finite_rate_le_of_grid_rates ((standardMap k)^[n]) ((measurePreserving_standardMap k).iterate n)
    _ (eventually_grid_rate_derivative_upper k hk n) (Entropy.word (standardMap k) p.val n)
    (Entropy.word_measurable _ (measurePreserving_standardMap k).measurable p.val p.property n)
  rw [Entropy.rate_power_word area _ (measurePreserving_standardMap k) p.val p.property n hnpos] at hu
  exact (le_div_iff₀ (Nat.cast_pos.mpr hnpos)).mpr (by simpa only [mul_comm] using hu)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma standardLyapunov_le_log_growthBase (k : ℝ) (hk : 0≤k) (z : Torus) :
    standardLyapunov k hk z≤Real.log (growthBase k) := by
  change Real.log (growthBase k)*(transferCocycle k hk).lowerRate (recurrenceCoordinates z)≤_
  have hh := (transferCocycle k hk).lowerRate_bounds (recurrenceCoordinates z)
  nlinarith [log_growthBase_pos k hk]

theorem integral_standardLyapunov_le_metricEntropy (k : ℝ) (hk : 0≤k) :
    ENNReal.ofReal (∫ z,standardLyapunov k hk z ∂area)≤ metricEntropy area (standardMap k) := by
  by_cases htop : metricEntropy area (standardMap k)=∞
  · rw [htop]; exact le_top
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨m,u,a,χ,hu,hinv,ha,hgap,hL,happrox⟩ := exists_lower_spectral_bins
    (standardLyapunov k hk) (measurable_standardLyapunov k hk) (standardLyapunov_nonneg k hk)
    (Real.log (growthBase k)) (standardLyapunov_le_log_growthBase k hk) (η/3) (by positivity)
  have hh := entropy_lower_finite_spectral_bins k hk u hu
    (hinv (standardMap k) (standardLyapunov_invariant k hk)) a χ ha hgap hL
  have hh' := (ENNReal.ofReal_le_iff_le_toReal htop).mp hh
  have hi : Integrable (fun x => a (u x)) area := LocalCoding.integrable_finite_observable area u hu a
  have hle := integral_mono (integrable_standardLyapunov k hk) (hi.add (integrable_const η))
    (fun x => by change standardLyapunov k hk x≤a (u x)+η; have hx := (happrox x).2; linarith)
  simp only [Pi.add_apply] at hle
  rw [integral_add hi (integrable_const η),integral_const] at hle
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hle
  linarith

theorem metricEntropy_eq_integral_standardLyapunov (k : ℝ) (hk : 0≤k) :
    metricEntropy area (standardMap k)=ENNReal.ofReal (∫ z,standardLyapunov k hk z ∂area) :=
  le_antisymm (metricEntropy_le_integral_standardLyapunov k hk)
    (integral_standardLyapunov_le_metricEntropy k hk)
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem actual_positive_lyapunov_and_entropy :
    ∃ k₀ : ℝ,0<k₀ ∧ ∀ k : ℝ,k₀≤k →
      ∃ L : Torus → ℝ,Measurable L ∧ Integrable L area ∧
        (∀ z,L (standardMap k z)=L z) ∧
        (∀ᵐ z ∂area,LyapunovSpectrumAt k z (L z)) ∧
        (∀ᵐ z ∂area,Tendsto
          (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖/(n : ℝ)) atTop (𝓝 (L z))) ∧
        0<area {z | 0<L z} ∧ metricEntropy area (standardMap k)=ENNReal.ofReal (∫ z,L z ∂area) := by
  obtain ⟨K,hK,hdef⟩ := eventually_meanDeficit_small (1/8 : ℝ) (by norm_num)
  refine ⟨K,hK,?_⟩
  intro k hk
  have hk0 : 0≤k := hK.le.trans hk
  exact ⟨standardLyapunov k hk0,measurable_standardLyapunov k hk0,integrable_standardLyapunov k hk0,
    standardLyapunov_invariant k hk0,ae_standardLyapunov_spectrum k hk0,ae_standardLyapunov_rate k hk0,
    positive_standardLyapunov_of_deficit k hk0 (hdef k hk),metricEntropy_eq_integral_standardLyapunov k hk0⟩
end StandardMapEntropy

end
end

end OAI
