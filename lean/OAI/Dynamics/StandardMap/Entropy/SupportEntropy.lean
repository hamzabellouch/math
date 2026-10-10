import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Stable.PerronStability
import OAI.Dynamics.StandardMap.Entropy.ObservableEntropy

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype α] [Fintype β]

lemma shannon_support_bound (p : α → ℝ) (hp : ∀ a,0≤p a) (s : Finset α)
    (hs : ∀ a,a∉s → p a=0) :
    shannon p≤Real.negMulLog (∑ a,p a)+(∑ a,p a)*Real.log (s.card : ℝ) := by
  classical
  have hsum : ∑ a : s,p a=∑ a,p a := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => hs a ha)
  have hent : shannon (fun a : s => p a)=shannon p := by
    unfold shannon
    dsimp only
    rw [←Finset.sum_subtype s (fun a => Iff.rfl) (fun a => Real.negMulLog (p a))]
    exact Finset.sum_subset (Finset.subset_univ s) (fun a _ ha => by rw [hs a ha,Real.negMulLog_zero])
  have h := shannon_total_bound (fun a : s => p a) (fun a => hp a)
  simpa only [hent,hsum,Fintype.card_coe] using h

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]
lemma cond_support_bound (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (S : β → Finset α) (hS : ∀ x,p x∈S (q x)) :
    cond μ p q≤∑ b,mass μ q b*Real.log ((S b).card : ℝ) := by
  classical
  have rz (b : β) (a : α) (ha : a∉S b) : mass μ (fun x => (p x,q x)) (a,b)=0 := by
    have he : (fun x => (p x,q x)) ⁻¹' {(a,b)}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx1,hx2⟩ := Prod.mk.inj hx
      exact ha (hx1 ▸ hx2 ▸ hS x)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    shannon_support_bound (fun a => mass μ (fun x => (p x,q x)) (a,b))
      (fun a => mass_nonneg μ _ _) (S b) (rz b))
  simp only [←mass_joint_col μ p q hp hq,shannon,Finset.sum_add_distrib] at hh
  unfold cond obs shannon
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  linarith

end StandardMapEntropy.Entropy
end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def errorObs (p q : Ω → α) (x : Ω) : Bool := by
  classical
  exact decide (p x≠q x)
lemma errorObs_measurable (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    Measurable (errorObs p q) := by
  classical
  exact (measurable_of_countable (fun v : α×α => decide (v.1≠v.2))).comp (hp.prodMk hq)
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma errorObs_false (p q : Ω → α) (x : Ω) : errorObs p q x=false ↔ p x=q x := by
  classical
  simp [errorObs]
lemma obs_bool (e : Ω → Bool) (he : Measurable e) :
    obs μ e=Real.negMulLog (mass μ e true)+Real.negMulLog (1-mass μ e true) := by
  have hm := mass_sum μ e he
  simp only [Fintype.sum_bool,measure_univ,ENNReal.toReal_one] at hm
  have hf : mass μ e false=1-mass μ e true := by linarith
  simp only [obs,shannon,Fintype.sum_bool,hf]

lemma cond_fano (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q≤obs μ (errorObs p q)+mass μ (errorObs p q) true*Real.log (Fintype.card α) := by
  classical
  let e := errorObs p q
  have he := errorObs_measurable p q hp hq
  let S : Bool×α → Finset α := fun v => if v.1 then Finset.univ else {v.2}
  have hs (x : Ω) : p x∈S (e x,q x) := by
    by_cases h : p x=q x <;> simp [S,e,errorObs,h]
  have hb := cond_support_bound μ p (fun x => (e x,q x)) hp (he.prodMk hq) S hs
  have hv : (∑ v : Bool×α,mass μ (fun x => (e x,q x)) v*Real.log ((S v).card : ℝ))=
      mass μ e true*Real.log (Fintype.card α) := by
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,S,Bool.false_eq_true,↓reduceIte,
      Finset.card_univ,Finset.card_singleton,Nat.cast_one,Real.log_one,mul_zero,Finset.sum_const_zero,add_zero]
    rw [←Finset.sum_mul,←mass_joint_row μ e q he hq true]
  rw [hv] at hb
  have hm := obs_pair_ge_right μ e (fun x => (p x,q x)) he (hp.prodMk hq)
  rw [obs_triple_assoc] at hm
  have hc := cond_chain μ e q p
  have ho := cond_le_obs μ e q he hq
  unfold cond at hb hc ho ⊢
  linarith
lemma cond_fano_bound (p q : Ω → α) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q≤Real.negMulLog (mass μ (errorObs p q) true)+
      Real.negMulLog (1-mass μ (errorObs p q) true)+
      mass μ (errorObs p q) true*Real.log (Fintype.card α) := by
  rw [←obs_bool μ _ (errorObs_measurable p q hp hq)]
  exact cond_fano μ p q hp hq

lemma cond_small_of_error (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ,0<η ∧ ∀ (p q : Ω → α), Measurable p → Measurable q →
      mass μ (errorObs p q) true<η → cond μ p q<ε := by
  let B : ℝ → ℝ := fun d => Real.negMulLog d+Real.negMulLog (1-d)+d*Real.log (Fintype.card α)
  have hB : Continuous B := Real.continuous_negMulLog.add
    (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id)) |>.add
      (continuous_id.mul continuous_const)
  have hB0 : B 0=0 := by simp [B]
  have hev : ∀ᶠ d in 𝓝 (0 : ℝ),B d<ε :=
    (hB.continuousAt : ContinuousAt B 0).eventually (gt_mem_nhds (show B 0<ε by rw [hB0]; exact hε))
  obtain ⟨η,hη,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨η,hη,?_⟩
  intro p q hp hq he
  have hm := mass_nonneg μ (errorObs p q) true
  have hb := hball (show mass μ (errorObs p q) true∈Metric.ball 0 η from by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hm] using he)
  exact lt_of_le_of_lt (cond_fano_bound μ p q hp hq) hb

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop]
variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma compact_partition_core (p : Ω → α) (hp : Measurable p) (ε : ℝ) (hε : 0<ε) :
    ∃ K : Set Ω, IsCompact K ∧ μ Kᶜ≤ENNReal.ofReal ε ∧
      ∃ δ : ℝ,0<δ ∧ ∀ x∈K,∀ y∈K,dist x y<δ → p x=p y := by
  classical
  have hc : (0 : ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hr : 0<ε/(Fintype.card α : ℝ) := div_pos hε hc
  have ha (a : α) := (hp (measurableSet_singleton a)).exists_isCompact_sdiff_lt
    (measure_ne_top μ _) (ENNReal.ofReal_pos.mpr hr).ne'
  choose K hKsub hKcompact hKerr using ha
  have herr : μ (⋃ a,K a)ᶜ≤ENNReal.ofReal ε := by
    have hs : (⋃ a,K a)ᶜ=⋃ a,(p ⁻¹' {a})\K a := by
      ext x
      simp only [mem_compl_iff,mem_iUnion,not_exists,Set.mem_sdiff,mem_preimage,mem_singleton_iff]
      constructor
      · intro h; exact ⟨p x,rfl,h (p x)⟩
      · rintro ⟨a,ha,haK⟩ b hb
        have hpb := hKsub b hb
        exact haK ((ha.symm.trans hpb) ▸ hb)
    rw [hs]
    calc
      _ ≤ ∑ a,μ ((p ⁻¹' {a})\K a) := by simpa only [tsum_fintype] using measure_iUnion_le (fun a => (p ⁻¹' {a})\K a)
      _ ≤ ∑ _a : α,ENNReal.ofReal (ε/(Fintype.card α : ℝ)) := Finset.sum_le_sum (fun a _ => (hKerr a).le)
      _ = (Fintype.card α : ℝ≥0∞)*ENNReal.ofReal (ε/(Fintype.card α : ℝ)) := by simp
      _ = ENNReal.ofReal ((Fintype.card α : ℝ)*(ε/(Fintype.card α : ℝ))) := by
        rw [ENNReal.ofReal_mul hc.le,ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ε := by congr 1; field_simp
  have hsep (ab : α×α) : ∃ δ : ℝ,0<δ ∧ ∀ x∈K ab.1,∀ y∈K ab.2,ab.1≠ab.2 → δ<dist x y := by
    by_cases he : ab.1=ab.2
    · exact ⟨1,by norm_num,fun _ _ _ _ h => False.elim (h he)⟩
    have hd : Disjoint (K ab.1) (K ab.2) := by
      apply disjoint_left.mpr
      intro x hx hy
      exact he ((hKsub ab.1 hx).symm.trans (hKsub ab.2 hy))
    obtain ⟨δ,hδ,hxy⟩ := Metric.exists_pos_forall_lt_edist (hKcompact ab.1) (hKcompact ab.2).isClosed hd
    refine ⟨δ,hδ,?_⟩
    intro x hx y hy _
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (edist_ne_top x y)).mpr (hxy x hx y hy)
    simpa only [edist_dist,ENNReal.coe_toReal,ENNReal.toReal_ofReal dist_nonneg] using h
  choose d hd hdsep using hsep
  let δ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (α×α)).Nonempty) d
  have hδ : 0<δ := (Finset.lt_inf'_iff _).mpr (fun ab _ => hd ab)
  refine ⟨⋃ a,K a,isCompact_iUnion hKcompact,herr,δ,hδ,?_⟩
  intro x hx y hy hxy
  obtain ⟨a,ha⟩ := mem_iUnion.mp hx
  obtain ⟨b,hb⟩ := mem_iUnion.mp hy
  have he : a=b := by
    by_contra h
    have hs := hdsep (a,b) x ha y hb h
    exact (not_lt_of_ge ((Finset.inf'_le d (Finset.mem_univ (a,b))).trans hs.le)) hxy
  exact (hKsub a ha).trans (he.trans (hKsub b hb).symm)

lemma cond_small_of_diameter (p : Ω → α) (hp : Measurable p) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ {β : Type} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
      (q : Ω → β),Measurable q →
      (∀ x y,q x=q y → dist x y<δ) → cond μ p q<ε := by
  classical
  obtain ⟨η,hη,hsmall⟩ := cond_small_of_error (α:=α) μ ε hε
  obtain ⟨K,hK,hKerr,δ,hδ,hsep⟩ := compact_partition_core μ p hp (η/2) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro β _ _ _ q hq hdiam
  let g : β → α := fun b => if h : ∃ x∈K,q x=b then p h.choose else Classical.choice inferInstance
  have he (x : Ω) (hx : x∈K) : g (q x)=p x := by
    have h : ∃ y∈K,q y=q x := ⟨x,hx,rfl⟩
    dsimp only [g]
    rw [dite_eq_left h]
    exact hsep h.choose h.choose_spec.1 x hx (hdiam _ _ h.choose_spec.2)
  have hm : mass μ (errorObs p (g ∘ q)) true<η := by
    have hs : (errorObs p (g ∘ q)) ⁻¹' {true}⊆Kᶜ := by
      intro x hx hxK
      have heq := (errorObs_false p (g ∘ q) x).mpr (he x hxK).symm
      have htrue : errorObs p (g ∘ q) x=true := hx
      rw [htrue] at heq
      cases heq
    have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hs).trans hKerr)
    rw [ENNReal.toReal_ofReal (by positivity)] at hu
    exact lt_of_le_of_lt hu (by linarith)
  have hh := hsmall p (g ∘ q) hp ((measurable_of_countable g).comp hq) hm
  exact lt_of_le_of_lt (cond_factor_right μ p q g hp hq) hh

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

lemma circleRep_dist_le (x y : Circle) : dist x y≤|circleRep x-circleRep y| := by
  have h : ‖((circleRep x-circleRep y : ℝ) : Circle)‖≤‖circleRep x-circleRep y‖ :=
    QuotientAddGroup.norm_mk_le_norm
  simpa only [QuotientAddGroup.mk_sub,coe_circleRep,←dist_eq_norm,Real.dist_eq] using h
lemma gridLabel_dist_le (Q : ℕ) (hQ : 0<Q) {z w : Torus}
    (h : gridLabel Q hQ z=gridLabel Q hQ w) : dist z w≤1/(Q : ℝ) := by
  obtain ⟨h1,h2⟩ := (gridLabel_eq_iff Q hQ z w).mp h
  exact max_le ((circleRep_dist_le z.1 w.1).trans (gridIndex_close Q hQ h1))
    ((circleRep_dist_le z.2 w.2).trans (gridIndex_close Q hQ h2))

lemma metricEntropy_le_of_grid_rates (f : Torus → Torus) (hf : MeasurePreserving f area area) (b : ℝ)
    (hb : ∀ ε : ℝ,0<ε → ∃ Q₀ : ℕ,∀ Q : ℕ,Q₀≤Q → ∀ hQ : 0<Q,
      Entropy.rate area f (gridLabel Q hQ)≤b+ε) :
    metricEntropy area f≤ENNReal.ofReal b := by
  apply iSup_le
  intro r
  apply iSup_le
  intro p
  rw [partitionEntropy_eq_ofReal_rate area f hf p]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,hsmall⟩ := Entropy.cond_small_of_diameter area p.val p.property (ε/2) (by positivity)
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
  have hc := Entropy.rate_comparison area f hf p.val (gridLabel Q hQ) p.property (measurable_gridLabel Q hQ)
  linarith

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

noncomputable def complexRep (z : Torus) : ℂ := ⟨circleRep z.1,circleRep z.2⟩
@[simp] lemma complexProjection_complexRep (z : Torus) : complexProjection (complexRep z)=z := by
  ext <;> simp only [complexProjection,complexRep,coe_circleRep]
lemma gridLabel_complexRep_close (Q : ℕ) (hQ : 0<Q) {z w : Torus}
    (h : gridLabel Q hQ z=gridLabel Q hQ w) : ‖complexRep z-complexRep w‖≤2/(Q : ℝ) := by
  obtain ⟨h1,h2⟩ := (gridLabel_eq_iff Q hQ z w).mp h
  have hh := add_le_add (gridIndex_close Q hQ h1) (gridIndex_close Q hQ h2)
  calc
    _ ≤ |circleRep z.1-circleRep w.1|+|circleRep z.2-circleRep w.2| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1/(Q : ℝ)+1/(Q : ℝ) := hh
    _ = _ := by ring

lemma integrable_log_standardDerivativeProduct (k : ℝ) (n : ℕ) :
    Integrable (fun z => Real.log ‖standardDerivativeProduct k z n‖) area :=
  ((continuous_standardDerivativeProduct k n).norm.log (fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k z n)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma standard_iterate_grid_cover (k : ℝ) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hLip : ∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
       standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖)
    (Q : ℕ) (hQ : 0<Q) (hQC : 4*C≤(Q : ℝ)) (z : Torus) :
    ∃ S : Finset (Fin (Q*Q+1)),(S.card : ℝ)≤1000*‖standardDerivativeProduct k z n‖ ∧
      ∀ w : Torus,gridLabel Q hQ w=gridLabel Q hQ z → gridLabel Q hQ ((standardMap k)^[n] w)∈S := by
  have hQp : (0 : ℝ)<Q := Nat.cast_pos.mpr hQ
  obtain ⟨S,hcard,hcover⟩ := (standardDerivativeProduct_area k z n).grid_cover Q hQ ((standardLift k)^[n] (complexRep z))
  refine ⟨S,hcard,?_⟩
  intro w hw
  have hdist := gridLabel_complexRep_close Q hQ hw
  have ht := quadratic_taylor_of_derivative_lipschitz ((standardLift k)^[n])
    (fun u => standardDerivativeProduct k (complexProjection u) n)
    (hasFDerivAt_standardLift_iterate k n) hC hLip (complexRep z) (complexRep w)
  rw [complexProjection_complexRep] at ht
  have herror : ‖(standardLift k)^[n] (complexRep w)-(standardLift k)^[n] (complexRep z)-
      standardDerivativeProduct k z n (complexRep w-complexRep z)‖≤1/(Q : ℝ) := by
    apply ht.trans
    calc
      _ ≤ C*(2/(Q : ℝ))^2 := mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hdist) hC
      _ ≤ 1/(Q : ℝ) := by
        calc
          C*(2/(Q : ℝ))^2 = (4*C)/(Q : ℝ)^2 := by ring
          _ ≤ 1/(Q : ℝ) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hQp) hQp).mpr
            nlinarith
  have hh := hcover (complexRep w-complexRep z) ((standardLift k)^[n] (complexRep w)) hdist herror
  simpa only [complexProjection_iterate,complexProjection_complexRep] using hh

lemma standard_iterate_grid_log_variation (k : ℝ) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hLip : ∀ z w : ℂ,‖standardDerivativeProduct k (complexProjection z) n-
       standardDerivativeProduct k (complexProjection w) n‖≤C*‖z-w‖)
    (Q : ℕ) (hQ : 0<Q) {z w : Torus} (hw : gridLabel Q hQ w=gridLabel Q hQ z) :
    Real.log ‖standardDerivativeProduct k z n‖≤Real.log ‖standardDerivativeProduct k w n‖+2*C/(Q : ℝ) := by
  have hdist := gridLabel_complexRep_close Q hQ hw.symm
  have hd := hLip (complexRep z) (complexRep w)
  simp only [complexProjection_complexRep] at hd
  have hl := (le_abs_self (Real.log ‖standardDerivativeProduct k z n‖-Real.log ‖standardDerivativeProduct k w n‖)).trans
    (log_norm_sub_le_of_one_le (standardDerivativeProduct_norm_ge_one k z n) (standardDerivativeProduct_norm_ge_one k w n))
  have hh := hl.trans (hd.trans (mul_le_mul_of_nonneg_left hdist hC))
  rw [show C*(2/(Q : ℝ))=2*C/(Q : ℝ) by ring] at hh
  linarith

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma exists_dyadic_level {r : ℝ} (hr : 0<r) : ∃ n : ℕ,1≤(2 : ℝ)^n*r := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt r⁻¹ (show (1 : ℝ)<2 by norm_num)
  refine ⟨n,?_⟩
  have hh := mul_lt_mul_of_pos_right hn hr
  rw [inv_mul_cancel₀ hr.ne'] at hh
  exact hh.le
noncomputable def dyadicLevel (r : ℝ) (hr : 0<r) : ℕ := Nat.find (exists_dyadic_level hr)
lemma dyadicLevel_lower (r : ℝ) (hr : 0<r) : 1≤(2 : ℝ)^(dyadicLevel r hr)*r :=
  Nat.find_spec (exists_dyadic_level hr)
lemma dyadicLevel_upper (r : ℝ) (hr : 0<r) (hr1 : r≤1) :
    (2 : ℝ)^(dyadicLevel r hr)*r≤2 := by
  generalize hn : dyadicLevel r hr=n
  cases n with
  | zero => simpa only [pow_zero,one_mul] using hr1.trans (show (1 : ℝ)≤2 by norm_num)
  | succ n =>
    have hnot : ¬1≤(2 : ℝ)^n*r := Nat.find_min (exists_dyadic_level hr) (by change n<dyadicLevel r hr; rw [hn]; omega)
    rw [pow_succ]
    nlinarith [not_le.mp hnot]
lemma dyadicLevel_mono_bound {r s : ℝ} (hr : 0<r) (hs : 0<s) (J : ℕ)
    (h : r≤(2 : ℝ)^J*s) : dyadicLevel s hs≤dyadicLevel r hr+J := by
  apply Nat.find_min' (exists_dyadic_level hs)
  rw [pow_add,mul_assoc]
  exact (dyadicLevel_lower r hr).trans (mul_le_mul_of_nonneg_left h (by positivity))
lemma measurable_dyadicLevel {Ω : Type*} [MeasurableSpace Ω] (r : Ω → ℝ)
    (hr : ∀ x,0<r x) (hm : Measurable r) : Measurable (fun x => dyadicLevel (r x) (hr x)) := by
  exact measurable_find (fun x => exists_dyadic_level (hr x))
    (fun n => measurableSet_le measurable_const (measurable_const.mul hm))
lemma inv_dyadicLevel_le (r : ℝ) (hr : 0<r) : 1/(2 : ℝ)^(dyadicLevel r hr)≤r :=
  (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using dyadicLevel_lower r hr)

end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

abbrev AdaptiveSymbol := ℕ×ℕ
noncomputable def dyadicGridVal (n : ℕ) (z : Torus) : ℕ :=
  (gridLabel (2^n) (by positivity) z).val
lemma measurable_dyadicGridVal (n : ℕ) : Measurable (dyadicGridVal n) := by
  have hv : Measurable (fun j : Fin (2^n*2^n+1) => j.val) := measurable_of_countable _
  exact hv.comp (measurable_gridLabel (2^n) (by positivity))
noncomputable def adaptiveLabel (l : Torus → ℕ) (z : Torus) : AdaptiveSymbol :=
  (l z,dyadicGridVal (l z) z)
lemma measurable_nat_select {X : Type*} [MeasurableSpace X] (g : ℕ → X → ℕ)
    (hg : ∀ n,Measurable (g n)) (l : X → ℕ) (hl : Measurable l) :
    Measurable (fun z => g (l z) z) := by
  have hm : Measurable (fun w : ℕ×X => g w.1 w.2) :=
    measurable_from_prod_countable_right (f:=fun w : ℕ×X => g w.1 w.2) hg
  exact hm.comp (hl.prodMk measurable_id)
lemma measurable_adaptiveLabel (l : Torus → ℕ) (hl : Measurable l) : Measurable (adaptiveLabel l) := by
  have hm := measurable_nat_select dyadicGridVal measurable_dyadicGridVal l hl
  apply Measurable.prodMk hl hm
lemma adaptiveLabel_level {l : Torus → ℕ} {z w : Torus} (h : adaptiveLabel l z=adaptiveLabel l w) : l z=l w := congrArg Prod.fst h
lemma adaptiveLabel_grid {l : Torus → ℕ} {z w : Torus} (h : adaptiveLabel l z=adaptiveLabel l w) :
    gridLabel (2^(l z)) (by positivity) z=gridLabel (2^(l z)) (by positivity) w := by
  have hh := congrArg Prod.snd h
  simp only [adaptiveLabel] at hh
  rw [←adaptiveLabel_level h] at hh
  exact Fin.ext hh
lemma adaptiveLabel_rep_close {l : Torus → ℕ} {z w : Torus} (h : adaptiveLabel l z=adaptiveLabel l w) :
    ‖complexRep z-complexRep w‖≤2/(2 : ℝ)^(l z) := by
  have hh := gridLabel_complexRep_close (2^(l z)) (by positivity) (adaptiveLabel_grid h)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

noncomputable def adaptiveCenter (l : Torus → ℕ) (a : AdaptiveSymbol) : Torus := by
  classical
  exact if h : ∃ z,adaptiveLabel l z=a then Classical.choose h else (0,0)
lemma adaptiveCenter_label (l : Torus → ℕ) (z : Torus) :
    adaptiveLabel l (adaptiveCenter l (adaptiveLabel l z))=adaptiveLabel l z := by
  simp only [adaptiveCenter,dite_eq_left (show ∃ w,adaptiveLabel l w=adaptiveLabel l z from ⟨z,rfl⟩)]
  exact Classical.choose_spec (show ∃ w,adaptiveLabel l w=adaptiveLabel l z from ⟨z,rfl⟩)
noncomputable def adaptiveSuccessors (k : ℝ) (l : Torus → ℕ) (J M : ℕ) (a : AdaptiveSymbol) : Finset AdaptiveSymbol :=
  (Finset.Icc (a.1-J) (a.1+J)).biUnion (fun m =>
    (liftGridCover (2^m) (by positivity) (standardLift k (complexRep (adaptiveCenter l a))) M).image (fun j => (m,j.val)))
lemma adaptiveSuccessors_card (k : ℝ) (l : Torus → ℕ) (J M : ℕ) (a : AdaptiveSymbol) :
    (adaptiveSuccessors k l J M a).card≤(2*J+1)*(2*M+3)^2 := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _m∈Finset.Icc (a.1-J) (a.1+J),(2*M+3)^2 :=
      Finset.sum_le_sum (fun m _ => Finset.card_image_le.trans (liftGridCover_card _ _ _ _))
    _ ≤ (2*J+1)*(2*M+3)^2 := by
      simp only [Finset.sum_const,smul_eq_mul,Nat.card_Icc]
      exact Nat.mul_le_mul_right _ (by omega)

lemma standardLift_lipschitz_bound (k : ℝ) (hk : 0≤k) (z w : ℂ) :
    ‖standardLift k z-standardLift k w‖≤(9*growthBase k)*‖z-w‖ :=
  norm_sub_le_of_derivative_bound _ _ (hasFDerivAt_standardLift k) (fun _ => standardDerivative_norm_bound k hk _) z w

lemma adaptive_successor_mem (k : ℝ) (hk : 0≤k) (l : Torus → ℕ) (J M : ℕ)
    (hM : 2*(9*growthBase k)*(2 : ℝ)^J≤M) (z : Torus)
    (hnext : l (standardMap k z)≤l z+J) (hprev : l z≤l (standardMap k z)+J) :
    adaptiveLabel l (standardMap k z)∈adaptiveSuccessors k l J M (adaptiveLabel l z) := by
  let n := l z
  let m := l (standardMap k z)
  let c := adaptiveCenter l (adaptiveLabel l z)
  have hlab : adaptiveLabel l z=adaptiveLabel l c := (adaptiveCenter_label l z).symm
  have hdist := adaptiveLabel_rep_close hlab
  have hL : 0≤9*growthBase k := by have hg := growthBase_ge_four k hk; linarith
  have hpow : (2 : ℝ)^m≤(2 : ℝ)^n*(2 : ℝ)^J := by rw [←pow_add]; exact pow_le_pow_right₀ (by norm_num) hnext
  have hb : ‖standardLift k (complexRep z)-standardLift k (complexRep c)‖≤(M : ℝ)/(2 : ℝ)^m := by
    calc
      _ ≤ (9*growthBase k)*(2/(2 : ℝ)^n) := (standardLift_lipschitz_bound k hk _ _).trans
        (mul_le_mul_of_nonneg_left hdist hL)
      _ ≤ (M : ℝ)/(2 : ℝ)^m := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hh := mul_le_mul_of_nonneg_left hpow (show 0≤(9*growthBase k)*(2/(2 : ℝ)^n) by positivity)
        have he : (9*growthBase k)*(2/(2 : ℝ)^n)*((2 : ℝ)^n*(2 : ℝ)^J)=2*(9*growthBase k)*(2 : ℝ)^J := by field_simp
        exact hh.trans (he.le.trans hM)
  apply Finset.mem_biUnion.mpr
  refine ⟨m,Finset.mem_Icc.mpr ⟨by change n-J ≤ m; omega,hnext⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨gridLabel (2^m) (by positivity) (standardMap k z),?_,rfl⟩
  have hm := liftGridCover_mem (2^m) (by positivity) (standardLift k (complexRep c))
    (standardLift k (complexRep z)) M (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hb)
  simpa only [complexProjection_standardLift,complexProjection_complexRep] using hm

end StandardMapEntropy

end
end

end OAI
