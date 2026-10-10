import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.TailNameSaturation

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {α β : Type*} [Fintype α] [Fintype β]

lemma shannon_ge_one_sub_max (p : α → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (m : ℝ) (hm : ∀ a,p a ≤ m) : 1-m≤ shannon p := by
  have hh (a : α) : p a*(1-m)≤Real.negMulLog (p a) := by
    by_cases hz : p a=0
    · simp only [hz,zero_mul,Real.negMulLog_zero,le_refl]
    have hpos : 0<p a := lt_of_le_of_ne (hp a) (Ne.symm hz)
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) (hp a)
    have hu := mul_le_mul_of_nonneg_left (sub_le_sub_left (hm a) 1) (hp a)
    unfold Real.negMulLog
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hh a)
  simpa only [←Finset.sum_mul,hs,one_mul,shannon] using hh

lemma shannon_ge_total_sub_max (p : α → ℝ) (hp : ∀ a,0≤p a)
    (a₀ : α) (hm : ∀ a,p a≤p a₀) :
    (∑ a,p a)-p a₀≤ shannon p-Real.negMulLog (∑ a,p a) := by
  let S := ∑ a,p a
  have hS : 0≤S := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hz : S=0
  · have he (a : α) : p a=0 := le_antisymm ((Finset.single_le_sum
        (fun b _ => hp b) (Finset.mem_univ a)).trans_eq hz) (hp a)
    simp only [he,Finset.sum_const_zero,sub_self,shannon,Real.negMulLog_zero,le_refl]
  have hS0 : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
  have ht := shannon_ge_one_sub_max (fun a => p a/S)
    (fun a => div_nonneg (hp a) hS) (by rw [←Finset.sum_div]; exact div_self hz)
    (p a₀/S) (fun a => div_le_div_of_nonneg_right (hm a) hS)
  have hs := shannon_scale (fun a => p a/S) S
  have he : (fun a => S*(p a/S))=p := by funext a; exact mul_div_cancel₀ _ hz
  rw [he,←Finset.sum_div,div_self hz,one_mul] at hs
  have hh := mul_le_mul_of_nonneg_left ht hS
  have hc : S*(1-p a₀/S)=S-p a₀ := by field_simp
  rw [hc] at hh
  dsimp only [S] at hs hh
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

theorem exists_decoder_error_le_cond [Nonempty α] (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) :
    ∃ g : β → α,(μ {x | p x≠g (q x)}).toReal≤cond μ p q := by
  classical
  let J (a : α) (b : β) := mass μ (fun x => (p x,q x)) (a,b)
  have hm (b : β) : ∃ a₀ : α,∀ a,J a b≤J a₀ b := by
    obtain ⟨a,ha,hm⟩ := Finset.exists_max_image Finset.univ (fun a => J a b) Finset.univ_nonempty
    exact ⟨a,fun a' => hm a' (Finset.mem_univ a')⟩
  choose g hg using hm
  refine ⟨g,?_⟩
  have hcol (b : β) : ∑ a,J a b=mass μ q b := (mass_joint_col μ p q hp hq b).symm
  have hbound (b : β) : mass μ q b-J (g b) b≤
      shannon (fun a => J a b)-Real.negMulLog (mass μ q b) := by
    have hs := shannon_ge_total_sub_max (fun a => J a b) (fun a => mass_nonneg μ _ _)
      (g b) (hg b)
    rwa [hcol b] at hs
  have hall := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hbound b)
  have herr : (μ {x | p x≠g (q x)}).toReal=∑ b,(mass μ q b-J (g b) b) := by
    let e : α×β → Bool := fun ab => decide (ab.1≠g ab.2)
    have he : (fun x => (e ((p x,q x)))) ⁻¹' {true}={x | p x≠g (q x)} := by
      ext x
      simp [e]
    have hh := mass_joint_col μ (fun x => (p x,q x)) (e ∘ (fun x => (p x,q x)))
      (hp.prodMk hq) ((measurable_of_countable e).comp (hp.prodMk hq)) true
    change mass μ (fun x => e (p x,q x)) true=_ at hh
    rw [mass,he] at hh
    simp only [Function.comp_def,mass_pair_function,Fintype.sum_prod_type] at hh
    rw [hh,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [←hcol b]
    have hsum : (∑ a : α,if a=g b then 0 else J a b)+J (g b) b=∑ a,J a b := by
      have hsingle : (∑ a : α,if a=g b then J a b else 0)=J (g b) b := by simp
      rw [←hsingle,←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by split_ifs <;> simp)
    have hid (a : α) : (if e (a,b)=true then J a b else 0)=if a=g b then 0 else J a b := by
      by_cases ha : a=g b <;> simp [e,ha]
    change (∑ a : α,if e (a,b)=true then J a b else 0)=(∑ a,J a b)-J (g b) b
    simp only [hid]
    exact (eq_sub_iff_add_eq.mpr hsum)
  rw [herr]
  unfold cond obs shannon
  simp only [Finset.sum_sub_distrib,shannon] at hall
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simpa only [Finset.sum_sub_distrib,J] using hall

end StandardMapEntropy.Entropy

end
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HyperbolicCoding

lemma exists_eventual_decoder {Y B : Type*} [MeasurableSpace Y] [MeasurableSpace B]
    [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (G : ℕ → Y → B) (hG : ∀ n,Measurable (G n)) :
    ∃ H : Y → B,Measurable H ∧ ∀ v b,(∀ᶠ n : ℕ in atTop,G n v=b) → H v=b := by
  classical
  let b₀ : B := Classical.choice inferInstance
  let E (b : B) : Set Y := {v | ∀ᶠ n : ℕ in atTop,G n v=b}
  have hEm (b : B) : MeasurableSet (E b) := by
    have he : E b=⋃ N : ℕ,⋂ n : ℕ,⋂ (_h : N≤n),(G n) ⁻¹' {b} := by
      ext v
      simp only [E,mem_ofPred_eq,eventually_atTop,mem_iUnion,mem_iInter,mem_preimage,mem_singleton_iff]
    rw [he]
    exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
      MeasurableSet.iInter (fun _ : N≤n => hG n (measurableSet_singleton b))))
  have huniq (v : Y) (b c : B) (hb : v∈E b) (hc : v∈E c) : b=c := by
    obtain ⟨n,hn⟩ := (hb.and hc).exists
    exact hn.1.symm.trans hn.2
  let H (v : Y) : B := if h : ∃ b,v∈E b then h.choose else b₀
  have hHb (v : Y) (b : B) (hb : v∈E b) : H v=b := by
    have he : ∃ b,v∈E b := ⟨b,hb⟩
    dsimp only [H]
    rw [dite_eq_left he]
    exact huniq v _ b he.choose_spec hb
  refine ⟨H,?_,hHb⟩
  apply measurable_to_countable'
  intro b
  have he : H ⁻¹' {b}=E b ∪ (if b=b₀ then (⋃ c,E c)ᶜ else ∅) := by
    ext v
    simp only [mem_preimage,mem_singleton_iff,mem_union]
    by_cases hv : ∃ c,v∈E c
    · have hn : v∉(⋃ c,E c)ᶜ := by simpa using hv
      have hh : H v=b ↔ v∈E b :=
        ⟨fun h => h ▸ (show v∈E (H v) from by simpa only [H,dite_eq_left hv] using hv.choose_spec),hHb v b⟩
      by_cases hb : b=b₀
      · rw [ite_eq_left hb]
        simpa only [hn,or_false] using hh
      · rw [ite_eq_right hb]
        simpa only [mem_empty_iff_false,or_false] using hh
    · have hh : H v=b₀ := dite_eq_right hv
      have hn : v∈(⋃ c,E c)ᶜ := by simpa using hv
      have hb : v∉E b := fun hb => hv ⟨b,hb⟩
      by_cases he : b=b₀
      · rw [ite_eq_left he]
        simp only [hn,or_true,iff_true]
        exact hh.trans he.symm
      · rw [ite_eq_right he]
        simp only [hb,mem_empty_iff_false,or_self,iff_false]
        exact fun hc => he (hc.symm.trans hh)
  rw [he]
  apply (hEm b).union
  split_ifs
  · exact (MeasurableSet.iUnion hEm).compl
  · exact MeasurableSet.empty

theorem exists_factor_of_approx {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
    (μ : Measure X) [IsFiniteMeasure μ] (Z : X → Y) (q : X → B)
    (happrox : ∀ ε : ℝ,0<ε → ∃ G : Y → B,Measurable G ∧
      μ {x | G (Z x)≠q x}<ENNReal.ofReal ε) :
    ∃ G : Y → B,Measurable G ∧ q=ᵐ[μ]G ∘ Z := by
  have happ (n : ℕ) := happrox ((1/2 : ℝ)^n) (pow_pos (by norm_num) n)
  choose G hG hsmall using happ
  obtain ⟨H,hH,hHb⟩ := exists_eventual_decoder G hG
  have hs : (∑' n : ℕ,μ {x | G n (Z x)≠q x})≠⊤ := by
    apply ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun n => (hsmall n).le))
    simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ)≤1/2),ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr
      (ENNReal.ofReal_lt_one.mpr (by norm_num))))
  have ha := ae_eventually_notMem hs
  refine ⟨H,hH,?_⟩
  filter_upwards [ha] with x hx
  exact (hHb (Z x) (q x) (hx.mono (fun n hn => not_ne_iff.mp hn))).symm

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

lemma cond_factor_left (p : Ω → α) (q : Ω → β) (g : α → γ)
    (hp : Measurable p) (hq : Measurable q) : cond μ (g ∘ p) q≤cond μ p q := by
  unfold cond
  apply sub_le_sub_right
  exact obs_factor μ (fun x => (p x,q x)) (fun v : α×β => (g v.1,v.2))
    (hp.prodMk hq) (((measurable_of_countable g).comp hp).prodMk hq)

lemma cond_future_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    Tendsto (fun m : ℕ => cond μ (word f p n) (fun x => word f p m (f^[n] x))) atTop
      (𝓝 ((n : ℝ)*rate μ f p)) := by
  simp_rw [cond_word_future_eq μ f hf p hp]
  induction n with
  | zero =>
    have he (m : ℕ) : obs μ (word f p (0+m))=obs μ (word f p m) := by
      have hi (a b : ℕ) (h : a=b) : obs μ (word f p a)=obs μ (word f p b) := by subst b; rfl
      exact hi _ _ (Nat.zero_add m)
    simpa only [he,sub_self,Nat.cast_zero,zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ n ih =>
    have ht : Tendsto (fun m : ℕ => n+m) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id
    have hd := (entropy_increment_tendsto μ f hf p hp).comp ht
    have hh := hd.add ih
    have he (m : ℕ) :
        (obs μ (word f p ((n+m)+1))-obs μ (word f p (n+m)))+
          (obs μ (word f p (n+m))-obs μ (word f p m))=
            obs μ (word f p (n+1+m))-obs μ (word f p m) := by
      rw [show n+1+m=n+m+1 from by omega]
      ring
    simp only [Function.comp_def,he] at hh
    convert hh using 1
    simp only [Nat.cast_add,Nat.cast_one]
    ring_nf

theorem tailObservable_self_of_rate_zero [Nonempty α] (f : Ω → Ω)
    (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p)
    (hz : rate μ f p=0) : TailObservable μ f p p := by
  intro n
  by_cases hn : n=0
  · subst n
    exact ⟨fun v => v 0,measurable_pi_apply 0,ae_of_all _ (fun x => rfl)⟩
  have hn0 : 0<n := Nat.pos_of_ne_zero hn
  apply exists_factor_of_approx μ (tailName f p n) p
  intro ε hε
  have ht := cond_future_tendsto μ f hf p hp n
  rw [hz,mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨M,hM⟩ := he.exists
  let r : Ω → (Fin M → α) := fun x => word f p M (f^[n] x)
  have hr : Measurable r := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n)
  have hl : cond μ p r≤cond μ (word f p n) r :=
    cond_factor_left μ (word f p n) r (fun v => v ⟨0,hn0⟩)
      (word_measurable f hf.measurable p hp n) hr
  obtain ⟨g,hg⟩ := exists_decoder_error_le_cond μ p r hp hr
  let G (v : ℕ → α) := g (fun i : Fin M => v i.val)
  have hG : Measurable G := (measurable_of_countable g).comp
    (Measurable.of_eval (fun i : Fin M => measurable_pi_apply i.val))
  have hEq : {x | G (tailName f p n x)≠p x}={x | p x≠g (r x)} := by
    ext x
    change (g (fun i : Fin M => p (f^[i.val+n] x))≠p x) ↔
      p x≠g (fun i : Fin M => p (f^[i.val] (f^[n] x)))
    simp only [←Function.iterate_add_apply,ne_comm]
  refine ⟨G,hG,?_⟩
  rw [hEq,←ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε.le]
  exact hg.trans_lt (hl.trans_lt hM)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

def wordPairEquiv (n : ℕ) : (Fin n → α×β) ≃ (Fin n → α)×(Fin n → β) where
  toFun v := (fun i => (v i).1,fun i => (v i).2)
  invFun v := fun i => (v.1 i,v.2 i)
  left_inv v := by funext i; rfl
  right_inv v := by cases v; rfl

omit [MeasurableSpace Ω] [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma wordPairEquiv_apply (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n : ℕ) :
    (wordPairEquiv n) ∘ word f (fun x => (p x,q x)) n=
      (fun x => (word f p n x,word f q n x)) := rfl

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_word_pair (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n : ℕ) :
    obs μ (word f (fun x => (p x,q x)) n)=obs μ (fun x => (word f p n x,word f q n x)) :=
  (obs_equiv μ (word f (fun x => (p x,q x)) n) (wordPairEquiv n)).symm

lemma rate_pair_ge_left (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f p≤rate μ f (fun x => (p x,q x)) := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp)
    (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair]
  exact div_le_div_of_nonneg_right (obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

lemma rate_pair_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    rate μ f (fun x => (p x,q x))≤rate μ f p+rate μ f q := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf (fun x => (p x,q x)) (hp.prodMk hq))
    ((rate_tendsto μ f hf p hp).add (rate_tendsto μ f hf q hq))
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [obs_word_pair,←add_div]
  exact div_le_div_of_nonneg_right (obs_pair_subadd_prob μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)) (Nat.cast_nonneg n)

lemma rate_pair_eq_of_zero (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (hz : rate μ f q=0) :
    rate μ f (fun x => (p x,q x))=rate μ f p := by
  have hl := rate_pair_ge_left μ f hf p q hp hq
  have hu := rate_pair_subadd μ f hf p q hp hq
  rw [hz,add_zero] at hu
  exact le_antisymm hu hl

omit [IsProbabilityMeasure μ] in
lemma rate_comp_iterate (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (hp : Measurable p) (s : ℕ) : rate μ f (p ∘ f^[s])=rate μ f p := by
  have he (n : ℕ) : word f (p ∘ f^[s]) n=(word f p n) ∘ f^[s] := by
    funext x i
    simp only [word,Function.comp_def,←Function.iterate_add_apply,Nat.add_comm]
  have hs (n : ℕ) : obs μ (word f (p ∘ f^[s]) n)=obs μ (word f p n) := by
    rw [he]
    exact obs_comp_preserving μ (f^[s]) (hf.iterate s) (word f p n) (word_measurable f hf.measurable p hp n)
  unfold rate
  simp only [hs]

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open HyperbolicCoding MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma rate_mul_le_cond_future_zero (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ f q=0) (n M : ℕ) :
    (n : ℝ)*rate μ f p≤cond μ (word f p n) (fun x => (word f p M (f^[n] x),q x)) := by
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,zero_mul]
    exact cond_nonneg μ (word f p 0) _ (word_measurable f hf.measurable p hp 0)
      (((word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate 0)).prodMk hq)
  by_contra h
  have hε : 0<(n : ℝ)*rate μ f p-cond μ (word f p n) (fun x => (word f p M (f^[n] x),q x)) :=
    sub_pos.mpr (lt_of_not_ge h)
  have ht := cond_future_tendsto μ f hf q hq n
  rw [hz,mul_zero] at ht
  obtain ⟨L,hL,hLM⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop M)).exists
  let r : Ω → α×β := fun x => (p x,q x)
  let R : Ω → (Fin L → α×β) := fun x => word f r L (f^[n] x)
  have hR : Measurable R := (word_measurable f hf.measurable r (hp.prodMk hq) L).comp (hf.measurable.iterate n)
  have hpN := word_measurable f hf.measurable p hp n
  have hqN := word_measurable f hf.measurable q hq n
  have hlo := rate_mul_le_cond_future μ f hf r (hp.prodMk hq) n L
  rw [rate_pair_eq_of_zero μ f hf p q hp hq hz] at hlo
  have he : cond μ (word f r n) R=cond μ (word f q n) R+
      cond μ (word f p n) (fun x => (word f q n x,R x)) := by
    rw [←cond_equiv_left μ (word f r n) R
      ((wordPairEquiv n).trans (Equiv.prodComm (Fin n → α) (Fin n → β)))]
    exact cond_chain μ (word f q n) R (word f p n)
  change _≤cond μ (word f r n) R at hlo
  rw [he] at hlo
  have hQ : cond μ (word f q n) R≤cond μ (word f q n) (fun x => word f q L (f^[n] x)) :=
    cond_factor_right μ (word f q n) R (fun v : Fin L → α×β => fun i => (v i).2) hqN hR
  let g (v : (Fin n → β)×(Fin L → α×β)) : (Fin M → α)×β :=
    (fun i => (v.2 ⟨i.val,lt_of_lt_of_le i.isLt hLM⟩).1,v.1 ⟨0,Nat.pos_of_ne_zero hn⟩)
  have hge : g ∘ (fun x => (word f q n x,R x))=
      (fun x => (word f p M (f^[n] x),q x)) := rfl
  have hP := cond_factor_right μ (word f p n) (fun x => (word f q n x,R x)) g hpN (hqN.prodMk hR)
  rw [hge] at hP
  linarith

lemma cond_future_zero_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (hz : rate μ f q=0) (n M : ℕ) :
    cond μ q (fun x => word f p M (f^[n] x))≤cond μ q (word f p n)+
      cond μ (word f p n) (fun x => word f p M (f^[n] x))-(n : ℝ)*rate μ f p := by
  let P := word f p n
  let R : Ω → (Fin M → α) := fun x => word f p M (f^[n] x)
  have hPm : Measurable P := word_measurable f hf.measurable p hp n
  have hRm : Measurable R := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate n)
  have hl := rate_mul_le_cond_future_zero μ f hf p q hp hq hz n M
  have hs := cond_pair_swap_right μ P q R
  have h1 := cond_chain μ P R q
  have h2 := cond_chain μ q R P
  have he : cond μ (fun x => (P x,q x)) R=cond μ (fun x => (q x,P x)) R :=
    (cond_equiv_left μ (fun x => (P x,q x)) R (Equiv.prodComm _ _)).symm
  have hu := cond_pair_right μ q P R hq hPm hRm
  change (n : ℝ)*rate μ f p≤cond μ P (fun x => (R x,q x)) at hl
  rw [←hs] at hl
  change cond μ q R≤cond μ q P+cond μ P R-(n : ℝ)*rate μ f p
  linarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma inverse_iterate_forward_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e.symm^[i] (e^[M] x)=e^[M-i] x := by
  have hx : e^[M] x=e^[i] (e^[M-i] x) := by
    rw [←Function.iterate_add_apply,show i+(M-i)=M from by omega]
  rw [hx]
  exact (show Function.LeftInverse (e.symm : Ω → Ω) e from e.symm_apply_apply).iterate i _

lemma forward_iterate_inverse_sub (e : Ω ≃ᵐ Ω) {M i : ℕ} (hi : i≤M) (x : Ω) :
    e^[M] (e.symm^[i] x)=e^[M-i] x := by
  have hx : e^[M] (e.symm^[i] x)=e^[M-i] (e^[i] (e.symm^[i] x)) := by
    rw [←Function.iterate_add_apply,show M-i+i=M from by omega]
  rw [hx,(show Function.LeftInverse (e : Ω → Ω) e.symm from e.apply_symm_apply).iterate i x]

def wordReverseEquiv (n : ℕ) : (Fin n → α) ≃ (Fin n → α) where
  toFun v i := v i.rev
  invFun v i := v i.rev
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp

omit [IsProbabilityMeasure μ] in
lemma obs_word_inverse (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    obs μ (word e.symm p n)=obs μ (word e p n) := by
  have hw : (word e.symm p n) ∘ e^[n-1]=(wordReverseEquiv n) ∘ word e p n := by
    funext x i
    change p (e.symm^[i.val] (e^[n-1] x))=p (e^[i.rev.val] x)
    rw [inverse_iterate_forward_sub e (by omega)]
    congr 2
    have h := Fin.val_rev i
    omega
  have h := obs_comp_preserving μ (e^[n-1]) (he.iterate (n-1)) (word e.symm p n)
    (word_measurable e.symm e.symm.measurable p hp n)
  rw [hw,obs_equiv] at h
  exact h.symm

omit [IsProbabilityMeasure μ] in
lemma rate_inverse (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → α) (hp : Measurable p) : rate μ e.symm p=rate μ e p := by
  unfold rate
  simp only [obs_word_inverse μ e he p hp]

end StandardMapEntropy.Entropy

end
end

end OAI
