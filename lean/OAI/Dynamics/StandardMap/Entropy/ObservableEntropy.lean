import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.LiftGrid

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

noncomputable def mass (p : Ω → α) (a : α) : ℝ := (μ (p ⁻¹' {a})).toReal
noncomputable def obs (p : Ω → α) : ℝ := shannon (mass μ p)
omit [IsFiniteMeasure μ] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma mass_nonneg (p : Ω → α) (a : α) : 0 ≤ mass μ p a := ENNReal.toReal_nonneg
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma fiber_disjoint (p : Ω → α) : Pairwise (Function.onFun Disjoint (fun a => p ⁻¹' {a})) := by
  intro a b hab
  exact Set.disjoint_left.mpr (fun x hxa hxb => hab (hxa.symm.trans hxb))
lemma mass_sum (p : Ω → α) (hp : Measurable p) : ∑ a,mass μ p a=(μ univ).toReal := by
  have he : (⋃ a : α,p ⁻¹' {a})=univ := by ext x; simp only [mem_iUnion,mem_preimage,mem_singleton_iff,exists_eq',mem_univ]
  rw [←he,measure_iUnion (fiber_disjoint p) (fun a => hp (measurableSet_singleton a)),tsum_fintype,
    ENNReal.toReal_sum (fun a _ => measure_ne_top μ _)]
  rfl
omit [Fintype α] in
lemma mass_joint_row (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (a : α) :
    mass μ p a=∑ b,mass μ (fun x => (p x,q x)) (a,b) := by
  have he : p ⁻¹' {a}=⋃ b : β,(fun x => (p x,q x)) ⁻¹' {(a,b)} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_iUnion,exists_and_left,exists_eq',and_true]
  have hd : Pairwise (Function.onFun Disjoint (fun b : β => (fun x => (p x,q x)) ⁻¹' {(a,b)})) := by
    intro b c hbc
    exact (fiber_disjoint (fun x => (p x,q x))) (by intro h; exact hbc (Prod.mk.inj h).2)
  unfold mass
  rw [he,measure_iUnion hd (fun b => (hp.prodMk hq) (measurableSet_singleton _)),tsum_fintype,
    ENNReal.toReal_sum (fun b _ => measure_ne_top μ _)]
omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mass_joint_swap (p : Ω → α) (q : Ω → β) (a : α) (b : β) :
    mass μ (fun x => (p x,q x)) (a,b)=mass μ (fun x => (q x,p x)) (b,a) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_comm]
omit [Fintype β] in
lemma mass_joint_col (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) (b : β) :
    mass μ q b=∑ a,mass μ (fun x => (p x,q x)) (a,b) := by
  rw [mass_joint_row μ q p hq hp]
  exact Finset.sum_congr rfl (fun a _ => mass_joint_swap μ q p b a)
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_swap (p : Ω → α) (q : Ω → β) :
    obs μ (fun x => (p x,q x))=obs μ (fun x => (q x,p x)) := by
  simp only [obs,shannon,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => congrArg Real.negMulLog (mass_joint_swap μ p q a b)))

lemma obs_pair_ge_left (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ p ≤ obs μ (fun x => (p x,q x)) := by
  have h := matrix_super_row (fun a b => mass μ (fun x => (p x,q x)) (a,b))
    (fun a b => mass_nonneg μ _ _)
  simpa only [obs,Prod.mk.eta,←mass_joint_row μ p q hp hq] using h
lemma obs_pair_ge_right (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ q ≤ obs μ (fun x => (p x,q x)) := by
  rw [obs_pair_swap]
  exact obs_pair_ge_left μ q p hq hp
lemma obs_pair_subadd (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    obs μ (fun x => (p x,q x)) ≤ obs μ p+obs μ q-Real.negMulLog (μ univ).toReal := by
  have h := matrix_subadd (fun a b => mass μ (fun x => (p x,q x)) (a,b))
    (fun a b => mass_nonneg μ _ _)
  simpa only [obs,Prod.mk.eta,←mass_joint_row μ p q hp hq,←mass_joint_col μ p q hp hq,mass_sum μ p hp] using h
lemma obs_pair_subadd_prob [IsProbabilityMeasure μ] (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : obs μ (fun x => (p x,q x)) ≤ obs μ p+obs μ q := by
  simpa only [measure_univ,ENNReal.toReal_one,Real.negMulLog_one,sub_zero] using obs_pair_subadd μ p q hp hq

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mass_pair_function [DecidableEq β] (p : Ω → α) (g : α → β) (a : α) (b : β) :
    mass μ (fun x => (p x,g (p x))) (a,b)=if g a=b then mass μ p a else 0 := by
  classical
  by_cases h : g a=b
  · rw [ite_eq_left h]
    unfold mass
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
    exact ⟨And.left,fun hp => ⟨hp,hp ▸ h⟩⟩
  · rw [ite_eq_right h]
    have he : ((fun x => (p x,g (p x))) ⁻¹' {(a,b)})=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ((congrArg g (Prod.mk.inj hx).1).symm.trans (Prod.mk.inj hx).2)
    simp only [mass,he,measure_empty,ENNReal.toReal_zero]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_pair_function (p : Ω → α) (g : α → β) :
    obs μ (fun x => (p x,g (p x)))=obs μ p := by
  classical
  simp only [obs,shannon,Fintype.sum_prod_type,mass_pair_function]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite Real.negMulLog,Real.negMulLog_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
lemma obs_factor (p : Ω → α) (g : α → β) (hp : Measurable p) (hg : Measurable (g ∘ p)) :
    obs μ (g ∘ p) ≤ obs μ p := by
  have h := obs_pair_ge_right μ p (g ∘ p) hp hg
  simpa only [Function.comp_def,obs_pair_function] using h

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma obs_equiv (p : Ω → α) (e : α ≃ β) : obs μ (e ∘ p)=obs μ p := by
  have he (a : α) : mass μ (e ∘ p) (e a)=mass μ p a := by
    unfold mass
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,e.injective.eq_iff]
  unfold obs shannon
  rw [←e.sum_comp]
  simp only [he]

lemma sum_mass_mul_integral (p : Ω → α) (hp : Measurable p) (g : α → ℝ) :
    ∑ a,mass μ p a*g a=∫ x,g (p x) ∂μ := by
  classical
  have he (x : Ω) : (∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=g (p x) := by
    simp only [indicator_apply,mem_preimage,mem_singleton_iff,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←show (fun x => ∑ a : α,(p ⁻¹' {a}).indicator (fun _ => g a) x)=(fun x => g (p x)) from funext he]
  rw [integral_finsetSum _ (fun a _ => (integrable_const _).indicator (hp (measurableSet_singleton a)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator (hp (measurableSet_singleton a)),integral_const,Measure.real,Measure.restrict_apply_univ]
  rfl

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variable {α β γ ζ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ζ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace ζ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] [MeasurableSingletonClass ζ]

omit [IsFiniteMeasure μ] [Fintype α] [Fintype β] [Fintype γ]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma mass_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) (a : α) (b : β) (c : γ) :
    mass μ (fun x => (p x,(q x,r x))) (a,(b,c))=
      mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_assoc]
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma obs_triple_assoc (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    obs μ (fun x => (p x,(q x,r x)))=obs μ (fun x => ((p x,q x),r x)) := by
  simpa only [Function.comp_def,Equiv.prodAssoc_apply] using obs_equiv μ (fun x => ((p x,q x),r x)) (Equiv.prodAssoc α β γ)

lemma obs_strong_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    obs μ (fun x => (p x,(q x,r x)))+obs μ q ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x)) := by
  let P : α → β → γ → ℝ := fun a b c => mass μ (fun x => (p x,(q x,r x))) (a,(b,c))
  have hrow (a : α) (b : β) : ∑ c,P a b c=mass μ (fun x => (p x,q x)) (a,b) := by
    simp only [P,mass_triple_assoc]
    exact (mass_joint_row μ _ r (hp.prodMk hq) hr (a,b)).symm
  have hcol (b : β) (c : γ) : ∑ a,P a b c=mass μ (fun x => (q x,r x)) (b,c) :=
    (mass_joint_col μ p _ hp (hq.prodMk hr) (b,c)).symm
  have htotal (b : β) : ∑ a,∑ c,P a b c=mass μ q b := by
    simp only [hrow]
    exact (mass_joint_col μ p q hp hq b).symm
  have hb (b : β) := matrix_subadd (fun a c => P a b c) (fun a c => mass_nonneg μ _ _)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hb b)
  simp only [shannon,Fintype.sum_prod_type,hrow,hcol,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  simp only [←mass_joint_col μ p q hp hq] at hh
  rw [Finset.sum_comm (f:=fun b a => ∑ c,Real.negMulLog (P a b c)),
    Finset.sum_comm (f:=fun b a => Real.negMulLog (mass μ (fun x => (p x,q x)) (a,b)))] at hh
  have h : obs μ (fun x => (p x,(q x,r x))) ≤
      obs μ (fun x => (p x,q x))+obs μ (fun x => (q x,r x))-obs μ q := by
    simpa only [obs,shannon,Fintype.sum_prod_type] using hh
  linarith

noncomputable def cond (p : Ω → α) (q : Ω → β) : ℝ := obs μ (fun x => (p x,q x))-obs μ q
lemma cond_nonneg (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) : 0 ≤ cond μ p q :=
  sub_nonneg.mpr (obs_pair_ge_right μ p q hp hq)
lemma cond_le_obs [IsProbabilityMeasure μ] (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ obs μ p := sub_le_iff_le_add.mpr (obs_pair_subadd_prob μ p q hp hq)
lemma cond_pair_right (p : Ω → α) (q : Ω → β) (r : Ω → γ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) :
    cond μ p (fun x => (q x,r x)) ≤ cond μ p q := by
  have h := obs_strong_subadd μ p q r hp hq hr
  dsimp [cond]
  linarith
omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_pair_swap_right (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ p (fun x => (q x,r x))=cond μ p (fun x => (r x,q x)) := by
  have he : obs μ (fun x => (p x,(r x,q x)))=obs μ (fun x => (p x,(q x,r x))) := by
    simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.prodComm_apply,Prod.swap_prod_mk] using
      obs_equiv μ (fun x => (p x,(q x,r x))) (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm β γ))
  unfold cond
  rw [he,obs_pair_swap μ q r]

omit [IsFiniteMeasure μ] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ] in
lemma cond_chain (p : Ω → α) (q : Ω → β) (r : Ω → γ) :
    cond μ (fun x => (p x,r x)) q=cond μ p q+cond μ r (fun x => (p x,q x)) := by
  have h1 := obs_pair_swap μ (fun x => (p x,r x)) q
  have h2 := obs_triple_assoc μ q p r
  have h3 := obs_pair_swap μ (fun x => (q x,p x)) r
  have h4 := cond_pair_swap_right μ r q p
  unfold cond at *
  have h5 := obs_pair_swap μ p q
  linarith
lemma cond_factor_right (p : Ω → α) (q : Ω → β) (g : β → γ)
    (hp : Measurable p) (hq : Measurable q) :
    cond μ p q ≤ cond μ p (g ∘ q) := by
  have hg : Measurable (g ∘ q) := (measurable_of_countable g).comp hq
  have h := cond_pair_right μ p (g ∘ q) q hp hg hq
  have he0 : cond μ p (fun x => (q x,g (q x)))=cond μ p q := by
    unfold cond
    dsimp only
    rw [obs_triple_assoc]
    rw [show obs μ (fun x => ((p x,q x),g (q x)))=obs μ (fun x => (p x,q x)) from
      obs_pair_function μ (fun x => (p x,q x)) (fun v : α×β => g v.2)]
    rw [obs_pair_function μ q g]
  have he : cond μ p (fun x => (g (q x),q x))=cond μ p q :=
    (cond_pair_swap_right μ p (g ∘ q) q).trans he0
  calc
    cond μ p q = cond μ p (fun x => (g (q x),q x)) := he.symm
    _ ≤ cond μ p (g ∘ q) := h

lemma cond_pair_subadd (p : Ω → α) (q : Ω → β) (r : Ω → γ) (s : Ω → ζ)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (hs : Measurable s) :
    cond μ (fun x => (p x,r x)) (fun x => (q x,s x)) ≤ cond μ p q+cond μ r s := by
  rw [cond_chain]
  apply add_le_add (cond_pair_right μ p q s hp hq hs)
  exact cond_factor_right μ r (fun x => (p x,(q x,s x))) (fun v : α×(β×ζ) => v.2.2) hr (hp.prodMk (hq.prodMk hs))

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma obs_nonneg (p : Ω → α) (hp : Measurable p) : 0 ≤ obs μ p := by
  apply shannon_nonneg _ (mass_nonneg μ p)
  rw [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
lemma obs_bound [Nonempty α] (p : Ω → α) (hp : Measurable p) : obs μ p ≤ Real.log (Fintype.card α) := by
  apply shannon_bound _ (mass_nonneg μ p)
  rw [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_const [Nonempty α] (a : α) : obs μ (fun _ : Ω => a)=0 := by
  classical
  have he (b : α) : mass μ (fun _ : Ω => a) b=if a=b then 1 else 0 := by
    unfold mass
    by_cases h : a=b
    · subst b; simp
    · have hs : (fun _ : Ω => a) ⁻¹' {b}=∅ := by ext x; simp [h]
      simp [hs,h]
  simp only [obs,shannon,he,apply_ite Real.negMulLog,Real.negMulLog_one,Real.negMulLog_zero,ite_self,Finset.sum_const_zero]

omit [IsProbabilityMeasure μ] [Fintype α] in
lemma mass_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) (a : α) : mass μ (p ∘ f) a=mass μ p a := by
  unfold mass
  rw [Set.preimage_comp,hf.measure_preimage (hp (measurableSet_singleton a)).nullMeasurableSet]
omit [IsProbabilityMeasure μ] in
lemma obs_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α)
    (hp : Measurable p) : obs μ (p ∘ f)=obs μ p := by
  simp only [obs,shannon,mass_comp_preserving μ f hf p hp]
omit [IsProbabilityMeasure μ] in
lemma cond_comp_preserving (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : cond μ (p ∘ f) (q ∘ f)=cond μ p q := by
  unfold cond
  rw [show (fun x => ((p ∘ f) x,(q ∘ f) x))=(fun x => (p x,q x)) ∘ f from rfl,
    obs_comp_preserving μ f hf _ (hp.prodMk hq),obs_comp_preserving μ f hf q hq]

def word (f : Ω → Ω) (p : Ω → α) (n : ℕ) (x : Ω) : Fin n → α := fun i => p (f^[i.val] x)
omit [Fintype α] [MeasurableSingletonClass α] in
lemma word_measurable (f : Ω → Ω) (hf : Measurable f) (p : Ω → α) (hp : Measurable p) (n : ℕ) :
    Measurable (word f p n) := Measurable.of_eval (fun i => hp.comp (hf.iterate i.val))
noncomputable def wordSplit (n m : ℕ) : (Fin (n+m) → α) ≃ (Fin n → α)×(Fin m → α) :=
  ((Equiv.piCongrLeft (fun _ : Fin (n+m) => α) finSumFinEquiv).symm).trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => α))
omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma wordSplit_apply (n m : ℕ) (v : Fin (n+m) → α) :
    wordSplit n m v=(fun i => v (Fin.castAdd m i),fun i => v (Fin.natAdd n i)) := by
  simp only [wordSplit,Equiv.trans_apply,Equiv.sumPiEquivProdPi_apply,
    Equiv.piCongrLeft_symm_apply,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right]
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma word_split (f : Ω → Ω) (p : Ω → α) (n m : ℕ) (x : Ω) :
    wordSplit n m (word f p (n+m) x)=(word f p n x,word f p m (f^[n] x)) := by
  rw [wordSplit_apply]
  apply Prod.ext
  · rfl
  · funext i
    simp only [word,Fin.val_natAdd,Nat.add_comm n i.val,Function.iterate_add_apply]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_split (f : Ω → Ω) (p : Ω → α) (n m : ℕ) :
    obs μ (word f p (n+m))=obs μ (fun x => (word f p n x,word f p m (f^[n] x))) := by
  have h := obs_equiv μ (word f p (n+m)) (wordSplit n m)
  simpa only [Function.comp_def,word_split] using h.symm
lemma obs_word_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    Subadditive (fun n => obs μ (word f p n)) := by
  intro n m
  dsimp only
  rw [obs_word_split]
  have h := obs_pair_subadd_prob μ (word f p n) ((word f p m) ∘ f^[n])
    (word_measurable f hf.measurable p hp n) ((word_measurable f hf.measurable p hp m).comp (hf.measurable.iterate n))
  rw [obs_comp_preserving μ (f^[n]) (hf.iterate n) _ (word_measurable f hf.measurable p hp m)] at h
  exact h
lemma obs_word_one (f : Ω → Ω) (p : Ω → α) (hp : Measurable p) : obs μ (word f p 1)=obs μ p := by
  have he (x : Ω) : word f p 1 x=(fun _ : Fin 1 => p x) := by
    funext i
    have hi : i.val=0 := by omega
    simp only [word,hi,Function.iterate_zero,Function.id_def]
  have hef : word f p 1=(fun x (_ : Fin 1) => p x) := funext he
  have h1 := obs_factor μ p (fun (a : α) (_ : Fin 1) => a) hp ((measurable_of_countable _).comp hp)
  have h2 := obs_factor μ (word f p 1) (fun v : Fin 1→α => v 0)
    (by simpa only [hef,Function.comp_def] using (measurable_of_countable (fun a (_ : Fin 1) => a)).comp hp)
    (by simpa only [Function.comp_def,word,Fin.val_zero,Function.iterate_zero,Function.id_def] using hp)
  apply le_antisymm
  · simpa only [Function.comp_def,hef] using h1
  · simpa only [Function.comp_def,word,Fin.val_zero,Function.iterate_zero,Function.id_def] using h2
omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma obs_word_zero (f : Ω → Ω) (p : Ω → α) : obs μ (word f p 0)=0 := by
  have he : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  rw [he,obs_const]

omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_left (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : α ≃ γ) :
    cond μ (e ∘ p) q=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr e (Equiv.refl β))
  unfold cond
  rw [show obs μ (fun x => ((e ∘ p) x,q x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h]
omit [IsProbabilityMeasure μ] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_equiv_right (p : Ω → α) (q : Ω → β)
    {γ : Type*} [Fintype γ] [MeasurableSpace γ] [MeasurableSingletonClass γ] (e : β ≃ γ) :
    cond μ p (e ∘ q)=cond μ p q := by
  have h := obs_equiv μ (fun x => (p x,q x)) (Equiv.prodCongr (Equiv.refl α) e)
  unfold cond
  rw [show obs μ (fun x => (p x,(e ∘ q) x))=obs μ (fun x => (p x,q x)) from
    by simpa only [Function.comp_def,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply] using h,
    obs_equiv μ q e]
omit [IsProbabilityMeasure μ] in
lemma cond_word_split (f : Ω → Ω) (p : Ω → α) (q : Ω → β) (n m : ℕ) :
    cond μ (word f p (n+m)) (word f q (n+m))=
      cond μ (fun x => (word f p n x,word f p m (f^[n] x)))
        (fun x => (word f q n x,word f q m (f^[n] x))) := by
  rw [←cond_equiv_left μ (word f p (n+m)) (word f q (n+m)) (wordSplit n m),
    ←cond_equiv_right μ ((wordSplit n m) ∘ word f p (n+m)) (word f q (n+m)) (wordSplit n m)]
  simp only [Function.comp_def,word_split]
lemma cond_word_subadd (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) :
    Subadditive (fun n => cond μ (word f p n) (word f q n)) := by
  intro n m
  dsimp only
  rw [cond_word_split]
  have h := cond_pair_subadd μ (word f p n) (word f q n) ((word f p m) ∘ f^[n]) ((word f q m) ∘ f^[n])
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)
    ((word_measurable f hf.measurable p hp m).comp (hf.measurable.iterate n))
    ((word_measurable f hf.measurable q hq m).comp (hf.measurable.iterate n))
  rw [cond_comp_preserving μ (f^[n]) (hf.iterate n) _ _
    (word_measurable f hf.measurable p hp m) (word_measurable f hf.measurable q hq m)] at h
  exact h
omit [IsProbabilityMeasure μ] in
lemma cond_word_one (f : Ω → Ω) (p : Ω → α) (q : Ω → β)
    (_hp : Measurable p) (_hq : Measurable q) :
    cond μ (word f p 1) (word f q 1)=cond μ p q := by
  have hp0 : (Equiv.funUnique (Fin 1) α) ∘ word f p 1=p := by
    funext x
    simp [word,Equiv.funUnique,Fin.default_eq_zero]
  have hq0 : (Equiv.funUnique (Fin 1) β) ∘ word f q 1=q := by
    funext x
    simp [word,Equiv.funUnique,Fin.default_eq_zero]
  rw [←cond_equiv_left μ (word f p 1) (word f q 1) (Equiv.funUnique (Fin 1) α),hp0,
    ←cond_equiv_right μ p (word f q 1) (Equiv.funUnique (Fin 1) β),hq0]
omit [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma cond_word_zero (f : Ω → Ω) (p : Ω → α) (q : Ω → β) :
    cond μ (word f p 0) (word f q 0)=0 := by
  have hp : word f p 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  have hq : word f q 0=(fun _ : Ω => (fun i : Fin 0 => Fin.elim0 i)) := by funext x i; exact i.elim0
  simp only [cond,hp,hq,obs_const,sub_self]
lemma cond_word_bound (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (n : ℕ) :
    cond μ (word f p n) (word f q n) ≤ n*cond μ p q := by
  induction n with
  | zero => simp only [cond_word_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    have h := cond_word_subadd μ f hf p q hp hq n 1
    change cond μ (word f p (n+1)) (word f q (n+1))≤
      cond μ (word f p n) (word f q n)+cond μ (word f p 1) (word f q 1) at h
    rw [cond_word_one μ f p q hp hq] at h
    calc
      _ ≤ cond μ (word f p n) (word f q n)+cond μ p q := h
      _ ≤ n*cond μ p q+cond μ p q := add_le_add ih le_rfl
      _ = _ := by push_cast; ring
lemma obs_word_comparison (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) (n : ℕ) :
    obs μ (word f p n) ≤ obs μ (word f q n)+n*cond μ p q := by
  have h := obs_pair_ge_left μ (word f p n) (word f q n)
    (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable q hq n)
  have hc := cond_word_bound μ f hf p q hp hq n
  unfold cond at hc ⊢
  linarith

lemma obs_word_bddBelow (f : Ω → Ω) (hf : Measurable f) (p : Ω → α) (hp : Measurable p) :
    BddBelow (Set.range (fun n : ℕ => obs μ (word f p n)/(n : ℝ))) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (obs_nonneg μ _ (word_measurable f hf p hp n)) (Nat.cast_nonneg n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

noncomputable def rate (f : Ω → Ω) (p : Ω → α) : ℝ :=
  sInf ((fun n : ℕ => obs μ (word f p n)/(n : ℝ)) '' Ici 1)
lemma rate_eq_lim (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    rate μ f p=(obs_word_subadd μ f hf p hp).lim := by
  rw [Subadditive.lim]; rfl
lemma rate_tendsto (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    Tendsto (fun n : ℕ => obs μ (word f p n)/(n : ℝ)) atTop (𝓝 (rate μ f p)) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).tendsto_lim (obs_word_bddBelow μ f hf.measurable p hp)
lemma rate_le_div (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p)
    {n : ℕ} (hn : n≠0) : rate μ f p≤obs μ (word f p n)/(n : ℝ) := by
  rw [rate_eq_lim μ f hf p hp]
  exact (obs_word_subadd μ f hf p hp).lim_le_div (obs_word_bddBelow μ f hf.measurable p hp) hn
lemma rate_nonneg (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    0≤rate μ f p :=
  ge_of_tendsto' (rate_tendsto μ f hf p hp) (fun n => div_nonneg
    (obs_nonneg μ _ (word_measurable f hf.measurable p hp n)) (Nat.cast_nonneg n))
lemma rate_le_obs (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    rate μ f p≤obs μ p := by
  simpa only [Nat.cast_one,div_one,obs_word_one μ f p hp] using rate_le_div μ f hf p hp (n:=1) (by omega)
lemma rate_comparison (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (q : Ω → β)
    (hp : Measurable p) (hq : Measurable q) : rate μ f p≤rate μ f q+cond μ p q := by
  apply le_of_tendsto_of_tendsto (rate_tendsto μ f hf p hp) ((rate_tendsto μ f hf q hq).add_const _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right (obs_word_comparison μ f hf p q hp hq n) hn0.le
  simpa only [add_div,mul_div_cancel_left₀ _ hn0.ne'] using h
lemma ofReal_rate_eq_iInf (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → α) (hp : Measurable p) :
    ENNReal.ofReal (rate μ f p)=⨅ n : ℕ,ENNReal.ofReal (obs μ (word f p (n+1))/((n : ℝ)+1)) := by
  apply le_antisymm
  · apply le_iInf
    intro n
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.cast_add,Nat.cast_one] using (rate_le_div μ f hf p hp (n:=n+1) (by omega))
  · have ht := (ENNReal.tendsto_ofReal (rate_tendsto μ f hf p hp)).comp (tendsto_add_atTop_nat 1)
    apply ge_of_tendsto' ht
    intro n
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (iInf_le (fun n : ℕ => ENNReal.ofReal (obs μ (word f p (n+1))/((n : ℝ)+1))) n)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable (μ : Measure Torus) [IsProbabilityMeasure μ]
lemma blockAtom_eq_fiber {r : ℕ} (f : Torus → Torus) (p : FinitePartition r)
    (n : ℕ) (w : Fin n → Fin (r+1)) : blockAtom f p n w=(Entropy.word f p.val n) ⁻¹' {w} := by
  ext x
  simp only [blockAtom,mem_ofPred_eq,mem_preimage,mem_singleton_iff,Entropy.word,funext_iff]
omit [IsProbabilityMeasure μ] in
lemma blockEntropy_eq_obs {r : ℕ} (f : Torus → Torus) (p : FinitePartition r) (n : ℕ) :
    blockEntropy μ f p n=Entropy.obs μ (Entropy.word f p.val n) := by
  simp only [blockEntropy,Entropy.obs,Entropy.shannon,Entropy.mass,Real.negMulLog,
    blockAtom_eq_fiber,Finset.sum_neg_distrib,neg_mul]
lemma partitionEntropy_eq_ofReal_rate {r : ℕ} (f : Torus → Torus)
    (hf : MeasurePreserving f μ μ) (p : FinitePartition r) :
    partitionEntropy μ f p=ENNReal.ofReal (Entropy.rate μ f p.val) := by
  rw [Entropy.ofReal_rate_eq_iInf μ f hf p.val p.property]
  simp only [partitionEntropy,blockEntropy_eq_obs]
lemma blockEntropy_rate_tendsto {r : ℕ} (f : Torus → Torus)
    (hf : MeasurePreserving f μ μ) (p : FinitePartition r) :
    Tendsto (fun n : ℕ => blockEntropy μ f p n/(n : ℝ)) atTop (𝓝 (Entropy.rate μ f p.val)) := by
  simpa only [blockEntropy_eq_obs] using Entropy.rate_tendsto μ f hf p.val p.property
lemma partitionEntropy_comparison {r s : ℕ} (f : Torus → Torus)
    (hf : MeasurePreserving f μ μ) (p : FinitePartition r) (q : FinitePartition s) :
    partitionEntropy μ f p≤partitionEntropy μ f q+ENNReal.ofReal (Entropy.cond μ p.val q.val) := by
  rw [partitionEntropy_eq_ofReal_rate μ f hf p,partitionEntropy_eq_ofReal_rate μ f hf q]
  have hc := Entropy.cond_nonneg μ p.val q.val p.property q.property
  have hr := Entropy.rate_nonneg μ f hf q.val q.property
  rw [←ENNReal.ofReal_add hr hc]
  exact ENNReal.ofReal_le_ofReal (Entropy.rate_comparison μ f hf p.val q.val p.property q.property)

end StandardMapEntropy

end
end

end OAI
