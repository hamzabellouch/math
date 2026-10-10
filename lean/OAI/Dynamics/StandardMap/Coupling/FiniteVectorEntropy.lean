import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.TypicalWordCodebook

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma cond_vector_subadd [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (N : ℕ) (p : X → Fin N → A) (q : X → Fin N → B)
    (hp : Measurable p) (hq : Measurable q) :
    StandardMapEntropy.Entropy.cond μ p q≤∑ i : Fin N,
      StandardMapEntropy.Entropy.cond μ (fun x => p x i) (fun x => q x i) := by
  induction N with
  | zero =>
    have h1 : p=fun _ => (fun i : Fin 0 => i.elim0 : Fin 0 → A) := by
      funext x i
      exact i.elim0
    have h2 : q=fun _ => (fun i : Fin 0 => i.elim0 : Fin 0 → B) := by
      funext x i
      exact i.elim0
    rw [h1,h2]
    simp [StandardMapEntropy.Entropy.cond,obs_const]
  | succ N ih =>
    let eA : (A×(Fin N → A)) ≃ (Fin (N+1) → A) := Fin.consEquiv (fun _ => A)
    let eB : (B×(Fin N → B)) ≃ (Fin (N+1) → B) := Fin.consEquiv (fun _ => B)
    have h1 : p=eA ∘ (fun x => (p x 0,Fin.tail (p x))) := by
      funext x
      exact (Fin.consEquiv (fun _ => A)).apply_symm_apply (p x) |>.symm
    have h2 : q=eB ∘ (fun x => (q x 0,Fin.tail (q x))) := by
      funext x
      exact (Fin.consEquiv (fun _ => B)).apply_symm_apply (q x) |>.symm
    have hp0 := (measurable_pi_apply 0).comp hp
    have hq0 := (measurable_pi_apply 0).comp hq
    have hpt : Measurable (fun x => Fin.tail (p x)) := Measurable.of_eval
      (fun i => (measurable_pi_apply i.succ).comp hp)
    have hqt : Measurable (fun x => Fin.tail (q x)) := Measurable.of_eval
      (fun i => (measurable_pi_apply i.succ).comp hq)
    have hb := cond_pair_subadd μ (fun x => p x 0) (fun x => q x 0)
      (fun x => Fin.tail (p x)) (fun x => Fin.tail (q x)) hp0 hq0 hpt hqt
    have hi := ih (fun x => Fin.tail (p x)) (fun x => Fin.tail (q x)) hpt hqt
    rw [h1,h2,cond_equiv_left,cond_equiv_right]
    rw [Fin.sum_univ_succ]
    exact hb.trans (add_le_add (le_refl _) hi)

lemma shannon_productVector [MeasurableSpace A] [MeasurableSingletonClass A]
    (N : ℕ) (p : Fin N → A → ℝ) (hs : ∀ i,∑ a,p i a=1) :
    shannon (fun w : Fin N → A => ∏ i,p i (w i))=∑ i,shannon (p i) := by
  induction N with
  | zero => simp [shannon]
  | succ N ih =>
    let e : (A×(Fin N → A)) ≃ (Fin (N+1) → A) := Fin.consEquiv (fun _ => A)
    have he : shannon (fun w : Fin (N+1) → A => ∏ i,p i (w i))=
        shannon (fun aw : A×(Fin N → A) => p 0 aw.1*∏ i,p i.succ (aw.2 i)) := by
      unfold shannon
      rw [←Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro aw _
      congr 1
      simp [e,Fin.prod_univ_succ]
    have hm : (∑ w : Fin N → A,∏ i,p i.succ (w i))=1 :=
      productWeights_sum (fun i : Fin N => p i.succ) (fun i => hs i.succ)
    rw [he,shannon_product_weights (p 0) (fun w : Fin N → A => ∏ i,p i.succ (w i))
      (hs 0) hm,ih _ (fun i => hs i.succ),Fin.sum_univ_succ]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X)

lemma mass_factor_sum [MeasurableSpace A] [MeasurableSingletonClass A]
    [IsProbabilityMeasure μ] [DecidableEq C] (p : X → A) (hp : Measurable p) (c : A → C) (z : C) :
    mass μ (c ∘ p) z=∑ a,if c a=z then mass μ p a else 0 := by
  classical
  have h := sum_mass_factor_mul μ p hp c (fun v => if v=z then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h.symm

lemma cond_eq_channel_average [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B)
    (K : A → B → ℝ) (hK : ∀ a,∑ b,K a b=1)
    (hjoint : ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=mass μ p a*K a b) :
    StandardMapEntropy.Entropy.cond μ q p=∑ a,mass μ p a*shannon (K a) := by
  have hs (a : A) : (∑ b,Real.negMulLog (mass μ p a*K a b))=
      mass μ p a*shannon (K a)+Real.negMulLog (mass μ p a) := by
    change shannon (fun b => mass μ p a*K a b)=_
    simpa only [hK,one_mul] using shannon_scale (K a) (mass μ p a)
  rw [StandardMapEntropy.Entropy.cond,obs_pair_swap μ q p]
  simp only [obs,shannon,Fintype.sum_prod_type,hjoint]
  change (∑ a,∑ b,Real.negMulLog (mass μ p a*K a b))-
    (∑ a,Real.negMulLog (mass μ p a))=_
  simp only [hs,Finset.sum_add_distrib,shannon]
  ring

lemma product_channel_coordinate [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [IsProbabilityMeasure μ]
    (N : ℕ) (p : X → Fin N → A) (q : X → Fin N → B)
    (hp : Measurable p) (hq : Measurable q) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a,∑ b,K i a b=1)
    (hjoint : ∀ v w,mass μ (fun x => (p x,q x)) (v,w)=
      mass μ p v*∏ i,K i (v i) (w i)) (i : Fin N) (a : A) (b : B) :
    mass μ (fun x => (p x i,q x i)) (a,b)=mass μ (fun x => p x i) a*K i a b := by
  classical
  have he := mass_factor_sum μ (fun x => (p x,q x)) (hp.prodMk hq)
    (fun vw : (Fin N → A)×(Fin N → B) => (vw.1 i,vw.2 i)) (a,b)
  change mass μ (fun x => (p x i,q x i)) (a,b)=_ at he
  rw [he]
  simp only [Fintype.sum_prod_type,hjoint,Prod.mk.injEq]
  have hr (v : Fin N → A) :
      (∑ w : Fin N → B,if v i=a ∧ w i=b then mass μ p v*∏ j,K j (v j) (w j) else 0)=
      (if v i=a then mass μ p v else 0)*K i a b := by
    by_cases hv : v i=a
    · simp only [hv,true_and,ite_true]
      have hec := expectation_coordinate (fun j => K j (v j)) (fun j => hK j (v j)) i
        (fun z => if z=b then 1 else 0)
      simp only [finiteExpectation,productWeights,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hec
      calc
        _ = mass μ p v*(∑ w : Fin N → B,if w i=b then ∏ j,K j (v j) (w j) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          split_ifs <;> simp
        _ = _ := by rw [hec,hv]
    · simp only [hv,false_and,ite_false,Finset.sum_const_zero,zero_mul]
  simp only [hr,←Finset.sum_mul]
  have hm := mass_factor_sum μ p hp (fun v : Fin N → A => v i) a
  exact congrArg (fun t : ℝ => t*K i a b) hm.symm

theorem product_channel_entropy_lower [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [IsProbabilityMeasure μ]
    (N : ℕ) (p : X → Fin N → A) (q : X → Fin N → B)
    (hp : Measurable p) (hq : Measurable q) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a,∑ b,K i a b=1)
    (hjoint : ∀ v w,mass μ (fun x => (p x,q x)) (v,w)=
      mass μ p v*∏ i,K i (v i) (w i)) :
    obs μ p+(∑ i : Fin N,(obs μ (fun x => q x i)-obs μ (fun x => p x i)))≤obs μ q := by
  have hfull := cond_eq_channel_average μ p q (fun v w => ∏ i,K i (v i) (w i))
    (fun v => productWeights_sum (fun i => K i (v i)) (fun i => hK i (v i))) hjoint
  have hr : StandardMapEntropy.Entropy.cond μ q p=∑ i : Fin N,
      StandardMapEntropy.Entropy.cond μ (fun x => q x i) (fun x => p x i) := by
    rw [hfull]
    simp_rw [shannon_productVector _ _ (fun i => hK i _),Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [cond_eq_channel_average μ (fun x => p x i) (fun x => q x i) (K i) (hK i)
      (product_channel_coordinate μ N p q hp hq K hK hjoint i)]
    exact sum_mass_factor_mul μ p hp (fun v : Fin N → A => v i) (fun a => shannon (K i a))
  have hsub := cond_vector_subadd μ N p q hp hq
  have hid : obs μ p-obs μ q=StandardMapEntropy.Entropy.cond μ p q-
      StandardMapEntropy.Entropy.cond μ q p := by
    rw [StandardMapEntropy.Entropy.cond,StandardMapEntropy.Entropy.cond,obs_pair_swap μ q p]
    ring
  have hi (i : Fin N) : obs μ (fun x => q x i)-obs μ (fun x => p x i)=
      StandardMapEntropy.Entropy.cond μ (fun x => q x i) (fun x => p x i)-
        StandardMapEntropy.Entropy.cond μ (fun x => p x i) (fun x => q x i) := by
    unfold StandardMapEntropy.Entropy.cond
    rw [obs_pair_swap μ (fun x => q x i) (fun x => p x i)]
    ring
  simp only [hi,Finset.sum_sub_distrib]
  rw [hr] at hid
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSpace B] [Fintype B]

lemma mass_finiteWeightLaw_id [MeasurableSingletonClass A] (P : A → ℝ) (hP : ∀ a,0≤P a) (a : A) :
    mass (finiteWeightLaw P) id a=P a := by
  simp only [mass,preimage_id,finiteWeightLaw_singleton,ENNReal.toReal_ofReal (hP a)]

noncomputable def finiteChannelLaw (N : ℕ) (P : (Fin N → A) → ℝ)
    (K : Fin N → A → B → ℝ) : Measure ((Fin N → A)×(Fin N → B)) :=
  finiteWeightLaw (fun vw => P vw.1*∏ i,K i (vw.1 i) (vw.2 i))

lemma finiteChannelLaw_probability [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (hPs : ∑ v,P v=1) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a b,0≤K i a b) (hKs : ∀ i a,∑ b,K i a b=1) :
    IsProbabilityMeasure (finiteChannelLaw N P K) := by
  apply finiteWeightLaw_probability
  · intro vw
    exact mul_nonneg (hP _) (Finset.prod_nonneg (fun i _ => hK _ _ _))
  · simp only [Fintype.sum_prod_type,←Finset.mul_sum]
    have he (v : Fin N → A) : (∑ w : Fin N → B,∏ i,K i (v i) (w i))=1 :=
      productWeights_sum (fun i => K i (v i)) (fun i => hKs i (v i))
    simp only [he,mul_one,hPs]

lemma finiteChannelLaw_pair_mass [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (K : Fin N → A → B → ℝ) (hK : ∀ i a b,0≤K i a b)
    (v : Fin N → A) (w : Fin N → B) :
    mass (finiteChannelLaw N P K) (fun vw => (vw.1,vw.2)) (v,w)=P v*∏ i,K i (v i) (w i) := by
  exact mass_finiteWeightLaw_id _ (fun vw => mul_nonneg (hP _)
    (Finset.prod_nonneg (fun i _ => hK _ _ _))) (v,w)

lemma finiteChannelLaw_input_mass [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (K : Fin N → A → B → ℝ) (hK : ∀ i a b,0≤K i a b)
    (hKs : ∀ i a,∑ b,K i a b=1) (v : Fin N → A) :
    mass (finiteChannelLaw N P K) Prod.fst v=P v := by
  have : IsFiniteMeasure (finiteChannelLaw N P K) := finiteWeightLaw_finite _
  rw [mass_joint_row _ Prod.fst Prod.snd measurable_fst measurable_snd]
  simp only [finiteChannelLaw_pair_mass N P hP K hK,←Finset.mul_sum]
  have he : (∑ w : Fin N → B,∏ i,K i (v i) (w i))=1 :=
    productWeights_sum (fun i => K i (v i)) (fun i => hKs i (v i))
  rw [he,mul_one]

theorem finiteChannelLaw_entropy [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (N : ℕ) (P : (Fin N → A) → ℝ)
    (hP : ∀ v,0≤P v) (hPs : ∑ v,P v=1) (K : Fin N → A → B → ℝ)
    (hK : ∀ i a b,0≤K i a b) (hKs : ∀ i a,∑ b,K i a b=1) :
    shannon P+(∑ i : Fin N,(obs (finiteChannelLaw N P K) (fun vw => vw.2 i)-
      obs (finiteChannelLaw N P K) (fun vw => vw.1 i)))≤
      obs (finiteChannelLaw N P K) Prod.snd := by
  have := finiteChannelLaw_probability N P hP hPs K hK hKs
  have hh := product_channel_entropy_lower (finiteChannelLaw N P K) N Prod.fst Prod.snd
    measurable_fst measurable_snd K hKs (by
      intro v w
      rw [finiteChannelLaw_pair_mass N P hP K hK,finiteChannelLaw_input_mass N P hP K hK hKs])
  have he : obs (finiteChannelLaw N P K) Prod.fst=shannon P := by
    unfold obs
    congr 1
    funext v
    exact finiteChannelLaw_input_mass N P hP K hK hKs v
  rw [he] at hh
  exact hh
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype A] [Fintype B]

lemma channel_joint_l1 [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b) :
    (∑ ab : A×B,|mass μ (fun x => (p x,r x)) ab-mass ν (fun x => (q x,s x)) ab|)=
      ∑ a,|mass μ p a-mass ν q a| := by
  simp only [Fintype.sum_prod_type,hμ,hν,←sub_mul,abs_mul,abs_of_nonneg (hK _ _),
    ←Finset.mul_sum,hKs,mul_one]

lemma channel_joint_lawClose [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b)
    {δ : ℝ} (hlaw : LawClose (μ.map p) (ν.map q) δ) :
    LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun x => (q x,s x))) (2*δ) := by
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (ν.map q) := inferInstance
  have : IsProbabilityMeasure (μ.map (fun x => (p x,r x))) := inferInstance
  have : IsProbabilityMeasure (ν.map (fun x => (q x,s x))) := inferInstance
  have hmass (a : A) : (μ.map p).real {a}=mass μ p a :=
    map_measureReal_apply hp (measurableSet_singleton a)
  have hmass' (a : A) : (ν.map q).real {a}=mass ν q a :=
    map_measureReal_apply hq (measurableSet_singleton a)
  have hj (ab : A×B) : (μ.map (fun x => (p x,r x))).real {ab}=
      mass μ (fun x => (p x,r x)) ab := map_measureReal_apply (hp.prodMk hr) (measurableSet_singleton ab)
  have hj' (ab : A×B) : (ν.map (fun x => (q x,s x))).real {ab}=
      mass ν (fun x => (q x,s x)) ab := map_measureReal_apply (hq.prodMk hs) (measurableSet_singleton ab)
  have hh := finite_l1_le_two_of_lawClose _ _ hlaw
  simp only [hmass,hmass'] at hh
  apply lawClose_of_finite_l1
  simp only [hj,hj']
  rw [channel_joint_l1 μ ν p r q s K hK hKs hμ hν]
  exact hh

lemma channel_output_lawClose [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b)
    {δ : ℝ} (hlaw : LawClose (μ.map p) (ν.map q) δ) :
    LawClose (μ.map r) (ν.map s) (2*δ) := by
  have hh := (channel_joint_lawClose μ ν p r q s hp hr hq hs K hK hKs hμ hν hlaw).map measurable_snd
  simpa only [Measure.map_map measurable_snd (hp.prodMk hr),
    Measure.map_map measurable_snd (hq.prodMk hs),Function.comp_def] using hh

lemma channel_cost_stability [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (K : A → B → ℝ) (hK : ∀ a b,0≤K a b) (hKs : ∀ a,∑ b,K a b=1)
    (hμ : ∀ a b,mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*K a b)
    (hν : ∀ a b,mass ν (fun x => (q x,s x)) (a,b)=mass ν q a*K a b)
    {δ M : ℝ} (hM : 0≤M) (hlaw : LawClose (μ.map p) (ν.map q) δ)
    (d : A → B → ℝ) (hd : ∀ a b,|d a b|≤M) :
    (MatrixCoupling.observations ν q s hq hs).cost d≤
      (MatrixCoupling.observations μ p r hp hr).cost d+2*δ*M := by
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (ν.map q) := inferInstance
  have hl1 := finite_l1_le_two_of_lawClose _ _ hlaw
  have he (a : A) : (μ.map p).real {a}=mass μ p a := map_measureReal_apply hp (measurableSet_singleton a)
  have he' (a : A) : (ν.map q).real {a}=mass ν q a := map_measureReal_apply hq (measurableSet_singleton a)
  simp only [he,he'] at hl1
  have hdiff : (∑ ab : A×B,(mass ν (fun x => (q x,s x)) ab-mass μ (fun x => (p x,r x)) ab)*d ab.1 ab.2)≤2*δ*M := by
    calc
      _≤∑ ab : A×B,|mass μ (fun x => (p x,r x)) ab-mass ν (fun x => (q x,s x)) ab| * M := by
        apply Finset.sum_le_sum
        intro ab _
        calc
          _≤|(mass ν (fun x => (q x,s x)) ab-mass μ (fun x => (p x,r x)) ab)*d ab.1 ab.2| := le_abs_self _
          _≤_ := by rw [abs_mul,abs_sub_comm]; exact mul_le_mul_of_nonneg_left (hd _ _) (abs_nonneg _)
      _=(∑ a,|mass μ p a-mass ν q a|)*M := by
        rw [←Finset.sum_mul,channel_joint_l1 μ ν p r q s K hK hKs hμ hν]
      _≤_ := mul_le_mul_of_nonneg_right hl1 hM
  simp only [sub_mul,Finset.sum_sub_distrib,Fintype.sum_prod_type] at hdiff
  change (∑ a,∑ b,mass ν (fun x => (q x,s x)) (a,b)*d a b)≤
    (∑ a,∑ b,mass μ (fun x => (p x,r x)) (a,b)*d a b)+2*δ*M
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

noncomputable def recodingKernel (μ : Measure X) [IsProbabilityMeasure μ] (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) : A → B → ℝ := by
  classical
  exact (MatrixCoupling.observations μ r p hr hp).conditionalAssignment

lemma recodingKernel_nonneg (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r) (a : A) (b : B) :
    0≤recodingKernel μ p r hp hr a b := by
  classical
  exact (MatrixCoupling.observations μ r p hr hp).conditionalAssignment_nonneg a b

lemma recodingKernel_sum (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r) (a : A) :
    ∑ b,recodingKernel μ p r hp hr a b=1 := by
  classical
  exact (MatrixCoupling.observations μ r p hr hp).conditionalAssignment_sum a

lemma recodingKernel_joint (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r) (a : A) (b : B) :
    mass μ (fun x => (p x,r x)) (a,b)=mass μ p a*recodingKernel μ p r hp hr a b := by
  classical
  have hh := (MatrixCoupling.observations μ r p hr hp).mul_conditionalAssignment b a
  exact (mass_joint_swap μ p r a b).trans hh.symm

noncomputable def recodingLaw (μ : Measure X) [IsProbabilityMeasure μ] (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) (ν : Measure Y)
    (N : ℕ) (Q : Y → Fin N → A) : Measure ((Fin N → A)×(Fin N → B)) :=
  finiteChannelLaw N (mass ν Q) (fun _ => recodingKernel μ p r hp hr)

lemma recodingLaw_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q) :
    IsProbabilityMeasure (recodingLaw μ p r hp hr ν N Q) := by
  apply finiteChannelLaw_probability N (mass ν Q) (mass_nonneg _ _) (by simpa using mass_sum ν Q hQ)
  · intro i
    exact recodingKernel_nonneg μ p r hp hr
  · intro i
    exact recodingKernel_sum μ p r hp hr

lemma recodingLaw_input_mass (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (v : Fin N → A) :
    mass (recodingLaw μ p r hp hr ν N Q) Prod.fst v=mass ν Q v :=
  finiteChannelLaw_input_mass N (mass ν Q) (mass_nonneg _ _)
    (fun _ => recodingKernel μ p r hp hr) (fun _ => recodingKernel_nonneg μ p r hp hr)
    (fun _ => recodingKernel_sum μ p r hp hr) v

lemma recodingLaw_input_coordinate (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) (a : A) :
    mass (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i) a=mass ν (fun y => Q y i) a := by
  classical
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  have hh := mass_factor_sum (recodingLaw μ p r hp hr ν N Q) Prod.fst measurable_fst
    (fun v : Fin N → A => v i) a
  have hh' := mass_factor_sum ν Q hQ (fun v : Fin N → A => v i) a
  simp only [recodingLaw_input_mass] at hh
  exact hh.trans hh'.symm

lemma recodingLaw_joint_coordinate (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) (a : A) (b : B) :
    mass (recodingLaw μ p r hp hr ν N Q) (fun vw => (vw.1 i,vw.2 i)) (a,b)=
      mass (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i) a*recodingKernel μ p r hp hr a b := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  apply product_channel_coordinate (recodingLaw μ p r hp hr ν N Q) N Prod.fst Prod.snd
    measurable_fst measurable_snd (fun _ => recodingKernel μ p r hp hr)
    (fun _ => recodingKernel_sum μ p r hp hr) _ i a b
  intro v w
  rw [recodingLaw_input_mass]
  exact finiteChannelLaw_pair_mass N (mass ν Q) (mass_nonneg _ _)
    (fun _ => recodingKernel μ p r hp hr) (fun _ => recodingKernel_nonneg μ p r hp hr) v w

lemma recodingLaw_input_law (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) :
    (recodingLaw μ p r hp hr ν N Q).map (fun vw => vw.1 i)=ν.map (fun y => Q y i) := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  apply Measure.ext_of_singleton
  intro a
  have hl : Measurable (fun vw : (Fin N → A)×(Fin N → B) => vw.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hr' : Measurable (fun y => Q y i) := (measurable_pi_apply i).comp hQ
  rw [Measure.map_apply hl (measurableSet_singleton a),Measure.map_apply hr' (measurableSet_singleton a)]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact recodingLaw_input_coordinate μ p r hp hr ν N Q hQ i a

lemma recodingLaw_output_lawClose (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    (i : Fin N) {δ : ℝ} (hlaw : LawClose (μ.map p) (ν.map (fun y => Q y i)) δ) :
    LawClose (μ.map r) ((recodingLaw μ p r hp hr ν N Q).map (fun vw => vw.2 i)) (2*δ) := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  apply channel_output_lawClose μ (recodingLaw μ p r hp hr ν N Q) p r
    (fun vw => vw.1 i) (fun vw => vw.2 i) hp hr
    ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd)
    (recodingKernel μ p r hp hr) (recodingKernel_nonneg μ p r hp hr)
    (recodingKernel_sum μ p r hp hr) (recodingKernel_joint μ p r hp hr)
    (recodingLaw_joint_coordinate μ p r hp hr ν N Q hQ i)
  rw [recodingLaw_input_law μ p r hp hr ν N Q hQ i]
  exact hlaw
end HyperbolicCoding

end

end OAI
