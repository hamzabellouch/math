import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.ChunkNameCost

namespace OAI

section
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] in
lemma mass_factor_le (p : X → A) (g : A → B) (a : A) :
    mass μ p a≤ mass μ (g ∘ p) (g a) := by
  unfold mass
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono
  intro x hx
  exact congrArg g hx

noncomputable def refinementCopyWeights (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B) : ℝ :=
  mass μ p a*mass μ (fun x => (c (p x),q x)) (c a,b)/mass μ (c ∘ p) (c a)

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [IsProbabilityMeasure μ] in
lemma refinementCopyWeights_nonneg (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B) :
    0≤refinementCopyWeights μ p q c a b :=
  div_nonneg (mul_nonneg (mass_nonneg _ _ _) (mass_nonneg _ _ _)) (mass_nonneg _ _ _)

omit [Fintype C] in
lemma refinementCopyWeights_row (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) (a : A) :
    (∑ b,refinementCopyWeights μ p q c a b)=mass μ p a := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  by_cases hz : mass μ (c ∘ p) (c a)=0
  · have hp0 : mass μ p a=0 := le_antisymm ((mass_factor_le μ p c a).trans (le_of_eq hz)) (mass_nonneg _ _ _)
    simp only [refinementCopyWeights,hp0,zero_mul,zero_div,Finset.sum_const_zero]
  · have hrow : (∑ b,mass μ (fun x => (c (p x),q x)) (c a,b))=mass μ (c ∘ p) (c a) :=
      (mass_joint_row μ (c ∘ p) q hc hq (c a)).symm
    simp only [refinementCopyWeights,←Finset.sum_div,←Finset.mul_sum,hrow,mul_div_cancel_right₀ _ hz]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] in
lemma refinementCopyWeights_support (p : X → A) (q : X → B) (c : A → C) (a : A) (b : B)
    (h : mass μ (fun x => (p x,q x)) (a,b)≠0) : refinementCopyWeights μ p q c a b≠0 := by
  have hu : 0 < mass μ (fun x => (p x,q x)) (a,b) := lt_of_le_of_ne (mass_nonneg _ _ _) (Ne.symm h)
  have hp : 0 < mass μ p a := hu.trans_le (mass_factor_le μ (fun x => (p x,q x)) Prod.fst (a,b))
  have hcb : 0 < mass μ (fun x => (c (p x),q x)) (c a,b) :=
    hu.trans_le (mass_factor_le μ (fun x => (p x,q x)) (fun ab => (c ab.1,ab.2)) (a,b))
  have hc : 0 < mass μ (c ∘ p) (c a) := hp.trans_le (mass_factor_le μ p c a)
  exact ne_of_gt (div_pos (mul_pos hp hcb) hc)

theorem refinement_relativeInformation (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) :
    relativeInformation (fun ab : A×B => mass μ (fun x => (p x,q x)) ab)
      (fun ab => refinementCopyWeights μ p q c ab.1 ab.2)=
        cond μ q (c ∘ p)-cond μ q p := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  let pq : X → A×B := fun x => (p x,q x)
  let cq : X → C×B := fun x => (c (p x),q x)
  have hpq : Measurable pq := hp.prodMk hq
  have hcq : Measurable cq := hc.prodMk hq
  unfold relativeInformation
  rw [sum_mass_mul_integral μ pq hpq]
  have he : (fun x => Real.log (mass μ pq (pq x))-
      Real.log (refinementCopyWeights μ p q c (p x) (q x)))=ᵐ[μ]
      (fun x => -information μ pq x+information μ p x+information μ cq x-information μ (c ∘ p) x) := by
    filter_upwards [ae_mass_positive μ p,ae_mass_positive μ cq,ae_mass_positive μ (c ∘ p)] with x hx hcx hcpx
    dsimp only [refinementCopyWeights,information,pq,cq,Function.comp_apply] at *
    rw [Real.log_div (mul_pos hx hcx).ne' hcpx.ne',Real.log_mul hx.ne' hcx.ne']
    ring
  rw [integral_congr_ae he]
  rw [integral_sub (f:=fun x => -information μ pq x+information μ p x+information μ cq x)
    (g:=fun x => information μ (c ∘ p) x) (((information_integrable μ pq hpq).neg.add (information_integrable μ p hp)).add
    (information_integrable μ cq hcq)) (information_integrable μ (c ∘ p) hc)]
  rw [integral_add (f:=fun x => -information μ pq x+information μ p x) (g:=fun x => information μ cq x) ((information_integrable μ pq hpq).neg.add (information_integrable μ p hp))
      (information_integrable μ cq hcq),integral_add (f:=fun x => -information μ pq x) (g:=fun x => information μ p x) (information_integrable μ pq hpq).neg
      (information_integrable μ p hp),integral_neg]
  simp only [integral_information μ pq hpq,integral_information μ p hp,
    integral_information μ cq hcq,integral_information μ (c ∘ p) hc]
  unfold cond
  rw [obs_pair_swap μ q (c ∘ p),obs_pair_swap μ q p]
  dsimp only [pq,cq,Function.comp_apply]
  ring

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma finite_l1_le_two_of_lawClose {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,|μ.real {a}-ν.real {a}|)≤2*ε := by
  have he (a : A) : |μ.real {a}-ν.real {a}|=
      max (μ.real {a}-ν.real {a}) 0+max (ν.real {a}-μ.real {a}) 0 := by
    rcases le_total (μ.real {a}) (ν.real {a}) with ha|ha
    · rw [abs_of_nonpos (sub_nonpos.mpr ha),max_eq_right (sub_nonpos.mpr ha),max_eq_left (sub_nonneg.mpr ha)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr ha),max_eq_left (sub_nonneg.mpr ha),max_eq_right (sub_nonpos.mpr ha)]
      ring
  simp_rw [he,Finset.sum_add_distrib]
  linarith [positive_mass_difference_le μ ν h,positive_mass_difference_le ν μ h.symm]

lemma lawClose_of_finite_l1 {ε : ℝ} (h : (∑ a,|μ.real {a}-ν.real {a}|)≤ε) : LawClose μ ν ε := by
  classical
  intro D _hD
  let S : Finset A := Finset.univ.filter (fun a => a∈D)
  have he : (S : Set A)=D := by ext a; simp [S]
  have hμ : μ.real D=∑ a∈S,μ.real {a} := by rw [←he]; exact (sum_measureReal_singleton S).symm
  have hν : ν.real D=∑ a∈S,ν.real {a} := by rw [←he]; exact (sum_measureReal_singleton S).symm
  rw [hμ,hν,←Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ h)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => abs_nonneg _)

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped BigOperators ENNReal
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma sum_mass_factor_mul (p : X → A) (hp : Measurable p) (c : A → C) (F : C → ℝ) :
    (∑ a,mass μ p a*F (c a))=∑ d,mass μ (c ∘ p) d*F d := by
  calc
    _ = ∫ x, (F ∘ c) (p x) ∂μ := sum_mass_mul_integral μ p hp (F ∘ c)
    _ = _ := (sum_mass_mul_integral μ (c ∘ p)
      ((measurable_of_countable c).comp hp) F).symm

omit [MeasurableSingletonClass B] in
lemma refinement_distance_eq (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (_ : Measurable q) :
    (∑ a,∑ b,|refinementCopyWeights μ p q c a b-mass μ p a*mass μ q b|)=
      ∑ d,∑ b,|mass μ (fun x => (c (p x),q x)) (d,b)-mass μ (c ∘ p) d*mass μ q b| := by
  have he (a : A) (b : B) : |refinementCopyWeights μ p q c a b-mass μ p a*mass μ q b|=
      mass μ p a*|mass μ (fun x => (c (p x),q x)) (c a,b)/mass μ (c ∘ p) (c a)-mass μ q b| := by
    unfold refinementCopyWeights
    rw [mul_div_assoc,←mul_sub,abs_mul,abs_of_nonneg (mass_nonneg μ p a)]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hec (b : B) := sum_mass_factor_mul μ p hp c
    (fun d => |mass μ (fun x => (c (p x),q x)) (d,b)/mass μ (c ∘ p) d-mass μ q b|)
  simp_rw [hec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro b _
  let u := mass μ (c ∘ p) d
  let v := mass μ (fun x => (c (p x),q x)) (d,b)
  have hu : 0≤u := mass_nonneg _ _ _
  have hv : 0≤v := mass_nonneg _ _ _
  have hvu : v≤u := mass_factor_le μ (fun x => (c (p x),q x)) Prod.fst (d,b)
  change u*|v/u-mass μ q b|=|v-u*mass μ q b|
  by_cases hu0 : u=0
  · have hv0 : v=0 := le_antisymm (hvu.trans (le_of_eq hu0)) hv
    simp [hu0,hv0]
  · calc
      _ = |u*(v/u-mass μ q b)| := by rw [abs_mul,abs_of_nonneg hu]
      _ = _ := by congr 1; rw [mul_sub,mul_div_cancel₀ _ hu0]

theorem lawClose_of_coarse_independence (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose (μ.map (fun x => (c (p x),q x)))
      ((μ.map (c ∘ p)).prod (μ.map q)) ε)
    (hdef : 4*(cond μ q (c ∘ p)-cond μ q p)≤δ^2) :
    LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) (δ+2*ε) := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (μ.map q) := inferInstance
  have : IsProbabilityMeasure (μ.map (c ∘ p)) := inferInstance
  have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := inferInstance
  have : IsProbabilityMeasure (μ.map (fun x => (c (p x),q x))) := inferInstance
  let u : A×B → ℝ := fun ab => mass μ (fun x => (p x,q x)) ab
  let v : A×B → ℝ := fun ab => refinementCopyWeights μ p q c ab.1 ab.2
  have hu1 : (∑ ab,u ab)=1 := by simp only [u,mass_sum μ _ (hp.prodMk hq),measure_univ,ENNReal.toReal_one]
  have hv1 : (∑ ab,v ab)=1 := by
    rw [Fintype.sum_prod_type]
    simp only [v,refinementCopyWeights_row μ p q c hp hq,mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
  have hpen := finite_pinsker_sq u v (fun _ => mass_nonneg _ _ _)
    (fun ab => refinementCopyWeights_nonneg μ p q c ab.1 ab.2) hu1 hv1
    (fun ab => refinementCopyWeights_support μ p q c ab.1 ab.2)
  have hinfo : relativeInformation u v=cond μ q (c ∘ p)-cond μ q p :=
    refinement_relativeInformation μ p q c hp hq
  rw [hinfo] at hpen
  have hUV : (∑ ab,|u ab-v ab|)≤δ := by nlinarith [hpen.trans hdef]
  have hmap (a : A) (b : B) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u (a,b) :=
    map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
  have hmapC (d : C) (b : B) : (μ.map (fun x => (c (p x),q x))).real {(d,b)}=
      mass μ (fun x => (c (p x),q x)) (d,b) :=
    map_measureReal_apply (hc.prodMk hq) (measurableSet_singleton (d,b))
  have hprod (a : A) (b : B) : ((μ.map p).prod (μ.map q)).real {(a,b)}=mass μ p a*mass μ q b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hprodC (d : C) (b : B) : ((μ.map (c ∘ p)).prod (μ.map q)).real {(d,b)}=
      mass μ (c ∘ p) d*mass μ q b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hc (measurableSet_singleton d),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hcoarse := finite_l1_le_two_of_lawClose _ _ hclose
  rw [Fintype.sum_prod_type] at hcoarse
  simp only [hmapC,hprodC] at hcoarse
  have hVP : (∑ ab : A×B,|v ab-mass μ p ab.1*mass μ q ab.2|)≤2*ε := by
    rw [Fintype.sum_prod_type]
    exact (refinement_distance_eq μ p q c hp hq).le.trans hcoarse
  apply lawClose_of_finite_l1
  rw [Fintype.sum_prod_type]
  simp only [hmap,hprod]
  rw [Fintype.sum_prod_type] at hUV hVP
  calc
    _≤∑ a,∑ b,(|u (a,b)-v (a,b)|+|v (a,b)-mass μ p a*mass μ q b|) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => abs_sub_le _ _ _))
    _=(∑ a,∑ b,|u (a,b)-v (a,b)|)+(∑ a,∑ b,|v (a,b)-mass μ p a*mass μ q b|) := by simp only [Finset.sum_add_distrib]
    _≤δ+2*ε := add_le_add hUV hVP

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped Topology ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem uniform_remote_from_finite_entropy
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose
      (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p L (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hdef : 4*(cond μ (word f p (k+g))
      (fun x => word f p L (f^[k+g] x))-(k+g : ℕ)*rate μ f p)≤δ^2) :
    ∀ M : ℕ,L≤M → LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) (δ+2*ε) := by
  intro M hLM
  let rM : X → (Fin M → A) := fun x => word f p M (f^[k+g] x)
  let c : (Fin M → A) → (Fin L → A) := fun w i => w (Fin.castLE hLM i)
  let d : (Fin (k+g) → A) → (Fin k → A) := fun w i => w (Fin.castLE (Nat.le_add_right k g) i)
  have hrM : Measurable rM := (word_measurable f hf.measurable p hp M).comp (hf.measurable.iterate (k+g))
  have hc : c ∘ rM=(fun x => word f p L (f^[k+g] x)) := by funext x i; rfl
  have hd : d ∘ word f p (k+g)=word f p k := by funext x i; rfl
  have hdata := conditional_defect_data_processing μ rM (word f p (k+g)) c d
    hrM (word_measurable f hf.measurable p hp (k+g))
  rw [hd,hc] at hdata
  have hlower := rate_mul_le_cond_future μ f hf p hp (k+g) M
  have hdef' : 4*(cond μ (word f p k) (c ∘ rM)-cond μ (word f p k) rM)≤δ^2 := by
    rw [hc]
    change (k+g : ℕ)*rate μ f p≤cond μ (word f p (k+g)) rM at hlower
    linarith
  apply lawClose_of_coarse_independence μ rM (word f p k) c hrM
    (word_measurable f hf.measurable p hp k) hδ
  · exact hclose
  · exact hdef'

theorem eventually_finite_entropy_test
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ L : ℕ in atTop,4*(cond μ (word f p n)
      (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p)<δ^2 := by
  have ht := ((cond_future_tendsto μ f hf p hp n).sub_const ((n : ℝ)*rate μ f p)).const_mul 4
  have he : (4 : ℝ)*((n : ℝ)*rate μ f p-(n : ℝ)*rate μ f p)=0 := by ring
  rw [he] at ht
  exact ht.eventually (gt_mem_nhds (sq_pos_of_pos hδ))

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [MeasurableSpace B]

lemma independence_law_stable (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : X → B) (p' : Y → A) (q' : Y → B)
    (hp : Measurable p) (hq : Measurable q) (hp' : Measurable p') (hq' : Measurable q')
    {ε δ : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) (ν.map (fun y => (p' y,q' y))) δ)
    (hi : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (ν.map (fun y => (p' y,q' y))) ((ν.map p').prod (ν.map q')) (ε+3*δ) := by
  have hleft := h.map measurable_fst
  have hright := h.map measurable_snd
  rw [Measure.map_map measurable_fst (hp.prodMk hq),Measure.map_map measurable_fst (hp'.prodMk hq')] at hleft
  rw [Measure.map_map measurable_snd (hp.prodMk hq),Measure.map_map measurable_snd (hp'.prodMk hq')] at hright
  change LawClose (μ.map p) (ν.map p') δ at hleft
  change LawClose (μ.map q) (ν.map q') δ at hright
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (μ.map q) := inferInstance
  have : IsProbabilityMeasure (ν.map p') := inferInstance
  have : IsProbabilityMeasure (ν.map q') := inferInstance
  convert h.symm.triangle (hi.triangle (hleft.prod hright)) using 1; ring

end HyperbolicCoding

namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped ENNReal Topology
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem finite_entropy_test_open (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (n L : ℕ) {r : ℝ}
    (hr : cond μ (word f p n) (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p<r) :
    ∃ δ : ℝ,0<δ ∧ ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν)
      (T : Y → Y) (_ : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
      LawClose (μ.map (word f p (n+L))) (ν.map (word T q (n+L))) δ →
      rate μ f p-δ≤rate ν T q →
      cond ν (word T q n) (fun y => word T q L (T^[n] y))-(n : ℝ)*rate ν T q<r := by
  let D := cond μ (word f p n) (fun x => word f p L (f^[n] x))-(n : ℝ)*rate μ f p
  let γ := (r-D)/(2*((n : ℝ)+2))
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hγ : 0<γ := div_pos (sub_pos.mpr hr) (by positivity)
  obtain ⟨δW,hδW,hW⟩ := obs_continuity_in_law (Y:=Y) μ (word f p (n+L))
    (word_measurable f hf.measurable p hp (n+L)) hγ
  obtain ⟨δL,hδL,hL⟩ := obs_continuity_in_law (Y:=Y) μ (word f p L)
    (word_measurable f hf.measurable p hp L) hγ
  let δ := min γ (min δW δL)
  have hδ : 0<δ := lt_min hγ (lt_min hδW hδL)
  refine ⟨δ,hδ,?_⟩
  intro ν hν T hT q hq hclose hrate
  let : IsProbabilityMeasure ν := hν
  have hW' := hW ν (word T q (n+L)) (word_measurable T hT.measurable q hq (n+L))
    (hclose.mono ((min_le_right γ (min δW δL)).trans (min_le_left δW δL)))
  let c : (Fin (n+L) → A) → (Fin L → A) := fun w i => w (Fin.castLE (Nat.le_add_left L n) i)
  have hshort := hclose.map (measurable_of_countable c)
  rw [Measure.map_map (measurable_of_countable c) (word_measurable f hf.measurable p hp (n+L)),
    Measure.map_map (measurable_of_countable c) (word_measurable T hT.measurable q hq (n+L))] at hshort
  change LawClose (μ.map (word f p L)) (ν.map (word T q L)) δ at hshort
  have hL' := hL ν (word T q L) (word_measurable T hT.measurable q hq L)
    (hshort.mono ((min_le_right γ (min δW δL)).trans (min_le_right δW δL)))
  have hδγ : δ≤γ := min_le_left _ _
  have hmargin : ((n : ℝ)+2)*γ=(r-D)/2 := by dsimp [γ]; field_simp
  have hmul := mul_le_mul_of_nonneg_left (show rate μ f p-γ≤rate ν T q by linarith) hn
  obtain ⟨hWlo,hWhi⟩ := abs_lt.mp hW'
  obtain ⟨hLlo,hLhi⟩ := abs_lt.mp hL'
  rw [cond_word_future_eq ν T hT q hq]
  have hD : D=obs μ (word f p (n+L))-obs μ (word f p L)-(n : ℝ)*rate μ f p := by
    dsimp [D]
    rw [cond_word_future_eq μ f hf p hp]
  nlinarith

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter HyperbolicCoding
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem all_remote_from_finite_entropy
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ε δ : ℝ} (hδ : 0≤δ)
    (hclose : LawClose
      (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p L (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hdef : 4*(cond μ (word f p (k+g))
      (fun x => word f p L (f^[k+g] x))-(k+g : ℕ)*rate μ f p)≤δ^2) :
    ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) (δ+2*ε) := by
  intro M
  by_cases hLM : L≤M
  · exact uniform_remote_from_finite_entropy μ f hf p hp k g L hδ hclose hdef M hLM
  · have hML : M≤L := by omega
    let c : (Fin L → A) → (Fin M → A) := fun w i => w (Fin.castLE hML i)
    have h := lawClose_pair_factor_left μ (fun x => word f p L (f^[k+g] x))
      (word f p k) c ((word_measurable f hf.measurable p hp L).comp (hf.measurable.iterate (k+g)))
      (word_measurable f hf.measurable p hp k) (measurable_of_countable c) hclose
    have hε : 0≤ε := hclose.nonneg
    exact h.mono (by linarith)

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal Topology BigOperators

lemma lawClose_prefix {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) (f : X → X) (T : Y → Y)
    (hf : Measurable f) (hT : Measurable T) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) {m n : ℕ} (hmn : m≤n) {δ : ℝ}
    (h : LawClose (μ.map (word f p n)) (ν.map (word T q n)) δ) :
    LawClose (μ.map (word f p m)) (ν.map (word T q m)) δ := by
  let c : (Fin n → A) → (Fin m → A) := fun w i => w (Fin.castLE hmn i)
  have hc : Measurable c := measurable_of_countable c
  have hh := h.map hc
  rw [Measure.map_map hc (word_measurable f hf p hp n),
    Measure.map_map hc (word_measurable T hT q hq n)] at hh
  exact hh

lemma lawClose_remote_of_word {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) (f : X → X) (T : Y → Y)
    (hf : Measurable f) (hT : Measurable T) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (k g L : ℕ) {δ : ℝ}
    (h : LawClose (μ.map (word f p ((k+g)+L))) (ν.map (word T q ((k+g)+L))) δ) :
    LawClose (μ.map (fun x => (word f p L (f^[k+g] x),word f p k x)))
      (ν.map (fun x => (word T q L (T^[k+g] x),word T q k x))) δ := by
  let c : (Fin ((k+g)+L) → A) → ((Fin L → A)×(Fin k → A)) :=
    fun w => (fun i => w ⟨i.val+(k+g),by omega⟩,fun i => w ⟨i.val,by omega⟩)
  have hc : Measurable c := measurable_of_countable c
  have hh := h.map hc
  rw [Measure.map_map hc (word_measurable f hf p hp _),
    Measure.map_map hc (word_measurable T hT q hq _)] at hh
  have he (x : X) : c (word f p ((k+g)+L) x)=(word f p L (f^[k+g] x),word f p k x) := by
    apply Prod.ext
    · funext i
      exact congrArg p (Function.iterate_add_apply f i.val (k+g) x)
    · rfl
  have he' (y : Y) : c (word T q ((k+g)+L) y)=(word T q L (T^[k+g] y),word T q k y) := by
    apply Prod.ext
    · funext i
      exact congrArg q (Function.iterate_add_apply T i.val (k+g) y)
    · rfl
  simpa only [Function.comp_def,he,he'] using hh

theorem weakBernoulli_finite_determination {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) {η : ℝ} (hη : 0<η) :
    ∃ m s : ℕ,0<s ∧ ∃ δ : ℝ,0<δ ∧
      ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν) (_ : NullSingletonClass ν)
        (T : Y → Y) (_ : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
        LawClose (μ.map (word e p m)) (ν.map (word T q m)) δ →
        rate μ e p-δ≤rate ν T q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e p (n*s))) (mass ν (word T q (n*s))),
          R.cost nameCost≤η*(n*s : ℕ) := by
  let ε : ℝ := η/100
  have hε : 0<ε := div_pos hη (by norm_num)
  obtain ⟨g,hg⟩ := weakBernoulli_forward_blocks μ e he p hp hwb hε
  obtain ⟨k,hk⟩ := exists_nat_gt ((g : ℝ)/ε+1)
  have hkpos : 0<k := by
    have hg0 : 0≤(g : ℝ)/ε := div_nonneg (Nat.cast_nonneg g) hε.le
    have hkR : 0<(k : ℝ) := by linarith
    exact_mod_cast hkR
  have hkg : (g : ℝ)≤ε*(k : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (show (g : ℝ)/ε<(k : ℝ) by linarith)
    nlinarith
  obtain ⟨L,hL⟩ := (eventually_finite_entropy_test μ e he p hp (k+g) hε).exists
  obtain ⟨δ₀,hδ₀,hopen⟩ := finite_entropy_test_open (Y:=Y) μ e he p hp (k+g) L
    (r:=ε^2/4) (by linarith)
  let δ := min ε δ₀
  have hδ : 0<δ := lt_min hε hδ₀
  refine ⟨(k+g)+L,k+g,by omega,δ,hδ,?_⟩
  intro ν hν hnonatomic T hT q hq hclose hrate n
  let : IsProbabilityMeasure ν := hν
  let : NullSingletonClass ν := hnonatomic
  have hdε : δ≤ε := min_le_left _ _
  have hd₀ : δ≤δ₀ := min_le_right _ _
  have hd := hopen ν hν T hT q hq (hclose.mono hd₀) (by linarith)
  have hj := lawClose_remote_of_word μ ν e T he.measurable hT.measurable p q hp hq k g L hclose
  have hfinite := independence_law_stable μ ν
    (fun x => word e p L (e^[k+g] x)) (word e p k)
    (fun y => word T q L (T^[k+g] y)) (word T q k)
    ((word_measurable e he.measurable p hp L).comp (he.measurable.iterate _))
    (word_measurable e he.measurable p hp k)
    ((word_measurable T hT.measurable q hq L).comp (hT.measurable.iterate _))
    (word_measurable T hT.measurable q hq k) hj (hg k L)
  have hremoteQ := all_remote_from_finite_entropy ν T hT q hq k g L hε.le hfinite
    (show 4*(cond ν (word T q (k+g)) (fun y => word T q L (T^[k+g] y))-
      (k+g : ℕ)*rate ν T q)≤ε^2 by linarith)
  have hshort := lawClose_prefix μ ν e T he.measurable hT.measurable p q hp hq
    (show k≤(k+g)+L by omega) hclose
  obtain ⟨R,hR⟩ := full_word_transport μ ν e he p hp T hT q hq k g (hg k) hremoteQ hshort n
  refine ⟨R,hR.trans ?_⟩
  have hb : (k : ℝ)*(ε+δ+(ε+2*(ε+3*δ)))+(g : ℝ)≤η*(k+g : ℕ) := by
    have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
    have hg0 : 0≤(g : ℝ) := Nat.cast_nonneg g
    have hsmall : ε+δ+(ε+2*(ε+3*δ))≤11*ε := by linarith
    have hh := mul_le_mul_of_nonneg_left hsmall hk0
    have hηε : η=100*ε := by dsimp [ε]; ring
    push_cast
    rw [hηε]
    nlinarith [mul_nonneg hε.le hk0,mul_nonneg hε.le hg0]
  have hn := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
  push_cast at hn ⊢
  nlinarith

end HyperbolicCoding

end
end

end OAI
