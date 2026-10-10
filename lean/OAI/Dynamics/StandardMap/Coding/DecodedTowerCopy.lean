import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Towers.ScaledFiniteCoupling
import OAI.Dynamics.StandardMap.Coding.TypicalDecodableCoupling

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

noncomputable def prefixNameCost {k t : ℕ} (F : C → A)
    (a : Fin k → C) (b : Fin (k+t) → A) : ℝ :=
  ∑ i : Fin k,symbolCost (F (a i)) (b (Fin.castAdd t i))

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] in
lemma nameCost_le_prefixNameCost {k t : ℕ} (F : C → A)
    (a : Fin (k+t) → C) (b : Fin (k+t) → A) :
    nameCost (F ∘ a) b ≤ prefixNameCost F (fun i => a (Fin.castAdd t i)) b + t := by
  rw [nameCost,Fin.sum_univ_add]
  unfold prefixNameCost
  apply add_le_add_right
  calc
    (∑ i : Fin t,symbolCost (F (a (Fin.natAdd k i))) (b (Fin.natAdd k i))) ≤
        ∑ _ : Fin t,(1 : ℝ) := Finset.sum_le_sum (fun _ _ => symbolCost_le_one _ _)
    _ = (t : ℝ) := by simp

theorem realize_prefix_tower_coupling (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) (k t : ℕ)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → C) (hp : Measurable p) (F : C → A) (v : (Fin (k+t) → A) → ℝ)
    (R : MatrixCoupling (mass (μ.restrict U) (word e p k)) v) :
    ∃ q : X → A,Measurable q ∧
      (∀ a b,mass (μ.restrict U) (fun x => (word e p k x,word e q (k+t) x)) (a,b)=R.weight a b) ∧
      (∀ b,mass (μ.restrict U) (word e q (k+t)) b=v b) ∧
      μ.real {x | F (p x)≠q x}≤R.cost (prefixNameCost F)+(t : ℝ)*μ.real U ∧
      ∀ x,x∉⋃ i : Fin (k+t),(e^[i.val]) '' U → q x=F (p x) := by
  have hF : Measurable F := measurable_of_countable F
  have hpw := word_measurable e e.measurable p hp k
  obtain ⟨B,hB,hR⟩ := realize_finite_coupling_finite (μ.restrict U) (word e p k) hpw v R
  let q := paintTower e U (k+t) B (F ∘ p)
  have hq : Measurable q := measurable_paintTower e hU (k+t) hd hB (hF.comp hp)
  have hj (a : Fin k → C) (b : Fin (k+t) → A) :
      mass (μ.restrict U) (fun x => (word e p k x,word e q (k+t) x)) (a,b)=R.weight a b := by
    rw [←hR a b]
    unfold mass
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_restrict_mem hU] with x hx
    change ((word e p k x,word e q (k+t) x)=(a,b)) = ((word e p k x,B x)=(a,b))
    rw [show word e q (k+t) x=B x from paintTower_word e U (k+t) hd B (F ∘ p) hx]
  refine ⟨q,hq,hj,?_,?_,fun x hx => paintTower_off e U (k+t) B (F ∘ p) hx⟩
  · intro b
    rw [mass_joint_col (μ.restrict U) (word e p k) (word e q (k+t)) hpw
      (word_measurable e e.measurable q hq (k+t))]
    simp_rw [hj]
    exact R.col b
  · change μ.real {x | (F ∘ p) x≠q x}≤_
    rw [paintTower_repaint_integral μ e he hU (k+t) hd hB (hF.comp hp)]
    have hprefix : Integrable (fun x => prefixNameCost F (word e p k x) (B x)) (μ.restrict U) :=
      integrable_finite_observation (μ.restrict U) (fun x => (word e p k x,B x))
        (hpw.prodMk hB) (fun ab => prefixNameCost F ab.1 ab.2)
    have hfull : Integrable (fun x => nameCost (word e (F ∘ p) (k+t) x) (B x)) (μ.restrict U) :=
      integrable_finite_observation (μ.restrict U) (fun x => (word e (F ∘ p) (k+t) x,B x))
        ((word_measurable e e.measurable (F ∘ p) (hF.comp hp) (k+t)).prodMk hB)
        (fun ab => nameCost ab.1 ab.2)
    have hb := integral_mono hfull (hprefix.add (integrable_const (t : ℝ)))
      (fun x => nameCost_le_prefixNameCost F (word e p (k+t) x) (B x))
    dsimp only [Pi.add_apply] at hb
    rw [integral_add hprefix (integrable_const (t : ℝ)), integral_const] at hb
    rw [integral_cost_of_realization (μ.restrict U) (word e p k) hpw B hB R hR (prefixNameCost F)] at hb
    simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hb

omit [StandardBorelSpace X] [Nonempty A] in
lemma prefix_tower_decoder_error (μ : Measure X) [IsFiniteMeasure μ]
    (e : X ≃ᵐ X) {U : Set X} (_hU : MeasurableSet U) (k t : ℕ)
    (p : X → C) (q : X → A) (hp : Measurable p) (hq : Measurable q)
    {v : (Fin (k+t) → A) → ℝ} (R : MatrixCoupling (mass (μ.restrict U) (word e p k)) v)
    (hR : ∀ a b,mass (μ.restrict U) (fun x => (word e p k x,word e q (k+t) x)) (a,b)=R.weight a b)
    (D : (Fin (k+t) → A) → (Fin k → C)) :
    μ.real (U∩{x | D (word e q (k+t) x)≠word e p k x})=
      R.cost (fun a b => symbolCost a (D b)) := by
  have hpw := word_measurable e e.measurable p hp k
  have hqw := word_measurable e e.measurable q hq (k+t)
  have hD : Measurable D := measurable_of_countable D
  have hh := finite_symbolCost_integral (μ.restrict U) (word e p k) (D ∘ word e q (k+t)) hpw (hD.comp hqw)
  have heq : (μ.restrict U).real {x | word e p k x≠(D ∘ word e q (k+t)) x}=
      μ.real (U∩{x | D (word e q (k+t) x)≠word e p k x}) := by
    have hm : MeasurableSet {x | word e p k x≠(D ∘ word e q (k+t)) x} :=
      (measurableSet_eq_fun hpw (hD.comp hqw)).compl
    rw [Measure.real,Measure.real,Measure.restrict_apply hm,inter_comm]
    congr 2
    ext x
    simp only [mem_inter_iff,mem_ofPred_eq,Function.comp_apply,ne_comm]
  rw [heq] at hh
  exact hh.symm.trans (integral_cost_of_realization (μ.restrict U) (word e p k) hpw
    (word e q (k+t)) hqw R hR (fun a b => symbolCost a (D b)))

omit [StandardBorelSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma ae_observation_of_zero_bad_mass (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → C) (Q : C → Prop) (hbad : ∀ c,¬Q c → mass μ p c=0) :
    ∀ᵐ x ∂μ,Q (p x) := by
  have hh (c : C) : ∀ᵐ x ∂μ,p x=c → Q c := by
    by_cases hc : Q c
    · exact ae_of_all _ (fun _ _ => hc)
    · apply ae_iff.mpr
      have hz : μ (p ⁻¹' {c})=0 := by
        have ht := hbad c hc
        change (μ (p ⁻¹' {c})).toReal=0 at ht
        exact ((ENNReal.toReal_eq_zero_iff _).mp ht).resolve_right (measure_ne_top _ _)
      convert hz using 1
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq,mem_preimage,mem_singleton_iff,hc,imp_false,not_not]
  filter_upwards [ae_all_iff.mpr hh] with x hx
  exact hx (p x) rfl

theorem decoded_prefix_tower_copy (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    {U : Set X} (hU : MeasurableSet U) {k t r : ℕ} (hn : 0<k+t) (hr : r<k+t)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → C) (hp : Measurable p) (F : C → A) (v : (Fin (k+t) → A) → ℝ)
    (R : MatrixCoupling (mass (μ.restrict U) (word e p k)) v)
    (zero one : A) (h01 : zero≠one)
    (hmark : ∀ w,¬Marker.MarkedBlock hr zero one w → v w=0)
    (D : (Fin (k+t) → A) → (Fin k → C)) (c₀ : C) :
    ∃ q : X → A,Measurable q ∧
      (∀ b,mass (μ.restrict U) (word e q (k+t)) b=v b) ∧
      μ.real {x | F (p x)≠q x}≤R.cost (prefixNameCost F)+(t : ℝ)*μ.real U ∧
      μ.real {x | Marker.decodeWindow hn hr zero one (extendPrefixDecoder D c₀)
        (word e q (2*(k+t)) (integerIterate e (-((k+t : ℕ) : ℤ)) x))≠p x} ≤
        μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
        (k+t : ℕ)*R.cost (fun a b => symbolCost a (D b))+(t : ℝ)*μ.real U := by
  obtain ⟨q,hq,hjoint,hbase,hpaint,_hoff⟩ :=
    realize_prefix_tower_coupling μ e he hU k t hd p hp F v R
  refine ⟨q,hq,hbase,hpaint,?_⟩
  have hmarked : ∀ᵐ b ∂μ.restrict U,Marker.MarkedBlock hr zero one (word e q (k+t) b) :=
    ae_observation_of_zero_bad_mass (μ.restrict U) (word e q (k+t))
      (Marker.MarkedBlock hr zero one) (fun w hw => (hbase w).trans (hmark w hw))
  have hb := marked_tower_prefix_decoder_error μ e he p q hn hr zero one h01 D c₀ hU hmarked
  rw [prefix_tower_decoder_error μ e hU k t p q hp hq R hjoint D] at hb
  exact hb

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A C : Type*} {k t r : ℕ}

lemma prefixNameCost_nonneg (F : C → A) (a : Fin k → C) (b : Fin (k+t) → A) :
    0 ≤ prefixNameCost F a b :=
  Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _)

lemma prefixNameCost_le_length (F : C → A) (a : Fin k → C) (b : Fin (k+t) → A) :
    prefixNameCost F a b ≤ (k : ℝ) := by
  calc
    _ ≤ ∑ _ : Fin k,(1 : ℝ) := Finset.sum_le_sum (fun _ _ => symbolCost_le_one _ _)
    _ = _ := by simp

lemma prefixNameCost_modify (F : C → A) (a : Fin k → C) (b d : Fin (k+t) → A) :
    prefixNameCost F a d ≤ prefixNameCost F a b+nameCost b d := by
  have htri : prefixNameCost F a d ≤ prefixNameCost F a b+
      ∑ i : Fin k,symbolCost (b (Fin.castAdd t i)) (d (Fin.castAdd t i)) := by
    unfold prefixNameCost
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun _ _ => symbolCost_triangle _ _ _)
  apply htri.trans
  apply add_le_add_right
  rw [nameCost,Fin.sum_univ_add]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _))

noncomputable def normalizedPrefixCost {k t : ℕ} (F : C → A)
    (a : Fin k → C) (b : Fin (k+t) → A) : ℝ := prefixNameCost F a b/(k+t : ℕ)

lemma normalizedPrefixCost_nonneg (F : C → A) (a : Fin k → C) (b : Fin (k+t) → A) :
    0 ≤ normalizedPrefixCost F a b := div_nonneg (prefixNameCost_nonneg F a b) (Nat.cast_nonneg _)

lemma normalizedPrefixCost_le_one (hn : 0<k+t) (F : C → A)
    (a : Fin k → C) (b : Fin (k+t) → A) : normalizedPrefixCost F a b ≤ 1 := by
  apply (div_le_one (Nat.cast_pos.mpr hn)).mpr
  exact (prefixNameCost_le_length F a b).trans (by exact_mod_cast Nat.le_add_right k t)

lemma normalizedPrefixCost_markWord [Fintype A] (F : C → A) (a : Fin k → C) (b : Fin (k+t) → A)
    (zero one : A) : normalizedPrefixCost F a (Marker.markWord r zero one b) ≤
      normalizedPrefixCost F a b + (Marker.reserved (k+t) r).card/(k+t : ℕ) := by
  classical
  rw [normalizedPrefixCost,normalizedPrefixCost,←add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (prefixNameCost_modify F a b (Marker.markWord r zero one b)).trans
    (add_le_add_right (Marker.markWord_cost zero one b) _)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A C : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem synchronized_codebook_producer (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ)
    (htotal : ∀ m : ℕ, 0 < m → Ergodic (f^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0<weightEntropy β) (hrate : rate μ f p≤weightEntropy β)
    (zero one : A) {ε : ℝ} (hε : 0<ε) :
    ∃ K r m : ℕ,0<K ∧ 0<r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0<n ∧ r<n*K*m+n*m ∧
      ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
      ((Marker.reserved (n*K*m+n*m) r).card : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
      ∀ R : MatrixCoupling (mass μ (word f p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∃ (D : (Fin (n*K*m+n*m) → A) → (Fin (n*K*m) → C))
          (H : MatrixCoupling (mass μ (word f p (n*K*m)))
            (pushWeight (productWordWeight β (n*K*m+n*m)) (Marker.markWord r zero one))),
          H.cost (fun a b => symbolCost a (D b))<ε ∧
          H.cost (normalizedPrefixCost F)<R.cost (normalizedPrefixCost F)+2*ε := by
  let θ : ℝ := min (ε/16) (1/16)
  have hθ : 0<θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ<1/4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθeps : θ≤ε/16 := min_le_left _ _
  obtain ⟨K,r,hK,hr,δ,hδ,_hsuffix,hparams⟩ := exists_entropy_slack_parameters
    (Fintype.card A) (weightEntropy β) ε (by exact_mod_cast Fintype.card_pos) hβentropy hε
  obtain ⟨m,hm,hsource⟩ := entropy_rate_codebook μ f hf htotal p hp hδ
  have hKgo : Tendsto (fun n : ℕ => n*K) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hK) tendsto_id
  have hNgo : Tendsto (fun n : ℕ => n*K*m+n*m) atTop atTop :=
    tendsto_atTop_mono (fun n => (Nat.le_mul_of_pos_right n hm).trans (Nat.le_add_left _ _)) tendsto_id
  have hM : 0<(1-4*θ)*MatrixCoupling.decodingThreshold (ε/2) :=
    mul_pos (by linarith) (MatrixCoupling.decodingThreshold_pos (by positivity))
  have hsource' := hKgo.eventually (hsource θ hθ)
  have htarget := hNgo.eventually (eventually_iid_typical_words β hβ hβsum hδ hθ)
  have hpar := hparams m hm ((1-4*θ)*MatrixCoupling.decodingThreshold (ε/2)) hM
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hsource',htarget,hpar] with n hnS hnT hnP
  obtain ⟨S,hScard,hSbad⟩ := hnS
  obtain ⟨T,hT,hTbad⟩ := hnT
  obtain ⟨hn,hrn,htail,hreserve,hsize⟩ := hnP
  have hnn : 0<n*K*m+n*m := lt_trans hr hrn
  refine ⟨hn,hrn,htail,hreserve,?_⟩
  intro R
  have hsum : (∑ a,mass μ (word f p (n*K*m)) a)=1 := by
    rw [mass_sum μ _ (word_measurable f hf.measurable p hp _)]; simp
  have hScard' : (S.card : ℝ)≤Real.exp ((n*K*m : ℕ)*(weightEntropy β+δ)) :=
    hScard.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add_left hrate δ) (Nat.cast_nonneg _)))
  have hSmall : (S.card : ℝ)*(2*(Fintype.card A : ℝ)^(Marker.reserved (n*K*m+n*m) r).card*
      Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(weightEntropy β-δ))) ≤
      (1-4*θ)*MatrixCoupling.decodingThreshold (ε/2) := by
    apply le_trans (mul_le_mul_of_nonneg_right hScard' (by positivity))
    convert hsize.le using 1
    ring
  obtain ⟨D,H,hD,hH⟩ := MatrixCoupling.marked_word_decodable_coupling β hβ hβsum
    (by positivity : 0<ε/2) hθ.le hθsmall R hsum S T
    (mass_codebook_lower μ _ (word_measurable f hf.measurable p hp _) S hSbad).le
    (L:=((n*K*m+n*m : ℕ) : ℝ)*(weightEntropy β-δ))
    (by simpa only [neg_mul] using hT) hTbad.le zero one (by simpa only [neg_mul] using hSmall)
    (normalizedPrefixCost F) (normalizedPrefixCost_nonneg F) (normalizedPrefixCost_le_one hnn F)
    (((Marker.reserved (n*K*m+n*m) r).card : ℝ)/(n*K*m+n*m : ℕ))
    (fun a b => normalizedPrefixCost_markWord F a b zero one)
  exact ⟨D,H,by linarith,by linarith⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

theorem unsanitize_tower (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    (n : ℕ) (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) (v : (Fin n → A) → ℝ)
    (hv : ∀ w,0≤v w) (hs : ∑ w,v w=1)
    (g : (Fin n → A) → (Fin n → A)) (K : ℝ) (hK : ∀ w,nameCost (g w) w≤K)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=μ.real U*pushWeight v g w) :
    ∃ q : X → A,Measurable q ∧
      (∀ w,mass (μ.restrict U) (word e q n) w=μ.real U*v w) ∧
      μ.real {x | p x≠q x}≤K*μ.real U := by
  classical
  let R : MatrixCoupling (mass (μ.restrict U) (word e p n)) (fun w => μ.real U*v w) := {
    weight := fun a b => if g b=a then μ.real U*v b else 0
    nonneg := fun a b => by split_ifs; exact mul_nonneg measureReal_nonneg (hv b); exact le_rfl
    row := fun a => by
      rw [hbase]
      simp only [pushWeight,Finset.mul_sum,mul_ite,mul_zero]
    col := fun b => by simp }
  obtain ⟨q,hq,_hjoint,hqbase,hcost,_hoff⟩ := realize_tower_coupling μ e he hU n hd p hp _ R
  refine ⟨q,hq,hqbase,?_⟩
  rw [hcost]
  change (∑ a,∑ b,(if g b=a then μ.real U*v b else 0)*nameCost a b)≤_
  rw [Finset.sum_comm]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  calc
    _ ≤ ∑ b,μ.real U*v b*K := Finset.sum_le_sum (fun b _ =>
      mul_le_mul_of_nonneg_left (hK b) (mul_nonneg measureReal_nonneg (hv b)))
    _ = K*μ.real U := by rw [←Finset.sum_mul,←Finset.mul_sum,hs,mul_one,mul_comm]

theorem unsanitize_marked_tower (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    (n r : ℕ) (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → A) (hp : Measurable p) (v : (Fin n → A) → ℝ)
    (hv : ∀ w,0≤v w) (hs : ∑ w,v w=1) (zero one : A)
    (hbase : ∀ w,mass (μ.restrict U) (word e p n) w=
      μ.real U*pushWeight v (Marker.markWord r zero one) w) :
    ∃ q : X → A,Measurable q ∧
      (∀ w,mass (μ.restrict U) (word e q n) w=μ.real U*v w) ∧
      μ.real {x | p x≠q x}≤(Marker.reserved n r).card*μ.real U := by
  apply unsanitize_tower μ e he hU n hd p hp v hv hs (Marker.markWord r zero one) _ _ hbase
  intro w
  rw [nameCost_comm]
  exact Marker.markWord_cost zero one w

omit [StandardBorelSpace X] [Nonempty A] in
lemma word_disagreement_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p q : X → A)
    (hp : Measurable p) (hq : Measurable q) (m : ℕ) :
    μ.real {x | word f p m x≠word f q m x}≤(m : ℝ)*μ.real {x | p x≠q x} := by
  have hset : {x | word f p m x≠word f q m x}=
      ⋃ i : Fin m,(f^[i.val]) ⁻¹' {x | p x≠q x} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion,mem_preimage]
    constructor
    · intro hx
      by_contra hn
      apply hx
      funext i
      have hh : ∀ i : Fin m,p (f^[i.val] x)=q (f^[i.val] x) := by simpa using hn
      exact hh i
    · rintro ⟨i,hi⟩ h
      exact hi (congrFun h i)
  rw [hset]
  apply (measureReal_iUnion_fintype_le _).trans
  have hE : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
  have he (i : Fin m) : μ.real ((f^[i.val]) ⁻¹' {x | p x≠q x})=μ.real {x | p x≠q x} := by
    rw [Measure.real,Measure.real,(hf.iterate i.val).measure_preimage hE.nullMeasurableSet]
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,le_refl]

omit [StandardBorelSpace X] [Nonempty A] in
lemma word_lawClose_of_repaint (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p q : X → A)
    (hp : Measurable p) (hq : Measurable q) (m : ℕ) :
    LawClose (μ.map (word f p m)) (μ.map (word f q m)) ((m : ℝ)*μ.real {x | p x≠q x}) := by
  intro D hD
  exact (law_distance_le_disagreement μ (word_measurable f hf.measurable p hp m)
    (word_measurable f hf.measurable q hq m) hD).trans (word_disagreement_le μ f hf p q hp hq m)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [Nonempty C]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C] [Nonempty C] in
lemma normalizedPrefixCost_left_triangle {k t : ℕ} (hn : 0<k+t) (F : C → A)
    (a b : Fin k → C) (c : Fin (k+t) → A) :
    normalizedPrefixCost F a c ≤ symbolCost a b+normalizedPrefixCost F b c := by
  classical
  by_cases hab : a=b
  · subst b; simp [symbolCost]
  · have h1 := normalizedPrefixCost_le_one hn F a c
    have h0 := normalizedPrefixCost_nonneg F b c
    simp only [symbolCost,ite_eq_right hab]
    linarith

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma tower_real_mass_le_one (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    (n : ℕ) (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    (n : ℝ)*μ.real U≤1 := by
  have hh := congrArg ENNReal.toReal (tower_measure μ e he hU n hd)
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hh
  have hi := measureReal_mono (μ:=μ) (subset_univ (⋃ i : Fin n,(e^[i.val]) '' U))
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,hh] using hi

omit [StandardBorelSpace X] [TopologicalSpace X] [SecondCountableTopology X]
  [OpensMeasurableSpace X] in
lemma tower_suffix_mass_le (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {k t : ℕ} (hn : 0<k+t)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    (t : ℝ)*μ.real U≤(t : ℝ)/(k+t : ℕ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr
  have hh := mul_le_mul_of_nonneg_left (tower_real_mass_le_one μ e he hU (k+t) hd) (Nat.cast_nonneg t)
  nlinarith

omit [Nonempty C] in
theorem lift_decoded_prefix_transport (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    {k t r : ℕ} (hn : 0<k+t) (hr : r<k+t)
    (p : X → C) (hp : Measurable p) (F : C → A)
    (v : (Fin (k+t) → A) → ℝ)
    (R : MatrixCoupling (mass μ (word e p k)) v)
    (zero one : A) (h01 : zero≠one)
    (hmark : ∀ w,¬Marker.MarkedBlock hr zero one w → v w=0)
    (D : (Fin (k+t) → A) → (Fin k → C)) (c₀ : C)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (U : Set X) (q : X → A),MeasurableSet U ∧ 0<μ U ∧ Measurable q ∧
      Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ<ε ∧
      (∀ b,mass (μ.restrict U) (word e q (k+t)) b=μ.real U*v b) ∧
      μ.real {x | F (p x)≠q x}≤R.cost (normalizedPrefixCost F)+ε+(t : ℝ)/(k+t : ℕ) ∧
      μ.real {x | Marker.decodeWindow hn hr zero one (extendPrefixDecoder D c₀)
        (word e q (2*(k+t)) (integerIterate e (-((k+t : ℕ) : ℤ)) x))≠p x} <
        2*ε+R.cost (fun a b => symbolCost a (D b))+(t : ℝ)/(k+t : ℕ) := by
  have hw := word_measurable e e.measurable p hp k
  obtain ⟨U,hU,hUp,hd,hcover,hclose⟩ := exists_unbiased_rohlin_tower μ e he hn (word e p k) hw hε
  let ν := (μ U)⁻¹ • μ.restrict U
  have : IsProbabilityMeasure ν := normalized_restriction_probability μ hUp
  obtain ⟨S,hS⟩ := coupling_of_observation_lawClose ν μ (word e p k) (word e p k) hw hw hclose
  have hP := S.comp_cost_le R symbolCost (normalizedPrefixCost F) (normalizedPrefixCost F)
    (normalizedPrefixCost_left_triangle hn F)
  have hD := S.comp_cost_le R symbolCost (fun a b => symbolCost a (D b))
    (fun a b => symbolCost a (D b)) (fun a b c => symbolCost_triangle a b (D c))
  have hc : 0≤μ.real U := measureReal_nonneg
  let W := (S.comp R).scale (μ.real U) hc
  let W' : MatrixCoupling (mass (μ.restrict U) (word e p k)) (fun b => μ.real U*v b) := {
    weight := W.weight
    nonneg := W.nonneg
    row := fun a => (W.row a).trans (normalize_mass_cancel μ hUp (word e p k) a)
    col := W.col }
  have hWP : W'.cost (prefixNameCost F)≤μ.real U*((k+t : ℕ)*(ε+R.cost (normalizedPrefixCost F))) := by
    change W.cost (prefixNameCost F)≤_
    rw [show prefixNameCost F=(fun a b => ((k+t : ℕ) : ℝ)*normalizedPrefixCost F a b) by
      funext a b
      unfold normalizedPrefixCost
      exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')).symm]
    rw [MatrixCoupling.cost_mul,MatrixCoupling.scale_cost]
    have hh := mul_le_mul_of_nonneg_left (le_trans hP (add_le_add hS le_rfl)) hc
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (k+t))
    nlinarith
  have hWD : W'.cost (fun a b => symbolCost a (D b))≤
      μ.real U*(ε+R.cost (fun a b => symbolCost a (D b))) := by
    change W.cost _≤_
    rw [MatrixCoupling.scale_cost]
    exact mul_le_mul_of_nonneg_left (hD.trans (add_le_add hS le_rfl)) hc
  obtain ⟨q,hq,hbase,hpaint,hdecode⟩ := decoded_prefix_tower_copy μ e he.toMeasurePreserving
    hU hn hr hd p hp F _ W' zero one h01 (fun w hw => by rw [hmark w hw,mul_zero]) D c₀
  have hmass := tower_real_mass_le_one μ e he.toMeasurePreserving hU (k+t) hd
  have htail := tower_suffix_mass_le μ e he.toMeasurePreserving hU hn hd
  have hP0 := R.cost_nonneg (normalizedPrefixCost F) (normalizedPrefixCost_nonneg F)
  have hD0 := R.cost_nonneg (fun a b => symbolCost a (D b)) (fun _ _ => symbolCost_nonneg _ _)
  refine ⟨U,q,hU,hUp,hq,hd,hcover,hbase,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hmass (show 0≤ε+R.cost (normalizedPrefixCost F) by linarith)
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hmass
      (show 0≤ε+R.cost (fun a b => symbolCost a (D b)) by linarith)
    have hn0 : (0 : ℝ)≤(k+t : ℕ) := Nat.cast_nonneg _
    have hbound := mul_le_mul_of_nonneg_left hWD hn0
    nlinarith

end HyperbolicCoding

end

end OAI
