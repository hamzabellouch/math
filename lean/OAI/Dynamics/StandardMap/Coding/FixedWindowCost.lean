import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.ActualFiniteRecodingBounds

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {A B C : Type*} {k t R : ℕ}

def blockWindow (b : Fin (k+t) → A) (i : Fin (k-2*R)) : Fin (2*R+1) → A :=
  fun j => b ⟨i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
def blockCenter (a : Fin k → C) (i : Fin (k-2*R)) : C :=
  a ⟨i.val+R,by have := i.isLt; omega⟩

noncomputable def decoderNameCost (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : ℝ :=
  ∑ i : Fin (k-2*R),symbolCost (H (blockCenter a i)) (D (blockWindow b i))

noncomputable def fixedWindowCost (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A) : ℝ :=
  (prefixNameCost F a b+decoderNameCost H D a b)/(2*(k+t : ℕ))

lemma decoderNameCost_nonneg (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : 0≤decoderNameCost H D a b :=
  Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _)
lemma decoderNameCost_le_length (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : decoderNameCost H D a b≤(k-2*R : ℕ) := by
  calc
    _≤∑ _ : Fin (k-2*R),(1 : ℝ) := Finset.sum_le_sum (fun _ _ => symbolCost_le_one _ _)
    _=_ := by simp
lemma fixedWindowCost_nonneg (F : C → A) (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b : Fin (k+t) → A) : 0≤fixedWindowCost F H D a b :=
  div_nonneg (add_nonneg (prefixNameCost_nonneg F a b) (decoderNameCost_nonneg H D a b)) (by positivity)
lemma fixedWindowCost_le_one (hn : 0<k+t) (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A) :
    fixedWindowCost F H D a b≤1 := by
  apply (div_le_one (by positivity : (0 : ℝ)<2*(k+t : ℕ))).mpr
  have h₁ := prefixNameCost_le_length F a b
  have h₂ := decoderNameCost_le_length H D a b
  have h₃ : ((k-2*R : ℕ) : ℝ)≤(k : ℝ) := by exact_mod_cast Nat.sub_le k (2*R)
  push_cast
  linarith

lemma symbolCost_factor_le (F : C → B) (a b : C) : symbolCost (F a) (F b)≤ symbolCost a b := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · simpa only [symbolCost,ite_eq_right h] using symbolCost_le_one (F a) (F b)

lemma symbolCost_function_le_sum {ι : Type*} [Fintype ι] (a b : ι → A) :
    symbolCost a b≤∑ i,symbolCost (a i) (b i) := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hh := Finset.single_le_sum (fun i _ => symbolCost_nonneg (a i) (b i)) (Finset.mem_univ i)
    simpa only [symbolCost,ite_eq_right h,ite_eq_right hi] using hh

lemma sum_blockWindow_cost_le (b d : Fin (k+t) → A) :
    (∑ i : Fin (k-2*R),nameCost (blockWindow b i) (blockWindow d i))≤(2*R+1 : ℕ)*nameCost b d := by
  classical
  unfold nameCost
  rw [Finset.sum_comm]
  calc
    _≤∑ _ : Fin (2*R+1),∑ j : Fin (k+t),symbolCost (b j) (d j) := by
      apply Finset.sum_le_sum
      intro j _
      let f : Fin (k-2*R) → Fin (k+t) := fun i => ⟨i.val+j.val,by have:=i.isLt; have:=j.isLt; omega⟩
      have hf : Function.Injective f := by intro i i' h; have := congrArg Fin.val h; apply Fin.ext; dsimp [f] at this; omega
      calc
        _=(∑ z ∈ Finset.univ.image f,symbolCost (b z) (d z)) := (Finset.sum_image (fun i hi i' hi' h => hf h)).symm
        _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => symbolCost_nonneg (b i) (d i))
    _=_ := by simp

lemma decoderNameCost_modify (H : C → B) (D : (Fin (2*R+1) → A) → B)
    (a : Fin k → C) (b d : Fin (k+t) → A) :
    decoderNameCost H D a d≤decoderNameCost H D a b+(2*R+1 : ℕ)*nameCost b d := by
  have hi (i : Fin (k-2*R)) := symbolCost_triangle (H (blockCenter a i)) (D (blockWindow b i)) (D (blockWindow d i))
  have hj (i : Fin (k-2*R)) := (symbolCost_factor_le D (blockWindow b i) (blockWindow d i)).trans
    (symbolCost_function_le_sum (blockWindow b i) (blockWindow d i))
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hi i |>.trans (add_le_add_right (hj i) _))
  rw [Finset.sum_add_distrib] at hh
  exact hh.trans (add_le_add_right (sum_blockWindow_cost_le b d) _)

lemma fixedWindowCost_markWord [Fintype A] (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A)
    (r : ℕ) (zero one : A) :
    fixedWindowCost F H D a (Marker.markWord r zero one b)≤fixedWindowCost F H D a b+
      ((2*R+2 : ℕ) : ℝ)*(Marker.reserved (k+t) r).card/(2*(k+t : ℕ)) := by
  classical
  have hp := prefixNameCost_modify F a b (Marker.markWord r zero one b)
  have hd := decoderNameCost_modify H D a b (Marker.markWord r zero one b)
  have hm := Marker.markWord_cost (r:=r) zero one b
  unfold fixedWindowCost
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast at *
  nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B C : Type*} {k t R : ℕ}

lemma finite_sum_injective_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (g : κ → ℝ) (hg : ∀ j,0≤g j) :
    (∑ i,g (f i))≤∑ j,g j := by
  classical
  calc
    _=(∑ j∈Finset.univ.image f,g j) := (Finset.sum_image (fun i hi i' hi' h => hf h)).symm
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hg i)

lemma fixedWindowCost_factor_triangle (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → C) (d : Fin (k+t) → A) :
    fixedWindowCost F H D a d≤normalizedPrefixCost id a b+
      fixedWindowCost F H D (fun i => b (Fin.castAdd t i)) d := by
  let b₀ : Fin k → C := fun i => b (Fin.castAdd t i)
  have hp : prefixNameCost F a d≤prefixNameCost id a b+prefixNameCost F b₀ d := by
    unfold prefixNameCost
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact (symbolCost_triangle _ (F (b₀ i)) _).trans
      (add_le_add_left (symbolCost_factor_le F (a i) (b₀ i)) _)
  have hd : decoderNameCost H D a d≤prefixNameCost id a b+decoderNameCost H D b₀ d := by
    have hh : decoderNameCost H D a d≤
        (∑ i : Fin (k-2*R),symbolCost (blockCenter a i) (blockCenter b₀ i))+decoderNameCost H D b₀ d := by
      unfold decoderNameCost
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      exact (symbolCost_triangle _ (H (blockCenter b₀ i)) _).trans
        (add_le_add_left (symbolCost_factor_le H (blockCenter a i) (blockCenter b₀ i)) _)
    apply hh.trans
    apply add_le_add_left
    let f : Fin (k-2*R) → Fin k := fun i => ⟨i.val+R,by have := i.isLt; omega⟩
    have hf : Function.Injective f := by
      intro i j h
      have hh := congrArg Fin.val h
      apply Fin.ext
      dsimp [f] at hh
      omega
    exact finite_sum_injective_le f hf (fun i => symbolCost (a i) (b₀ i)) (fun _ => symbolCost_nonneg _ _)
  unfold fixedWindowCost normalizedPrefixCost
  have hn0 : (0 : ℝ)≤(k+t : ℕ) := Nat.cast_nonneg _
  by_cases hn : k+t=0
  · simp [hn]
  · have hnpos : (0 : ℝ)<(k+t : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(k+t : ℕ))).mpr
    have heq : (prefixNameCost id a b/(k+t : ℕ)+
        (prefixNameCost F b₀ d+decoderNameCost H D b₀ d)/(2*(k+t : ℕ)))*(2*(k+t : ℕ))=
        2*prefixNameCost id a b+(prefixNameCost F b₀ d+decoderNameCost H D b₀ d) := by field_simp
    change prefixNameCost F a d+decoderNameCost H D a d≤_
    rw [heq]
    linarith

variable [MeasurableSpace A]

lemma graph_window_word [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    (_decoder : (Fin (2*R+1) → A) → B) (y : ℤ → A) (i : Fin (k-2*R)) :
    centeredWindow R (iidShift^[i.val+R] y)=blockWindow (word iidShift (fun y : ℤ → A => y 0) (k+t) y) i := by
  funext j
  simp only [centeredWindow,iidShift_iterate,blockWindow,iid_word_eq]
  congr 1
  omega

variable [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma graph_fixedWindowCost_zero (D : (Fin (2*R+1) → A) → B) (y : ℤ → A) :
    fixedWindowCost (k:=k) (t:=t) Prod.fst Prod.snd D
      (word iidShift (fun w : ℤ → A => (w 0,D (centeredWindow R w))) k y)
      (word iidShift (fun w : ℤ → A => w 0) (k+t) y)=0 := by
  have hp : prefixNameCost Prod.fst
      (word iidShift (fun w : ℤ → A => (w 0,D (centeredWindow R w))) k y)
      (word iidShift (fun w : ℤ → A => w 0) (k+t) y)=0 := by simp [prefixNameCost,word,symbolCost]
  have hd : decoderNameCost Prod.snd D
      (word iidShift (fun w : ℤ → A => (w 0,D (centeredWindow R w))) k y)
      (word iidShift (fun w : ℤ → A => w 0) (k+t) y)=0 := by
    unfold decoderNameCost
    apply Finset.sum_eq_zero
    intro i _
    dsimp only [blockCenter,word,Prod.snd]
    rw [graph_window_word D y i,symbolCost_self]
  simp only [fixedWindowCost,hp,hd,add_zero,zero_div]

theorem lift_joint_graph_transport {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X → X) (he : Measurable e)
    (p : X → A×B) (hp : Measurable p)
    (ν : Measure (ℤ → A)) [IsProbabilityMeasure ν]
    (D : (Fin (2*R+1) → A) → B)
    (S : MatrixCoupling (mass μ (word e p (k+t)))
      (mass ν (word iidShift (fun y : ℤ → A => (y 0,D (centeredWindow R y))) (k+t)))) :
    ∃ T : MatrixCoupling (mass μ (word e p k)) (mass ν (word iidShift (fun y : ℤ → A => y 0) (k+t))),
      T.cost (fixedWindowCost Prod.fst Prod.snd D)≤S.cost nameCost/(k+t : ℕ) := by
  classical
  obtain ⟨P,hP⟩ := lift_prefix_transport (k:=k) (t:=t) μ e he p hp id S
  let g : (ℤ → A) → A×B := fun y => (y 0,D (centeredWindow R y))
  have hg : Measurable g := (measurable_pi_apply 0).prodMk ((measurable_of_countable D).comp (measurable_centeredWindow R))
  let Q := MatrixCoupling.observations ν (word iidShift g (k+t))
    (word iidShift (fun y : ℤ → A => y 0) (k+t))
    (word_measurable iidShift iidShift.measurable g hg _)
    (word_measurable iidShift iidShift.measurable _ (measurable_pi_apply 0) _)
  let c := fun (a : Fin (k+t) → A×B) (b : Fin (k+t) → A) =>
    fixedWindowCost Prod.fst Prod.snd D (fun i : Fin k => a (Fin.castAdd t i)) b
  have hQ : Q.cost c=0 := by
    rw [MatrixCoupling.observations_cost]
    have hzero (y : ℤ → A) : c (word iidShift g (k+t) y) (word iidShift (fun y : ℤ → A => y 0) (k+t) y)=0 :=
      graph_fixedWindowCost_zero D y
    simp only [hzero,integral_zero]
  refine ⟨P.comp Q,?_⟩
  have hh := P.comp_cost_le Q (normalizedPrefixCost id) c (fixedWindowCost Prod.fst Prod.snd D)
    (fixedWindowCost_factor_triangle Prod.fst Prod.snd D)
  rw [hQ,add_zero] at hh
  exact hh.trans hP
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem fixed_window_fd_graph (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0<weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α)
    (happrox : ∀ ε : ℝ,0<ε → ∃ r : X → A×B,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | (p x,α x)≠r x}<ε) {η : ℝ} (hη : 0<η) :
    ∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,∃ s : ℕ,0<s ∧
      ∀ n : ℕ,∃ W : MatrixCoupling (mass μ (word e (fun x => (p x,α x)) (n*s)))
        (mass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β))
          (word iidShift (fun y : ℤ → A => (y 0,D (centeredWindow R y))) (n*s))),
        W.cost nameCost≤η*(n*s : ℕ) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  obtain ⟨m,s,hs,δ,hδ,hfd⟩ := weakBernoulli_limit_finite_determination (Y:=ℤ → A)
    μ e he.toMeasurePreserving (fun x => (p x,α x)) (hp.prodMk hα) happrox hη
  obtain ⟨R,D,hLaw,hRate⟩ := relative_iid_window_graph μ e he p hp β hβ hβsum hβentropy H hcode α hα m hδ
  refine ⟨R,D,s,hs,?_⟩
  apply hfd _ inferInstance iidShift (iidShift_preserving _) _
    ((measurable_pi_apply 0).prodMk ((measurable_of_countable D).comp (measurable_centeredWindow R))) hLaw
  simp only [Function.comp_apply]
  rw [hRate]
  have hh := H.upper (fun x => (p x,α x)) (hp.prodMk hα)
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A C : Type*} [MeasurableSpace X]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C]

theorem synchronized_cost_producer [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ)
    (htotal : ∀ m : ℕ, 0 < m → Ergodic (f^[m]) μ)
    (p : X → C) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0<weightEntropy β) (hrate : rate μ f p≤weightEntropy β)
    (zero one : A) {ε : ℝ} (hε : 0<ε) :
    ∃ K r m : ℕ,0<K ∧ 0<r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0<n ∧ r<n*K*m+n*m ∧
      ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
      ((Marker.reserved (n*K*m+n*m) r).card : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
      ∀ R : MatrixCoupling (mass μ (word f p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∀ (c : (Fin (n*K*m) → C) → (Fin (n*K*m+n*m) → A) → ℝ),
        (∀ a b,0≤c a b) → (∀ a b,c a b≤1) →
        ∀ (d : ℝ), (∀ a b,c a (Marker.markWord r zero one b)≤c a b+d) →
        ∃ (D : (Fin (n*K*m+n*m) → A) → (Fin (n*K*m) → C))
          (H : MatrixCoupling (mass μ (word f p (n*K*m)))
            (pushWeight (productWordWeight β (n*K*m+n*m)) (Marker.markWord r zero one))),
          H.cost (fun a b => symbolCost a (D b))<ε ∧
          H.cost c<R.cost c+ε+d := by
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
  intro R c hc0 hc1 d hd
  have hsum : (∑ a,mass μ (word f p (n*K*m)) a)=1 := by
    rw [mass_sum μ _ (word_measurable f hf.measurable p hp _)]; simp
  have hScard' : (S.card : ℝ)≤Real.exp ((n*K*m : ℕ)*(weightEntropy β+δ)) :=
    hScard.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add_left hrate δ) (Nat.cast_nonneg _)))
  have hSmall : (S.card : ℝ)*(2*(Fintype.card A : ℝ)^(Marker.reserved (n*K*m+n*m) r).card*
      Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(weightEntropy β-δ))) ≤
      (1-4*θ)*MatrixCoupling.decodingThreshold (ε/2) := by
    apply le_trans (mul_le_mul_of_nonneg_right hScard' (by positivity))
    convert hsize.le using 1; ring
  obtain ⟨D,H,hD,hH⟩ := MatrixCoupling.marked_word_decodable_coupling β hβ hβsum
    (by positivity : 0<ε/2) hθ.le hθsmall R hsum S T
    (mass_codebook_lower μ _ (word_measurable f hf.measurable p hp _) S hSbad).le
    (L:=((n*K*m+n*m : ℕ) : ℝ)*(weightEntropy β-δ))
    (by simpa only [neg_mul] using hT) hTbad.le zero one (by simpa only [neg_mul] using hSmall)
    c hc0 hc1 d hd
  exact ⟨D,H,by linarith,by linarith⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A : Type*} [MeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma tower_error_integral [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U) (m : ℕ)
    (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    μ.real {x | p x≠q x}≤μ.real (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+
      ∫ b in U,∑ i : Fin m,symbolCost (p (e^[i.val] b)) (q (e^[i.val] b)) ∂μ := by
  let Bad := fun i : Fin m => U∩{b | p (e^[i.val] b)≠q (e^[i.val] b)}
  have hsub : {x | p x≠q x}⊆(⋃ i : Fin m,(e^[i.val]) '' U)ᶜ ∪
      ⋃ i : Fin m,(e^[i.val]) '' Bad i := by
    intro x hx
    by_cases ht : x∈⋃ i : Fin m,(e^[i.val]) '' U
    · obtain ⟨i,b,hb,rfl⟩ := mem_iUnion.mp ht
      exact Or.inr (mem_iUnion.mpr ⟨i,b,⟨hb,hx⟩,rfl⟩)
    · exact Or.inl ht
  have hbound : μ {x | p x≠q x}≤μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+∑ i : Fin m,μ (Bad i) := by
    calc
      _≤_ := measure_mono hsub
      _≤μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+μ (⋃ i : Fin m,(e^[i.val]) '' Bad i) := measure_union_le _ _
      _≤μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+∑' i : Fin m,μ ((e^[i.val]) '' Bad i) := add_le_add_right (measure_iUnion_le _) _
      _=_ := by simp only [measure_iterate_image μ e he,tsum_fintype]
  have hsumfin : (∑ i : Fin m,μ (Bad i))≠⊤ := ENNReal.sum_ne_top.mpr (fun i _ => measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono (show μ (⋃ i : Fin m,(e^[i.val]) '' U)ᶜ+∑ i : Fin m,μ (Bad i)≠⊤ from ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,hsumfin⟩) hbound
  rw [ENNReal.toReal_add (measure_ne_top _ _) hsumfin,ENNReal.toReal_sum (by intro i hi; exact measure_ne_top _ _)] at hreal
  have hint (i : Fin m) : Integrable (fun b => symbolCost (p (e^[i.val] b)) (q (e^[i.val] b))) (μ.restrict U) :=
    integrable_finite_observation (μ.restrict U) (fun b => (p (e^[i.val] b),q (e^[i.val] b)))
      ((hp.comp (e.measurable.iterate i.val)).prodMk (hq.comp (e.measurable.iterate i.val)))
      (fun a => symbolCost a.1 a.2)
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have heq (i : Fin m) : (∫ b in U,symbolCost (p (e^[i.val] b)) (q (e^[i.val] b)) ∂μ)=μ.real (Bad i) := by
    rw [finite_symbolCost_integral (μ.restrict U) (fun b => p (e^[i.val] b)) (fun b => q (e^[i.val] b)) (hp.comp (e.measurable.iterate i.val)) (hq.comp (e.measurable.iterate i.val))]
    rw [Measure.real,Measure.restrict_apply' hU,inter_comm]
    rfl
  simp only [heq]
  exact hreal
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

lemma boundedCost_left_triangle {B D : Type*} (c : B → D → ℝ)
    (h0 : ∀ a b,0≤c a b) (h1 : ∀ a b,c a b≤1) (a b : B) (d : D) :
    c a d≤ symbolCost a b+c b d := by
  classical
  by_cases h : a=b
  · subst b; simp [symbolCost]
  · simp only [symbolCost,ite_eq_right h]
    linarith [h0 b d,h1 a d]

theorem lift_cost_transport [Nonempty C] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    {k t r : ℕ} (hn : 0<k+t) (hr : r<k+t)
    (p : X → C) (hp : Measurable p) (F : C → A)
    (v : (Fin (k+t) → A) → ℝ) (R : MatrixCoupling (mass μ (word e p k)) v)
    (c : (Fin k → C) → (Fin (k+t) → A) → ℝ)
    (hc0 : ∀ a b,0≤c a b) (hc1 : ∀ a b,c a b≤1)
    (zero one : A) (h01 : zero≠one)
    (hmark : ∀ w,¬Marker.MarkedBlock hr zero one w → v w=0)
    (D : (Fin (k+t) → A) → (Fin k → C)) (c₀ : C) {ε : ℝ} (hε : 0<ε) :
    ∃ (U : Set X) (q : X → A),MeasurableSet U ∧ 0<μ U ∧ Measurable q ∧
      Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ<ε ∧
      (∀ b,mass (μ.restrict U) (word e q (k+t)) b=μ.real U*v b) ∧
      (∫ x in U,c (word e p k x) (word e q (k+t) x) ∂μ)≤μ.real U*(R.cost c+ε) ∧
      (∀ x,x∉⋃ i : Fin (k+t),(e^[i.val]) '' U → q x=F (p x)) ∧
      μ.real {x | Marker.decodeWindow hn hr zero one (extendPrefixDecoder D c₀)
        (word e q (2*(k+t)) (integerIterate e (-((k+t : ℕ) : ℤ)) x))≠p x} <
        2*ε+R.cost (fun a b => symbolCost a (D b))+(t : ℝ)/(k+t : ℕ) := by
  have hw := word_measurable e e.measurable p hp k
  obtain ⟨U,hU,hUp,hd,hcover,hclose⟩ := exists_unbiased_rohlin_tower μ e he hn (word e p k) hw hε
  let ν := (μ U)⁻¹ • μ.restrict U
  have : IsProbabilityMeasure ν := normalized_restriction_probability μ hUp
  obtain ⟨S,hS⟩ := coupling_of_observation_lawClose ν μ (word e p k) (word e p k) hw hw hclose
  have hC := S.comp_cost_le R symbolCost c c (boundedCost_left_triangle c hc0 hc1)
  have hD := S.comp_cost_le R symbolCost (fun a b => symbolCost a (D b))
    (fun a b => symbolCost a (D b)) (fun a b d => symbolCost_triangle a b (D d))
  have hc : 0≤μ.real U := measureReal_nonneg
  let W := (S.comp R).scale (μ.real U) hc
  let W' : MatrixCoupling (mass (μ.restrict U) (word e p k)) (fun b => μ.real U*v b) := {
    weight := W.weight
    nonneg := W.nonneg
    row := fun a => (W.row a).trans (normalize_mass_cancel μ hUp (word e p k) a)
    col := W.col }
  have hWC : W'.cost c≤μ.real U*(R.cost c+ε) := by
    change W.cost c≤_
    rw [MatrixCoupling.scale_cost]
    apply mul_le_mul_of_nonneg_left _ hc
    linarith
  have hWD : W'.cost (fun a b => symbolCost a (D b))≤
      μ.real U*(ε+R.cost (fun a b => symbolCost a (D b))) := by
    change W.cost _≤_
    rw [MatrixCoupling.scale_cost]
    exact mul_le_mul_of_nonneg_left (hD.trans (add_le_add hS le_rfl)) hc
  obtain ⟨q,hq,hjoint,hbase,_hpaint,hoff⟩ :=
    realize_prefix_tower_coupling μ e he.toMeasurePreserving hU k t hd p hp F _ W'
  have hmarked : ∀ᵐ b ∂μ.restrict U,Marker.MarkedBlock hr zero one (word e q (k+t) b) :=
    ae_observation_of_zero_bad_mass (μ.restrict U) (word e q (k+t))
      (Marker.MarkedBlock hr zero one) (fun w hw => by rw [hbase w,hmark w hw,mul_zero])
  have hb := marked_tower_prefix_decoder_error μ e he.toMeasurePreserving p q hn hr zero one h01 D c₀ hU hmarked
  rw [prefix_tower_decoder_error μ e hU k t p q hp hq W' hjoint D] at hb
  refine ⟨U,q,hU,hUp,hq,hd,hcover,hbase,?_,hoff,?_⟩
  · rw [integral_cost_of_realization (μ.restrict U) (word e p k) hw (word e q (k+t))
      (word_measurable e e.measurable q hq _) W' hjoint c]
    exact hWC
  · have hmass := tower_real_mass_le_one μ e he.toMeasurePreserving hU (k+t) hd
    have htail := tower_suffix_mass_le μ e he.toMeasurePreserving hU hn hd
    have hD0 := R.cost_nonneg (fun a b => symbolCost a (D b)) (fun _ _ => symbolCost_nonneg _ _)
    have hh := mul_le_mul_of_nonneg_right hmass
      (show 0≤ε+R.cost (fun a b => symbolCost a (D b)) by linarith)
    have hbound := mul_le_mul_of_nonneg_left hWD (Nat.cast_nonneg (k+t))
    nlinarith
end HyperbolicCoding

end

end OAI
