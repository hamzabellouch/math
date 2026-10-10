import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.ErgodicL1
import OAI.Dynamics.StandardMap.Coupling.ConditionalRefinementInformation
import OAI.Dynamics.StandardMap.Coupling.FiniteProductVariance

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def productWordWeight (p : A → ℝ) (n : ℕ) (w : Fin n → A) : ℝ := ∏ i,p (w i)
noncomputable def wordInformation (p : A → ℝ) {n : ℕ} (w : Fin n → A) : ℝ := ∑ i,-Real.log (p (w i))

omit [DecidableEq A] in
lemma productWordWeight_sum (p : A → ℝ) (hp : ∑ a,p a=1) (n : ℕ) :
    (∑ w : Fin n → A,productWordWeight p n w)=1 :=
  productWeights_sum (fun _ : Fin n => p) (fun _ => hp)

omit [Fintype A] [DecidableEq A] in
lemma productWordWeight_nonneg (p : A → ℝ) (hp : ∀ a,0≤p a) (n : ℕ) (w : Fin n → A) :
    0≤productWordWeight p n w := Finset.prod_nonneg (fun i _ => hp (w i))

omit [Fintype A] [DecidableEq A] in
lemma productWordWeight_eq_exp (p : A → ℝ) {n : ℕ} (w : Fin n → A)
    (hw : ∀ i,0<p (w i)) : productWordWeight p n w=Real.exp (-wordInformation p w) := by
  rw [wordInformation,←Finset.sum_neg_distrib]
  simp only [neg_neg,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (hw i)).symm

omit [DecidableEq A] in
theorem information_codebook_card (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) (L : ℝ) :
    let S := Finset.univ.filter (fun w : Fin n → A => (∀ i,0<p (w i)) ∧ wordInformation p w≤L)
    (S.card : ℝ)≤Real.exp L := by
  intro S
  have hweights (w : Fin n → A) (hw : w∈S) : Real.exp (-L)≤productWordWeight p n w := by
    obtain ⟨hpos,hinfo⟩ := (Finset.mem_filter.mp hw).2
    rw [productWordWeight_eq_exp p w hpos]
    exact Real.exp_le_exp.mpr (neg_le_neg hinfo)
  have hmass : (S.card : ℝ)*Real.exp (-L)≤1 := by
    calc
      _=∑ _w∈S,Real.exp (-L) := by simp
      _≤∑ w∈S,productWordWeight p n w := Finset.sum_le_sum hweights
      _≤∑ w : Fin n → A,productWordWeight p n w :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun w _ _ => productWordWeight_nonneg p hp n w)
      _=1 := productWordWeight_sum p hs n
  have h := mul_le_mul_of_nonneg_right hmass (Real.exp_pos L).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at h
  exact h

section Ergodic
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [IsProbabilityMeasure μ] in
lemma wordInformation_word (f : X → X) (p : X → A) (n : ℕ) (x : X) :
    wordInformation (mass μ p) (word f p n x)=birkhoffSum f (information μ p) n x := by
  simp only [wordInformation,word,information,birkhoffSum]
  exact Fin.sum_univ_eq_sum_range (fun i => -Real.log (mass μ p (p (f^[i] x)))) n

omit [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [IsProbabilityMeasure μ] in
lemma information_uniform_bound (p : X → A) (x : X) :
    |information μ p x|≤∑ a : A,|Real.log (mass μ p a)| := by
  simp only [information,abs_neg]
  exact Finset.single_le_sum (fun a _ => abs_nonneg (Real.log (mass μ p a))) (Finset.mem_univ (p x))

omit [DecidableEq A] in
theorem eventually_upper_information_codebook (f : X → X) (hf : Ergodic f μ)
    (p : X → A) (hp : Measurable p) {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∃ S : Finset (Fin n → A),
      (S.card : ℝ)≤Real.exp ((n : ℝ)*(obs μ p+δ)) ∧
      μ.real {x | word f p n x∉S}<ε := by
  have hC : 0≤∑ a : A,|Real.log (mass μ p a)| := Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hav := ergodic_L1_bounded hf (information_measurable μ p hp) hC (information_uniform_bound μ p)
  rw [integral_information μ p hp] at hav
  have hsmall := (tendsto_order.mp hav).2 (δ*ε) (mul_pos hδ hε)
  filter_upwards [hsmall,eventually_gt_atTop 0] with n hsmall hn
  let S := Finset.univ.filter (fun w : Fin n → A =>
    (∀ i,0 < mass μ p (w i)) ∧ wordInformation (mass μ p) w≤(n : ℝ)*(obs μ p+δ))
  refine ⟨S,information_codebook_card _ (mass_nonneg μ p) (by simpa using mass_sum μ p hp) n _,?_⟩
  have hpos : ∀ᵐ x ∂μ,∀ i : Fin n,0 < mass μ p (p (f^[i.val] x)) := by
    apply ae_all_iff.mpr
    intro i
    exact (hf.toMeasurePreserving.iterate i.val).quasiMeasurePreserving.ae (ae_mass_positive μ p)
  have hnpos : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  have hsub : ∀ᵐ x ∂μ,word f p n x∉S → δ≤|orbitAverage f (information μ p) n x-obs μ p| := by
    filter_upwards [hpos] with x hx hbad
    have hi : (n : ℝ)*(obs μ p+δ)<wordInformation (mass μ p) (word f p n x) := by
      by_contra h
      exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,le_of_not_gt h⟩)
    rw [wordInformation_word] at hi
    have hb : obs μ p+δ<orbitAverage f (information μ p) n x := (lt_div_iff₀ hnpos).mpr (by simpa only [mul_comm] using hi)
    exact le_trans (by linarith) (le_abs_self _)
  have hi : Integrable (fun x => |orbitAverage f (information μ p) n x-obs μ p|) μ :=
    ((orbitAverage_integrable hf.toMeasurePreserving (information_integrable μ p hp) n).sub
      (integrable_const _)).abs
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ:=μ)
    (f:=fun x => |orbitAverage f (information μ p) n x-obs μ p|)
    (ae_of_all _ (fun x => abs_nonneg _)) hi δ
  have hmono : μ.real {x | word f p n x∉S}≤
      μ.real {x | δ≤|orbitAverage f (information μ p) n x-obs μ p|} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hb := mul_le_mul_of_nonneg_left hmono hδ.le
  nlinarith

end Ergodic
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def weightEntropy (p : A → ℝ) : ℝ := ∑ a,p a*(-Real.log (p a))
noncomputable def informationVariance (p : A → ℝ) : ℝ :=
  ∑ a,p a*(-Real.log (p a)-weightEntropy p)^2

omit [DecidableEq A] in
lemma weightInformation_centered (p : A → ℝ) (hs : ∑ a,p a=1) :
    (∑ a,p a*(-Real.log (p a)-weightEntropy p))=0 := by
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul,weightEntropy]
  ring

omit [DecidableEq A] in
lemma wordInformation_centered (p : A → ℝ) (n : ℕ) (w : Fin n → A) :
    wordInformation p w-(n : ℝ)*weightEntropy p=
      ∑ i : Fin n,(-Real.log (p (w i))-weightEntropy p) := by
  simp [wordInformation,Finset.sum_sub_distrib]

omit [DecidableEq A] in
lemma wordInformation_variance (p : A → ℝ) (hs : ∑ a,p a=1) (n : ℕ) :
    (∑ w : Fin n → A,productWordWeight p n w *
      (wordInformation p w-(n : ℝ)*weightEntropy p)^2)=(n : ℝ)*informationVariance p := by
  simp_rw [wordInformation_centered]
  have h := expectation_centered_sum_square (fun _ : Fin n => p) (fun _ => hs)
    (fun _ a => -Real.log (p a)-weightEntropy p) (fun _ => weightInformation_centered p hs)
  simpa only [finiteExpectation,productWeights,productWordWeight,informationVariance,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

omit [Fintype A] [DecidableEq A] in
lemma productWordWeight_le_exp (p : A → ℝ) (hp : ∀ a,0≤p a) {n : ℕ}
    (w : Fin n → A) {L : ℝ} (hI : L≤wordInformation p w) :
    productWordWeight p n w≤Real.exp (-L) := by
  by_cases hpos : ∀ i,0<p (w i)
  · rw [productWordWeight_eq_exp p w hpos]
    exact Real.exp_le_exp.mpr (neg_le_neg hI)
  · push Not at hpos
    obtain ⟨i,hi⟩ := hpos
    have hz := le_antisymm hi (hp (w i))
    have hw : productWordWeight p n w=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact hz
    rw [hw]
    exact (Real.exp_pos _).le

omit [DecidableEq A] in
lemma iid_bad_information_mass (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    (∑ w : Fin n → A,if wordInformation p w<(n : ℝ)*(weightEntropy p-δ)
      then productWordWeight p n w else 0)*((n : ℝ)*δ)^2 ≤
      (n : ℝ)*informationVariance p := by
  rw [←wordInformation_variance p hs n,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  split_ifs with hw
  · have hdev : (n : ℝ)*δ< -(wordInformation p w-(n : ℝ)*weightEntropy p) := by nlinarith
    have hnd : 0≤(n : ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
    apply mul_le_mul_of_nonneg_left _ (productWordWeight_nonneg p hp n w)
    nlinarith
  · simp only [zero_mul]
    exact mul_nonneg (productWordWeight_nonneg p hp n w) (sq_nonneg _)

theorem eventually_iid_typical_words (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) {δ ε : ℝ} (hδ : 0<δ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∃ T : Finset (Fin n → A),
      (∀ w∈T,productWordWeight p n w≤Real.exp (-(n : ℝ)*(weightEntropy p-δ))) ∧
      (∑ w : Fin n → A,if w∉T then productWordWeight p n w else 0)<ε := by
  have hV : 0 ≤ informationVariance p :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (sq_nonneg _))
  obtain ⟨N,hN⟩ := exists_nat_gt (informationVariance p/(ε*δ^2))
  filter_upwards [eventually_ge_atTop N,eventually_gt_atTop 0] with n hn hn0
  let T := Finset.univ.filter (fun w : Fin n → A => (n : ℝ)*(weightEntropy p-δ)≤wordInformation p w)
  refine ⟨T,?_,?_⟩
  · intro w hw
    have h := productWordWeight_le_exp p hp w (Finset.mem_filter.mp hw).2
    simpa only [neg_mul] using h
  · have ht (w : Fin n → A) : w∉T ↔ wordInformation p w<(n : ℝ)*(weightEntropy p-δ) := by
      simp only [T,Finset.mem_filter,Finset.mem_univ,true_and,not_le]
    simp_rw [ht]
    have hb := iid_bad_information_mass p hp hs n hδ
    have hnpos : 0<(n : ℝ) := Nat.cast_pos.mpr hn0
    have hnN : (N : ℝ)≤n := by exact_mod_cast hn
    have hlarge : informationVariance p<ε*δ^2*(n : ℝ) := by
      have h := (div_lt_iff₀ (mul_pos hε (sq_pos_of_pos hδ))).mp (hN.trans_le hnN)
      nlinarith
    have hh := mul_lt_mul_of_pos_left hlarge hnpos
    have hsq : 0<((n : ℝ)*δ)^2 := sq_pos_of_pos (mul_pos hnpos hδ)
    nlinarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def finiteWeightLaw (p : A → ℝ) : Measure A :=
  ∑ a,ENNReal.ofReal (p a) • Measure.dirac a

instance finiteWeightLaw_finite (p : A → ℝ) : IsFiniteMeasure (finiteWeightLaw p) := by
  constructor
  simp [finiteWeightLaw,Measure.finsetSum_apply]

lemma finiteWeightLaw_singleton (p : A → ℝ) (a : A) :
    finiteWeightLaw p {a}=ENNReal.ofReal (p a) := by
  classical
  simp [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,Pi.single_apply]

omit [MeasurableSingletonClass A] in
lemma finiteWeightLaw_probability (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    IsProbabilityMeasure (finiteWeightLaw p) := by
  constructor
  simp only [finiteWeightLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    Measure.dirac_apply_of_mem (mem_univ _),mul_one]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a),hs,ENNReal.ofReal_one]

def iidShift : (ℤ → A) ≃ᵐ (ℤ → A) where
  toFun w i := w (i+1)
  invFun w i := w (i-1)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp
  measurable_toFun := Measurable.of_eval (fun _ => measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift^[n]) w i=w (i+n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift^[n]) w (i+1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_preserving (β : Measure A) [IsProbabilityMeasure β] :
    MeasurePreserving (iidShift (A:=A)) (Measure.infinitePi (fun _ : ℤ => β))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  refine ⟨iidShift.measurable,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j : ℤ => by omega)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_eq (n : ℕ) (w : ℤ → A) :
    word iidShift (fun z : ℤ → A => z 0) n w=fun i : Fin n => w i.val := by
  funext i
  change (iidShift^[i.val]) w 0=_
  rw [iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_word_law (β : Measure A) [IsProbabilityMeasure β] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℤ => β)).map (word iidShift (fun z : ℤ → A => z 0) n)=
      Measure.pi (fun _ : Fin n => β) := by
  have hi : Function.Injective (fun i : Fin n => (i.val : ℤ)) := by
    intro i j h
    apply Fin.ext
    change (i.val : ℤ)=(j.val : ℤ) at h
    exact Int.ofNat_inj.mp h
  simpa only [funext (iid_word_eq (A:=A) n),Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P:=fun _ : ℤ => β) hi)

lemma iid_word_mass (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    (n : ℕ) (w : Fin n → A) :
    mass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun z : ℤ → A => z 0) n) w=productWordWeight p n w := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  change (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)).real
    ((word iidShift (fun z : ℤ → A => z 0) n) ⁻¹' {w})=_
  rw [←map_measureReal_apply (word_measurable iidShift iidShift.measurable _
    (measurable_pi_apply 0) n) (measurableSet_singleton w)]
  rw [iid_word_law,Measure.real,Measure.pi_singleton]
  simp only [finiteWeightLaw_singleton,ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _),productWordWeight]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory ProbabilityTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_disjoint_coordinate_independent {I J : Type*} (β : Measure A) [IsProbabilityMeasure β]
    (f : I → ℤ) (g : J → ℤ) (hfg : ∀ i j,f i≠g j) :
    IndepFun (fun w : ℤ → A => fun i => w (f i)) (fun w : ℤ → A => fun j => w (g j))
      (Measure.infinitePi (fun _ : ℤ => β)) := by
  classical
  apply IndepFun.process_indepFun_process (fun i => measurable_pi_apply (f i))
    (fun j => measurable_pi_apply (g j))
  intro S T
  have hST : Disjoint (S.image f) (T.image g) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hz'
    exact hfg i j he.symm
  have h := (iIndepFun_infinitePi (P:=fun _ : ℤ => β) (X:=fun _ a => a)
    (fun _ => measurable_id)).indepFun_finset (S.image f) (T.image g) hST
    (fun _ => measurable_pi_apply _)
  let F : ((S.image f) → A) → (S → A) := fun w i => w ⟨f i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩
  let G : ((T.image g) → A) → (T → A) := fun w j => w ⟨g j,Finset.mem_image.mpr ⟨j,j.2,rfl⟩⟩
  exact h.comp (Measurable.of_eval (fun _ => measurable_pi_apply _))
    (Measurable.of_eval (fun _ => measurable_pi_apply _)) (φ:=F) (ψ:=G)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iidShift_symm_iterate (w : ℤ → A) (n : ℕ) (i : ℤ) :
    (iidShift.symm^[n]) w i=w (i-n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (iidShift.symm^[n]) w (i-1)=_
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_tail_eq (w : ℤ → A) (n : ℕ) :
    tailName iidShift (fun w : ℤ → A => w 0) n w=fun i : ℕ => w ((i+n : ℕ) : ℤ) := by
  funext i
  simp only [tailName,iidShift_iterate,zero_add]

omit [Fintype A] [MeasurableSingletonClass A] in
lemma iid_past_eq (w : ℤ → A) (n : ℕ) :
    tailName iidShift.symm (fun w : ℤ → A => w 0) n w=fun i : ℕ => w (-((i+n : ℕ) : ℤ)) := by
  funext i
  simp only [tailName,iidShift_symm_iterate,zero_sub]

omit [Fintype A] [MeasurableSingletonClass A] in
theorem iid_weakBernoulli (β : Measure A) [IsProbabilityMeasure β] :
    WeakBernoulliProcess (Measure.infinitePi (fun _ : ℤ => β)) iidShift (fun w : ℤ → A => w 0) := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 1] with n hn
  let μ := Measure.infinitePi (fun _ : ℤ => β)
  have hi := iid_disjoint_coordinate_independent β (fun i : ℕ => -((i+n : ℕ) : ℤ))
    (fun i : ℕ => ((i+n : ℕ) : ℤ)) (by intro i j h; omega)
  have hp : IndepFun (tailName iidShift.symm (fun w : ℤ → A => w 0) n)
      (tailName iidShift (fun w : ℤ → A => w 0) n) μ := by
    have hP : tailName iidShift.symm (fun w : ℤ → A => w 0) n=
        fun w : ℤ → A => fun i : ℕ => w (-((i+n : ℕ) : ℤ)) := funext (fun w => iid_past_eq w n)
    have hF : tailName iidShift (fun w : ℤ → A => w 0) n=
        fun w : ℤ → A => fun i : ℕ => w ((i+n : ℕ) : ℤ) := funext (fun w => iid_tail_eq w n)
    rw [hP,hF]
    exact hi
  have hmap := hp.map_prod_eq_prod_map_map
    (measurable_tailName iidShift.symm.measurable (measurable_pi_apply 0) n).aemeasurable
    (measurable_tailName iidShift.measurable (measurable_pi_apply 0) n).aemeasurable
  have hpres := iidShift_preserving β
  rw [stationary_tail_law μ (hpres.symm iidShift) (measurable_pi_apply 0) n,
    stationary_tail_law μ hpres (measurable_pi_apply 0) n] at hmap
  have heq : μ.map (remotePair iidShift iidShift.symm (fun w : ℤ → A => w 0) n)=
      remoteProductLaw μ iidShift iidShift.symm (fun w : ℤ → A => w 0) := hmap
  change LawClose (μ.map (remotePair iidShift iidShift.symm (fun w : ℤ → A => w 0) n))
    (remoteProductLaw μ iidShift iidShift.symm (fun w : ℤ → A => w 0)) ε
  rw [heq]
  intro D _
  simpa only [sub_self,abs_zero] using hε.le

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma shannon_product_weights {B : Type*} [Fintype B] (p : A → ℝ) (q : B → ℝ)
    (hp : ∑ a,p a=1) (hq : ∑ b,q b=1) :
    shannon (fun ab : A×B => p ab.1*q ab.2)=shannon p+shannon q := by
  simp only [shannon,Fintype.sum_prod_type,Real.negMulLog_mul,Finset.sum_add_distrib]
  simp only [←Finset.sum_mul,←Finset.mul_sum,hp,hq,one_mul]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma shannon_productWordWeight (p : A → ℝ) (hs : ∑ a,p a=1) (n : ℕ) :
    shannon (productWordWeight p n)=(n : ℝ)*weightEntropy p := by
  classical
  have hdef : shannon p=weightEntropy p := by
    unfold shannon weightEntropy
    apply Finset.sum_congr rfl
    intro a _
    simp [Real.negMulLog]
  induction n with
  | zero => simp [shannon,productWordWeight]
  | succ n ih =>
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    have he : (∑ w : Fin (n+1) → A,Real.negMulLog (productWordWeight p (n+1) w))=
        ∑ ab : A×(Fin n → A),Real.negMulLog (p ab.1*productWordWeight p n ab.2) := by
      rw [←Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro ab _
      congr 1
      simp [productWordWeight,Fin.prod_univ_succ,e]
    rw [shannon,he]
    change shannon (fun ab : A×(Fin n → A) => p ab.1*productWordWeight p n ab.2)=_
    rw [shannon_product_weights p _ hs (productWordWeight_sum p hs n),hdef,ih]
    push_cast
    ring

theorem iid_rate [DecidableEq A] (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) :
    rate (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) iidShift
      (fun w : ℤ → A => w 0)=weightEntropy p := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  have hword (n : ℕ) : obs (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p))
      (word iidShift (fun w : ℤ → A => w 0) n)=(n : ℝ)*weightEntropy p := by
    rw [obs,funext (iid_word_mass p hp hs n)]
    exact shannon_productWordWeight p hs n
  have ht := rate_tendsto (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) iidShift
    (iidShift_preserving _) (fun w : ℤ → A => w 0) (measurable_pi_apply 0)
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hword,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory ProbabilityTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma weight_le_one (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1) (a : A) : p a≤1 := by
  rw [←hs]
  exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma weightEntropy_zero_of_one (p : A → ℝ) (hp : ∀ a,0≤p a) (hs : ∑ a,p a=1)
    {a : A} (ha : p a=1) : weightEntropy p=0 := by
  classical
  have hzer : ∑ b∈Finset.univ.erase a,p b=0 := by
    have hh := Finset.sum_erase_add (s:=Finset.univ) p (Finset.mem_univ a)
    rw [hs,ha] at hh
    linarith
  have hb (b : A) (hba : b≠a) : p b=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp hzer b (by simp [hba])
  unfold weightEntropy
  apply Finset.sum_eq_zero
  intro b _
  by_cases hba : b=a
  · simp [hba,ha]
  · simp [hb b hba]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma positive_weightEntropy_max_bound (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (hh : 0 < weightEntropy p) :
    ∃ c : ℝ,0≤c ∧ c < 1 ∧ ∀ a,p a≤c := by
  classical
  have : Nonempty A := by
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp at hs
  obtain ⟨a,ha,hamax⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  refine ⟨p a,hp a,?_,fun b => hamax b (Finset.mem_univ b)⟩
  apply lt_of_le_of_ne (weight_le_one p hp hs a)
  intro he
  have hz := weightEntropy_zero_of_one p hp hs he
  linarith

theorem iid_nullSingleton [DecidableEq A] (p : A → ℝ) (hp : ∀ a,0≤p a)
    (hs : ∑ a,p a=1) (hh : 0 < weightEntropy p) :
    NullSingletonClass (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)) := by
  let : IsProbabilityMeasure (finiteWeightLaw p) := finiteWeightLaw_probability p hp hs
  let μ := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw p)
  obtain ⟨c,hc,hc1,hbound⟩ := positive_weightEntropy_max_bound p hp hs hh
  constructor
  intro w
  have hb (n : ℕ) : μ.real {w}≤c^n := by
    have hsub : ({w} : Set (ℤ → A))⊆
        (word iidShift (fun y : ℤ → A => y 0) n) ⁻¹' {word iidShift (fun y : ℤ → A => y 0) n w} := by
      rintro y rfl
      rfl
    have h := measureReal_mono (μ:=μ) hsub
    change μ.real {w}≤ mass μ (word iidShift (fun y : ℤ → A => y 0) n)
      (word iidShift (fun y : ℤ → A => y 0) n w) at h
    have himass := iid_word_mass p hp hs n (word iidShift (fun y : ℤ → A => y 0) n w)
    change mass μ _ _=_ at himass
    rw [himass] at h
    apply h.trans
    calc
      productWordWeight p n _ ≤ ∏ _i : Fin n,c := Finset.prod_le_prod₀
        (fun _ _ => hp _) (fun _ _ => hbound _)
      _=c^n := by simp
  have hz : μ.real {w}=0 := le_antisymm
    (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1) hb) ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top μ _)

theorem iid_finite_determination {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty A] [DecidableEq A]
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) {η : ℝ} (hη : 0 < η) :
    ∃ m s : ℕ,0 < s ∧ ∃ δ : ℝ,0 < δ ∧
      ∀ (μ : Measure X) (_ : IsProbabilityMeasure μ) (_ : NullSingletonClass μ)
        (f : X → X) (_ : MeasurePreserving f μ μ) (q : X → A),Measurable q →
        LawClose (μ.map (word f q m)) (Measure.pi (fun _ : Fin m => finiteWeightLaw β)) δ →
        weightEntropy β-δ≤rate μ f q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word f q (n*s))) (productWordWeight β (n*s)),
          R.cost nameCost≤η*(n*s : ℕ) := by
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  let : NullSingletonClass ν := iid_nullSingleton β hβ hβsum hβentropy
  obtain ⟨m,s,hs,δ,hδ,hfd⟩ := weakBernoulli_finite_determination (Y:=X) ν iidShift
    (iidShift_preserving _) (fun w : ℤ → A => w 0) (measurable_pi_apply 0)
    (iid_weakBernoulli _) hη
  refine ⟨m,s,hs,δ,hδ,?_⟩
  intro μ hμ hnull f hf q hq hlaw hrate n
  let : IsProbabilityMeasure μ := hμ
  let : NullSingletonClass μ := hnull
  have hclose : LawClose (ν.map (word iidShift (fun w : ℤ → A => w 0) m))
      (μ.map (word f q m)) δ := by
    rw [iid_word_law]
    exact hlaw.symm
  have hrate' : rate ν iidShift (fun w : ℤ → A => w 0)-δ≤rate μ f q := by
    simpa only [ν,iid_rate β hβ hβsum] using hrate
  obtain ⟨R,hR⟩ := hfd μ hμ hnull f hf q hq hclose hrate' n
  have hR' : R.symm.cost nameCost≤η*(n*s : ℕ) := by
    rw [MatrixCoupling.symm_cost R nameCost nameCost_comm]
    exact hR
  have heq : mass ν (word iidShift (fun w : ℤ → A => w 0) (n*s)) =
      productWordWeight β (n*s) := funext (iid_word_mass β hβ hβsum (n*s))
  rw [←heq]
  exact ⟨R.symm,hR'⟩

end HyperbolicCoding

end

end OAI
