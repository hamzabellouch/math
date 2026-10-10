import OAI.Probability.GaussianReplacement.Sphere

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

open InformationTheory

lemma joint_le_fst_prod_count {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [SFinite P.fst] :
    P ≤ P.fst.prod (Measure.count : Measure W) := by
  apply Measure.le_iff.mpr
  intro t ht
  have hm (w : W) : MeasurableSet {a : A | (a,w) ∈ t} :=
    ht.preimage (measurable_id.prodMk measurable_const)
  calc
    P t ≤ P (⋃ w : W, Prod.fst ⁻¹' {a : A | (a,w) ∈ t}) := by
      apply measure_mono
      intro z hz
      exact Set.mem_iUnion.mpr ⟨z.2, hz⟩
    _ ≤ ∑' w : W, P (Prod.fst ⁻¹' {a : A | (a,w) ∈ t}) := measure_iUnion_le _
    _ = ∑' w : W, P.fst {a : A | (a,w) ∈ t} := by
      congr 1; funext w; exact (Measure.fst_apply (hm w)).symm
    _ = (P.fst.prod Measure.count) t := by
      rw [Measure.prod_apply_symm ht, lintegral_count]
      rfl

lemma joint_ac_fst_prod_count {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [SFinite P.fst] :
    P ≪ P.fst.prod (Measure.count : Measure W) := (joint_le_fst_prod_count P).absolutelyContinuous

lemma ae_positive_atom {W : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (π : Measure W) : ∀ᵐ w ∂π, π {w} ≠ 0 := by
  have : π {w | π {w} = 0} = 0 := by
    rw [show {w | π {w} = 0} = ⋃ w : {w : W // π {w} = 0}, ({w.1} : Set W) by
      ext w; simp]
    exact measure_iUnion_null (fun w => w.2)
  simpa only [ae_iff, not_not] using this

lemma joint_ac_prod_marginals {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [IsFiniteMeasure P] :
    P ≪ P.fst.prod P.snd := by
  apply Measure.AbsolutelyContinuous.mk
  intro t ht hzero
  have hm (w : W) : MeasurableSet {a : A | (a,w) ∈ t} :=
    ht.preimage (measurable_id.prodMk measurable_const)
  have hsec : ∀ᵐ w ∂P.snd, P.fst {a : A | (a,w) ∈ t} = 0 := by
    rw [Measure.prod_apply_symm ht] at hzero
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_right ht)).mp hzero
  have hslice (w : W) : P (t ∩ Prod.snd ⁻¹' {w}) = 0 := by
    by_cases hw : P.snd {w} = 0
    · exact measure_mono_null Set.inter_subset_right (by rwa [← Measure.snd_apply (measurableSet_singleton w)])
    · have hz : P.fst {a : A | (a,w) ∈ t} = 0 := (ae_iff_of_countable.mp hsec) w hw
      apply measure_mono_null (t:=Prod.fst ⁻¹' {a : A | (a,w) ∈ t})
      · rintro ⟨a,v⟩ ⟨ha,hv⟩
        have hvw : v = w := hv
        simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hvw] using ha
      · rwa [← Measure.fst_apply (hm w)]
  have he : t = ⋃ w : W, t ∩ Prod.snd ⁻¹' {w} := by ext z; simp
  rw [he]
  exact measure_iUnion_null hslice

lemma joint_le_prod_inverse_mass {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [IsFiniteMeasure P] :
    P ≤ (P.fst.prod P.snd).withDensity (fun z => (P.snd {z.2})⁻¹) := by
  have hm : Measurable (fun w : W => (P.snd {w})⁻¹) := measurable_of_countable _
  rw [← prod_withDensity_right hm]
  apply Measure.le_iff.mpr
  intro t ht
  have htm (w : W) : MeasurableSet {a : A | (a,w) ∈ t} :=
    ht.preimage (measurable_id.prodMk measurable_const)
  have he : t = ⋃ w : W, t ∩ Prod.snd ⁻¹' {w} := by ext z; simp
  calc
    P t ≤ ∑' w : W, P (t ∩ Prod.snd ⁻¹' {w}) := by
      calc P t = P (⋃ w : W, t ∩ Prod.snd ⁻¹' {w}) := congrArg P he
           _ ≤ _ := measure_iUnion_le (fun w : W => t ∩ Prod.snd ⁻¹' {w})
    _ ≤ ∑' w : W, P.fst {a : A | (a,w) ∈ t} * ((P.snd {w})⁻¹ * P.snd {w}) := by
      apply ENNReal.tsum_le_tsum
      intro w
      by_cases hw : P.snd {w} = 0
      · simp only [hw, ENNReal.inv_zero, mul_zero]
        exact le_of_eq (measure_mono_null Set.inter_subset_right
          (by rwa [← Measure.snd_apply (measurableSet_singleton w)]))
      · rw [ENNReal.inv_mul_cancel hw (measure_ne_top _ _), mul_one, Measure.fst_apply (htm w)]
        apply measure_mono
        rintro ⟨a,v⟩ ⟨ha,hv⟩
        have hvw : v = w := hv
        simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hvw] using ha
    _ = (P.fst.prod (P.snd.withDensity (fun w => (P.snd {w})⁻¹))) t := by
      rw [Measure.prod_apply_symm ht, lintegral_withDensity_eq_lintegral_mul P.snd hm
        (measurable_measure_prodMk_right ht), lintegral_countable']
      congr 1; funext w
      change P.fst {a : A | (a,w) ∈ t} * ((P.snd {w})⁻¹ * P.snd {w}) =
        ((P.snd {w})⁻¹ * P.fst {a : A | (a,w) ∈ t}) * P.snd {w}
      ac_rfl

lemma rnDeriv_le_of_le_withDensity {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsFiniteMeasure P] [SigmaFinite Q]
    (b : A → ℝ≥0∞) (hPQ : P ≤ Q.withDensity b) :
    P.rnDeriv Q ≤ᵐ[Q] b := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv P Q)
  intro s hs hsf
  calc
    ∫⁻ x in s, P.rnDeriv Q x ∂Q ≤ P s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ (Q.withDensity b) s := hPQ s
    _ = ∫⁻ x in s, b x ∂Q := withDensity_apply _ hs

lemma klDiv_bound_of_llr_le {A : Type*} [MeasurableSpace A]
    (P Q : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (c : A → ℝ) (hci : Integrable c P)
    (hc : ∀ᵐ x ∂P, llr P Q x ≤ c x) :
    klDiv P Q ≠ ∞ ∧ (klDiv P Q).toReal ≤ ∫ x, c x ∂P := by
  have hri : Integrable (fun x => (Q.rnDeriv P x).toReal) P := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ:=Q) (ν:=P) (s:=Set.univ) (measure_ne_top _ _))
  have hlo : ∀ᵐ x ∂P, -(Q.rnDeriv P x).toReal ≤ llr P Q x := by
    filter_upwards [exp_neg_llr hPQ] with x hx
    have h := Real.add_one_le_exp (-llr P Q x)
    rw [hx] at h
    linarith
  have hli : Integrable (llr P Q) P := integrable_of_le_of_le
    (measurable_llr P Q).aestronglyMeasurable hlo hc hri.neg hci
  refine ⟨klDiv_ne_top hPQ hli, ?_⟩
  rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
  exact integral_mono_ae hli hci hc


noncomputable def shannonEntropy {W : Type*} [MeasurableSpace W] (π : Measure W) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (-Real.log (π {w}).toReal) ∂π

lemma atom_surprisal_nonneg {W : Type*} [MeasurableSpace W]
    (π : Measure W) [IsProbabilityMeasure π] (w : W) :
    0 ≤ -Real.log (π {w}).toReal := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos ENNReal.toReal_nonneg (by exact_mod_cast ENNReal.toReal_mono (by simp) (prob_le_one))

lemma countable_information_le_entropy {A W : Type*} [MeasurableSpace A] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] (P : Measure (A × W)) [IsProbabilityMeasure P]
    (hH : shannonEntropy P.snd ≠ ∞) :
    klDiv P (P.fst.prod P.snd) ≠ ∞ ∧
      (klDiv P (P.fst.prod P.snd)).toReal ≤ (shannonEntropy P.snd).toReal := by
  let c : W → ℝ := fun w => -Real.log (P.snd {w}).toReal
  have hcm : Measurable c := measurable_of_countable _
  have hci : Integrable c P.snd :=
    (lintegral_ofReal_ne_top_iff_integrable hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall (atom_surprisal_nonneg P.snd))).mp hH
  have hcip : Integrable (fun z : A × W => c z.2) P :=
    (integrable_map_measure hcm.aestronglyMeasurable measurable_snd.aemeasurable).mp hci
  have hPQ := joint_ac_prod_marginals P
  have hb := rnDeriv_le_of_le_withDensity P (P.fst.prod P.snd)
    (fun z => (P.snd {z.2})⁻¹)
    (joint_le_prod_inverse_mass P)
  have hpos : ∀ᵐ z : A × W ∂P, P.snd {z.2} ≠ 0 :=
    (ae_map_iff measurable_snd.aemeasurable ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.snd)
  have hll : ∀ᵐ z ∂P, llr P (P.fst.prod P.snd) z ≤ c z.2 := by
    filter_upwards [hPQ.ae_le hb, hpos, Measure.rnDeriv_pos hPQ,
      hPQ.ae_le (Measure.rnDeriv_ne_top P (P.fst.prod P.snd))] with z hz hzp hzr hzt
    have ht : (P.snd {z.2})⁻¹ ≠ ∞ := by simpa using hzp
    have hreal := ENNReal.toReal_mono ht hz
    have hl := Real.log_le_log (ENNReal.toReal_pos hzr.ne' hzt) hreal
    simpa only [llr, ENNReal.toReal_inv, Real.log_inv, c] using hl
  obtain ⟨hf, hi⟩ := klDiv_bound_of_llr_le P (P.fst.prod P.snd) hPQ
    (fun z => c z.2) hcip hll
  refine ⟨hf, hi.trans_eq ?_⟩
  rw [← integral_map measurable_snd.aemeasurable hcm.aestronglyMeasurable]
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (atom_surprisal_nonneg P.snd)) hcm.aestronglyMeasurable)



lemma klDiv_map_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : A ≃ᵐ B) :
    klDiv (P.map e) (Q.map e) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q e.measurable)
  have h := klDiv_map_le (P.map e) (Q.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h

def swapLast {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    (A × B) × C ≃ᵐ (A × C) × B where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  measurable_invFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

lemma map_swapLast_prod {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C) [SFinite μ] [SFinite ν] [SFinite τ] :
    ((μ.prod ν).prod τ).map swapLast = (μ.prod τ).prod ν := by
  have he : (swapLast : (A×B)×C ≃ᵐ (A×C)×B) =
      (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl A).prodCongr
        (MeasurableEquiv.prodComm (α:=B) (β:=C)))).trans MeasurableEquiv.prodAssoc.symm := by
    ext p <;> rfl
  rw [he]
  change Measure.map (MeasurableEquiv.prodAssoc.symm ∘
    (Prod.map id Prod.swap) ∘ MeasurableEquiv.prodAssoc) _ = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap |>.comp MeasurableEquiv.prodAssoc.measurable)]
  rw [← Measure.map_map (measurable_id.prodMap measurable_swap) MeasurableEquiv.prodAssoc.measurable]
  rw [Measure.prodAssoc_prod, ← Measure.map_prod_map _ _ measurable_id measurable_swap,
    Measure.map_id, Measure.prod_swap]
  simpa only [Measure.prodAssoc_prod] using
    (MeasurableEquiv.prodAssoc.map_symm_map (μ:=((μ.prod τ).prod ν)))


def rowInformation {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] (P : Measure ((S×W)×X)) (γ : Measure X) : ℝ≥0∞ :=
  klDiv P (P.fst.prod γ)

lemma rowInformation_le_entropy {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ)
    (hH : shannonEntropy (P.map swapLast).snd ≠ ∞) :
    rowInformation P γ ≠ ∞ ∧
      (rowInformation P γ).toReal ≤ (shannonEntropy (P.map swapLast).snd).toReal := by
  let : IsProbabilityMeasure (P.map (swapLast : (S×W)×X ≃ᵐ (S×X)×W)) :=
    inferInstance
  let π := (P.map swapLast).snd
  have hRef : (((ν.prod π).prod γ).map swapLast) =
      (P.map swapLast).fst.prod (P.map swapLast).snd := by
    rw [map_swapLast_prod, hInd]
  have hi := countable_information_le_entropy (P.map swapLast) hH
  rw [← hRef, klDiv_map_equiv] at hi
  have hchain := klDiv_compProd_eq_add P.fst (ν.prod π) P.condKernel (Kernel.const _ γ)
  rw [P.disintegrate P.condKernel, Measure.compProd_const, Measure.compProd_const] at hchain
  have hle : rowInformation P γ ≤ klDiv P ((ν.prod π).prod γ) := by
    rw [hchain]
    exact le_add_left le_rfl
  exact ⟨ne_top_of_le_ne_top hi.1 hle, (ENNReal.toReal_mono hi.1 hle).trans hi.2⟩

lemma rowInformation_refinement {S W X E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [MeasurableSpace E]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (γ : Measure X) [IsProbabilityMeasure γ] (e : S×W → E) (he : Measurable e) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) γ =
      rowInformation P γ := by
  let f : S×W → S×(W×E) := fun sw => (sw.1,(sw.2,e sw))
  let g : S×(W×E) → S×W := fun sw => (sw.1,sw.2.1)
  have hf : Measurable f := measurable_fst.prodMk (measurable_snd.prodMk he)
  have hg : Measurable g := measurable_fst.prodMk measurable_snd.fst
  let T := Prod.map f (id : X → X)
  let U := Prod.map g (id : X → X)
  have hT : Measurable T := hf.prodMap measurable_id
  have hU : Measurable U := hg.prodMap measurable_id
  have hfst : (P.map T).fst = P.fst.map f := by
    simp only [Measure.fst, Measure.map_map measurable_fst hT,
      Measure.map_map hf measurable_fst]
    rfl
  have hRef : (P.map T).fst.prod γ = (P.fst.prod γ).map T := by
    rw [hfst]
    change _ = (P.fst.prod γ).map (Prod.map f id)
    rw [← Measure.map_prod_map P.fst γ hf measurable_id, Measure.map_id]
  change klDiv (P.map T) ((P.map T).fst.prod γ) = klDiv P (P.fst.prod γ)
  rw [hRef]
  apply le_antisymm (klDiv_map_le _ _ hT)
  have hd := klDiv_map_le (P.map T) ((P.fst.prod γ).map T) hU
  have heq : U ∘ T = id := rfl
  simpa only [Measure.map_map hU hT, heq, Measure.map_id] using hd



def messagePosterior {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] (P : Measure (S×W)) [IsFiniteMeasure P] : Kernel W S :=
  (P.map Prod.swap).condKernel

instance messagePosterior_markov {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] (P : Measure (S×W)) [IsFiniteMeasure P] :
    IsMarkovKernel (messagePosterior P) := by
  unfold messagePosterior
  infer_instance

lemma messagePosterior_apply {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] [MeasurableSingletonClass W]
    (P : Measure (S×W)) [IsFiniteMeasure P] {w : W} (hw : P.snd {w} ≠ 0)
    (s : Set S) (hs : MeasurableSet s) :
    messagePosterior P w s = (P.snd {w})⁻¹ * P (s ×ˢ {w}) := by
  have hfst : (P.map Prod.swap).fst = P.snd := by
    rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]
    rfl
  rw [messagePosterior,Measure.IsCondKernel.apply_of_ne_zero _ _ (by rwa [hfst]),
    hfst,Measure.map_apply measurable_swap (measurableSet_singleton w |>.prod hs)]
  congr 2
  ext x
  simp [and_comm]

lemma messagePosterior_le {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] [MeasurableSingletonClass W]
    (P : Measure (S×W)) [IsFiniteMeasure P] {w : W} (hw : P.snd {w} ≠ 0) :
    messagePosterior P w ≤ (P.snd {w})⁻¹ • P.fst := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [messagePosterior_apply P hw s hs,Measure.smul_apply,smul_eq_mul]
  apply mul_le_mul_right
  rw [Measure.fst_apply hs]
  exact measure_mono (by rintro ⟨s,w⟩ h; exact h.1)

lemma messagePosterior_disintegrate {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S]
    (P : Measure (S×W)) [IsFiniteMeasure P] :
    (P.snd ⊗ₘ messagePosterior P).map Prod.swap = P := by
  have hfst : (P.map Prod.swap).fst = P.snd := by
    rw [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]
    rfl
  rw [← hfst, messagePosterior,Measure.disintegrate,Measure.map_map measurable_swap measurable_swap]
  exact Measure.map_id

def refineSignal {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (S×W)) (e : S×W → E) : Measure (S×(W×E)) :=
  P.map (fun p => (p.1,(p.2,e p)))

instance refineSignal_finite {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (S×W)) [IsFiniteMeasure P] (e : S×W → E) : IsFiniteMeasure (refineSignal P e) := by
  unfold refineSignal
  infer_instance

lemma refineSignal_apply {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) (e : S×W → E) (he : Measurable e)
    (w : W) (v : E) (s : Set S) (hs : MeasurableSet s) :
    refineSignal P e (s ×ˢ {(w,v)}) = P ((s ∩ {x | e (x,w) = v}) ×ˢ {w}) := by
  rw [refineSignal,Measure.map_apply (measurable_fst.prodMk (measurable_snd.prodMk he))
    (hs.prod (measurableSet_singleton (w,v)))]
  congr 1
  ext ⟨a,b⟩
  simp only [mem_preimage,mem_prod,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hs,hx,he⟩
    exact ⟨⟨hs,by simpa [hx] using he⟩,hx⟩
  · rintro ⟨⟨hs,he⟩,hx⟩
    exact ⟨hs,hx,by simpa [hx] using he⟩

lemma refineSignal_mass {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsFiniteMeasure P] (e : S×W → E) (he : Measurable e)
    {w : W} (hw : P.snd {w} ≠ 0) (v : E) :
    (refineSignal P e).snd {(w,v)} = P.snd {w} * messagePosterior P w {x | e (x,w) = v} := by
  have hclass : MeasurableSet {x : S | e (x,w) = v} :=
    (measurableSet_singleton v).preimage (he.comp (measurable_id.prodMk measurable_const))
  rw [messagePosterior_apply P hw _ hclass,←mul_assoc,
    ENNReal.mul_inv_cancel hw (measure_ne_top _ _),one_mul,Measure.snd_apply (measurableSet_singleton (w,v))]
  have heq : (Prod.snd ⁻¹' ({(w,v)} : Set (W×E))) = (univ : Set S) ×ˢ {(w,v)} := by ext x; simp
  rw [heq,refineSignal_apply P e he w v univ MeasurableSet.univ,univ_inter]

lemma refineSignal_positive_original {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) (e : S×W → E) (he : Measurable e)
    {w : W} {v : E} (hv : (refineSignal P e).snd {(w,v)} ≠ 0) : P.snd {w} ≠ 0 := by
  contrapose! hv
  rw [Measure.snd_apply (measurableSet_singleton (w,v)),
    show (Prod.snd ⁻¹' ({(w,v)} : Set (W×E))) = (univ : Set S) ×ˢ {(w,v)} from by ext x; simp,
    refineSignal_apply P e he w v univ MeasurableSet.univ,univ_inter]
  apply measure_mono_null (t:=Prod.snd ⁻¹' {w})
  · intro x hx; exact hx.2
  · rwa [←Measure.snd_apply (measurableSet_singleton w)]

lemma messagePosterior_refinement {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (S×W)) [IsFiniteMeasure P] (e : S×W → E) (he : Measurable e)
    {w : W} {v : E} (hv : (refineSignal P e).snd {(w,v)} ≠ 0) :
    messagePosterior (refineSignal P e) (w,v) =
      (messagePosterior P w {x | e (x,w) = v})⁻¹ •
        (messagePosterior P w).restrict {x | e (x,w) = v} := by
  have hw := refineSignal_positive_original P e he hv
  have hclass : MeasurableSet {x : S | e (x,w) = v} :=
    (measurableSet_singleton v).preimage (he.comp (measurable_id.prodMk measurable_const))
  have hη : messagePosterior P w {x | e (x,w) = v} ≠ 0 := by
    intro hz
    rw [refineSignal_mass P e he hw v,hz,mul_zero] at hv
    exact hv rfl
  ext s hs
  rw [messagePosterior_apply _ hv s hs,refineSignal_apply P e he w v s hs,
    Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hs,
    messagePosterior_apply P hw _ (hs.inter hclass),refineSignal_mass P e he hw v,
    ENNReal.mul_inv (Or.inl hw) (Or.inl (measure_ne_top _ _)), mul_assoc]
  ac_rfl



lemma countable_ac_of_atom {W : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (P Q : Measure W)
    (h : ∀ w, Q {w} = 0 → P {w} = 0) : P ≪ Q := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  rw [show s = ⋃ w : s, ({w.1} : Set W) by ext x; simp]
  apply measure_iUnion_null
  intro w
  exact h w (measure_mono_null (by simp [w.2]) hz)

lemma rnDeriv_atom {W : Type*} [MeasurableSpace W] [MeasurableSingletonClass W]
    (P Q : Measure W) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) {w : W} (hw : Q {w} ≠ 0) :
    P.rnDeriv Q w = P {w} / Q {w} := by
  have h := congrArg (fun M : Measure W => M {w}) (Measure.withDensity_rnDeriv_eq P Q hPQ)
  rw [withDensity_apply _ (measurableSet_singleton w),Measure.restrict_singleton,
    lintegral_smul_measure,lintegral_dirac] at h
  change Q {w} * P.rnDeriv Q w = P {w} at h
  apply (ENNReal.eq_div_iff hw (measure_ne_top _ _)).mpr
  simpa only [mul_comm] using h

lemma countable_entropy_le_crossEntropy {W : Type*} [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (P Q : Measure W) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hci : Integrable (fun w => -Real.log (Q {w}).toReal) P) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤ ∫ w, -Real.log (Q {w}).toReal ∂P := by
  have hpos : ∀ᵐ w ∂P, Q {w} ≠ 0 := hPQ.ae_le (ae_positive_atom Q)
  have he : ∀ᵐ w ∂P, llr P Q w = Real.log (P {w}).toReal - Real.log (Q {w}).toReal := by
    filter_upwards [ae_positive_atom P,hpos] with w hp hq
    rw [llr,rnDeriv_atom P Q hPQ hq,ENNReal.toReal_div,Real.log_div
      (ENNReal.toReal_ne_zero.mpr ⟨hp,measure_ne_top _ _⟩)
      (ENNReal.toReal_ne_zero.mpr ⟨hq,measure_ne_top _ _⟩)]
  have hbound : ∀ᵐ w ∂P, llr P Q w ≤ -Real.log (Q {w}).toReal := by
    filter_upwards [he] with w hw
    rw [hw]
    linarith [atom_surprisal_nonneg P w]
  have hk := klDiv_bound_of_llr_le P Q hPQ _ hci hbound
  have hli := (klDiv_ne_top_iff.mp hk.1).2
  have hpi : Integrable (fun w => -Real.log (P {w}).toReal) P := by
    apply (hci.sub hli).congr
    filter_upwards [he] with w hw
    change -Real.log (Q {w}).toReal - llr P Q w = -Real.log (P {w}).toReal
    rw [hw]
    ring
  have hent : shannonEntropy P = ENNReal.ofReal (∫ w, -Real.log (P {w}).toReal ∂P) := by
    exact (ofReal_integral_eq_lintegral_ofReal hpi (Eventually.of_forall (atom_surprisal_nonneg P))).symm
  refine ⟨by rw [hent]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hent,ENNReal.toReal_ofReal (integral_nonneg (atom_surprisal_nonneg P))]
  have hn : 0 ≤ ∫ w, llr P Q w ∂P := by simpa using integral_llr_add_sub_measure_univ_nonneg hPQ hli
  have hi : (∫ w, llr P Q w ∂P) = (∫ w, -Real.log (Q {w}).toReal ∂P) -
      ∫ w, -Real.log (P {w}).toReal ∂P := by
    rw [←integral_sub hci hpi]
    apply integral_congr_ae
    filter_upwards [he] with w hw
    linarith
  linarith

lemma shannonEntropy_map_le {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    [Countable W] [Countable V] [MeasurableSingletonClass W] [MeasurableSingletonClass V]
    (P : Measure W) [IsProbabilityMeasure P] (f : W → V) :
    shannonEntropy (P.map f) ≤ shannonEntropy P := by
  have hfm : Measurable f := measurable_of_countable _
  let : IsProbabilityMeasure (P.map f) := inferInstance
  unfold shannonEntropy
  rw [lintegral_map (measurable_of_countable _) hfm]
  apply lintegral_mono_ae
  filter_upwards [ae_positive_atom P] with w hw
  apply ENNReal.ofReal_le_ofReal
  apply neg_le_neg
  apply Real.log_le_log (ENNReal.toReal_pos hw (measure_ne_top _ _))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [Measure.map_apply hfm (measurableSet_singleton (f w))]
  exact measure_mono (by intro x hx; simpa only [mem_preimage,mem_singleton_iff] using congrArg f hx)

lemma shannonEntropy_equiv {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    [Countable W] [Countable V] [MeasurableSingletonClass W] [MeasurableSingletonClass V]
    (P : Measure W) [IsProbabilityMeasure P] (e : W ≃ᵐ V) :
    shannonEntropy (P.map e) = shannonEntropy P := by
  let : IsProbabilityMeasure (P.map e) := inferInstance
  apply le_antisymm (shannonEntropy_map_le P e)
  simpa only [e.map_symm_map] using shannonEntropy_map_le (P.map e) e.symm

lemma geometric_pair_entropy {P : Measure (ℕ×ℕ)} [IsProbabilityMeasure P]
    (M : ℝ) (hM : 1 ≤ M)
    (hi : Integrable (fun x : ℕ×ℕ => (x.1:ℝ)+(x.2:ℝ)) P)
    (hmean : (∫ x : ℕ×ℕ, (x.1:ℝ)+(x.2:ℝ) ∂P) ≤ M) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤ 1 + 2 * Real.log (M+1) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM1 : 0 < M+1 := by linarith
  let p : unitInterval := ⟨(M+1)⁻¹, ⟨(inv_pos.mpr hM1).le, (inv_le_one₀ hM1).mpr (by linarith)⟩⟩
  have hp0 : p ≠ 0 := by
    intro h
    have hh : (M+1)⁻¹ = 0 := congrArg Subtype.val h
    exact (inv_ne_zero hM1.ne') hh
  have hp1 : p ≠ 1 := by
    intro h
    have hh := congrArg Subtype.val h
    have hlt : (M+1)⁻¹ < 1 := (inv_lt_one₀ hM1).mpr (by linarith)
    exact hlt.ne hh
  have hpR : 0 < (p:ℝ) := inv_pos.mpr hM1
  have hqR : 0 < 1-(p:ℝ) := by
    change 0 < 1-(M+1)⁻¹
    linarith [(inv_lt_one₀ hM1).mpr (by linarith : 1 < M+1)]
  let Q := (geometricMeasure p).prod (geometricMeasure p)
  have hatom (x : ℕ×ℕ) : Q {x} = ENNReal.ofReal (((1-p)^x.1*p) * ((1-p)^x.2*p)) := by
    rw [show ({x} : Set (ℕ×ℕ)) = {x.1} ×ˢ {x.2} by ext y; simp [Prod.ext_iff]]
    rw [Measure.prod_prod,geometricMeasure_singleton hp0,geometricMeasure_singleton hp0,
      ENNReal.ofReal_mul (geometricMeasure_nonneg p x.1)]
  have hpos (x : ℕ×ℕ) : Q {x} ≠ 0 := by
    rw [hatom, ne_eq,ENNReal.ofReal_eq_zero]
    exact (mul_pos (geometricMeasure_pos hp0 hp1 x.1) (geometricMeasure_pos hp0 hp1 x.2)).not_ge
  have hc (x : ℕ×ℕ) : -Real.log (Q {x}).toReal =
      ((x.1:ℝ)+(x.2:ℝ)) * (-Real.log (1-(p:ℝ))) - 2*Real.log (p:ℝ) := by
    rw [hatom,ENNReal.toReal_ofReal (mul_nonneg (geometricMeasure_nonneg p x.1)
      (geometricMeasure_nonneg p x.2)),Real.log_mul
      (geometricMeasure_pos hp0 hp1 x.1).ne' (geometricMeasure_pos hp0 hp1 x.2).ne',
      Real.log_mul (pow_pos hqR _).ne' hpR.ne',
      Real.log_mul (pow_pos hqR _).ne' hpR.ne',Real.log_pow,Real.log_pow]
    ring
  have hci : Integrable (fun x : ℕ×ℕ => -Real.log (Q {x}).toReal) P := by
    simp_rw [hc]
    exact (hi.mul_const _).sub (integrable_const _)
  have he := countable_entropy_le_crossEntropy P Q
    (countable_ac_of_atom P Q (fun x hx => False.elim (hpos x hx))) hci
  refine ⟨he.1,he.2.trans ?_⟩
  simp_rw [hc]
  rw [integral_sub (hi.mul_const _) (integrable_const _),integral_mul_const,integral_const,
    probReal_univ,one_smul]
  have hlp : -Real.log (p:ℝ) = Real.log (M+1) := by simp [p,Real.log_inv]
  have htpos : 0 < 1-(p:ℝ) := by
    change 0 < 1-(M+1)⁻¹
    linarith [(inv_lt_one₀ hM1).mpr (by linarith : 1 < M+1)]
  have hlog : -Real.log (1-(p:ℝ)) ≤ M⁻¹ := by
    have hrat : (1-(p:ℝ))⁻¹ = 1+M⁻¹ := by dsimp [p]; field_simp [hM0.ne',hM1.ne']; ring
    calc
      _ = Real.log ((1-(p:ℝ))⁻¹) := (Real.log_inv _).symm
      _ ≤ (1-(p:ℝ))⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
      _ = _ := by rw [hrat]; ring
  have hlog0 : 0 ≤ -Real.log (1-(p:ℝ)) := by
    apply neg_nonneg.mpr (Real.log_nonpos htpos.le _)
    have : 0 ≤ (p:ℝ) := p.2.1
    linarith
  have hb := mul_le_mul_of_nonneg_right hmean hlog0
  have hb' := mul_le_mul_of_nonneg_left hlog hM0.le
  rw [mul_inv_cancel₀ hM0.ne'] at hb'
  linarith

lemma entropy_finite_integrable {W : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure W) [IsProbabilityMeasure P] (h : shannonEntropy P ≠ ∞) :
    Integrable (fun w => -Real.log (P {w}).toReal) P :=
  (lintegral_ofReal_ne_top_iff_integrable (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (atom_surprisal_nonneg P))).mp h

lemma integral_surprisal {W : Type*} [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure W) [IsProbabilityMeasure P] :
    (∫ w, -Real.log (P {w}).toReal ∂P) = (shannonEntropy P).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (atom_surprisal_nonneg P))
    (measurable_of_countable _).aestronglyMeasurable

lemma shannonEntropy_subadd {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    [Countable W] [Countable E] [MeasurableSingletonClass W] [MeasurableSingletonClass E]
    (P : Measure (W×E)) [IsProbabilityMeasure P]
    (hW : shannonEntropy P.fst ≠ ∞) (hE : shannonEntropy P.snd ≠ ∞) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤
      (shannonEntropy P.fst).toReal + (shannonEntropy P.snd).toReal := by
  have hiW : Integrable (fun z : W×E => -Real.log (P.fst {z.1}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      measurable_fst.aemeasurable).mp (entropy_finite_integrable P.fst hW)
  have hiE : Integrable (fun z : W×E => -Real.log (P.snd {z.2}).toReal) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      measurable_snd.aemeasurable).mp (entropy_finite_integrable P.snd hE)
  have he : ∀ᵐ z ∂P, -Real.log ((P.fst.prod P.snd) {z}).toReal =
      -Real.log (P.fst {z.1}).toReal + -Real.log (P.snd {z.2}).toReal := by
    have hf := (ae_map_iff measurable_fst.aemeasurable
      ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.fst)
    have hs := (ae_map_iff measurable_snd.aemeasurable
      ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.snd)
    filter_upwards [hf,hs] with z hzf hzs
    rw [show ({z} : Set (W×E)) = {z.1} ×ˢ {z.2} by ext y; simp [Prod.ext_iff],
      Measure.prod_prod,ENNReal.toReal_mul,Real.log_mul
        (ENNReal.toReal_ne_zero.mpr ⟨hzf,measure_ne_top _ _⟩)
        (ENNReal.toReal_ne_zero.mpr ⟨hzs,measure_ne_top _ _⟩)]
    ring
  have hi : Integrable (fun z : W×E => -Real.log ((P.fst.prod P.snd) {z}).toReal) P :=
    (hiW.add hiE).congr (by filter_upwards [he] with z hz; exact hz.symm)
  obtain ⟨hfin,hineq⟩ := countable_entropy_le_crossEntropy P (P.fst.prod P.snd)
    (joint_ac_prod_marginals P) hi
  refine ⟨hfin,hineq.trans_eq ?_⟩
  rw [integral_congr_ae he,integral_add hiW hiE]
  have h1 : (∫ a : W×E, -Real.log (P.fst {a.1}).toReal ∂P) = (shannonEntropy P.fst).toReal := by
    rw [←integral_surprisal]
    exact (integral_map measurable_fst.aemeasurable (measurable_of_countable
      (fun w => -Real.log (P.fst {w}).toReal)).aestronglyMeasurable).symm
  have h2 : (∫ a : W×E, -Real.log (P.snd {a.2}).toReal ∂P) = (shannonEntropy P.snd).toReal := by
    rw [←integral_surprisal]
    exact (integral_map measurable_snd.aemeasurable (measurable_of_countable
      (fun w => -Real.log (P.snd {w}).toReal)).aestronglyMeasurable).symm
  rw [h1,h2]

lemma intCode_le (q : ℤ) : (Equiv.intEquivNat q : ℝ) ≤ 2 * (q.natAbs:ℝ) := by
  cases q with
  | ofNat n => change ((2*n:ℕ):ℝ) ≤ 2*(n:ℝ); norm_cast
  | negSucc n => change ((2*n+1:ℕ):ℝ) ≤ 2*((n+1:ℕ):ℝ); push_cast; linarith

def natIntEquivNatNat : (ℕ×ℤ) ≃ᵐ (ℕ×ℕ) where
  toEquiv := (Equiv.refl ℕ).prodCongr Equiv.intEquivNat
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

lemma natInt_entropy {P : Measure (ℕ×ℤ)} [IsProbabilityMeasure P]
    (M : ℝ) (hM : 1 ≤ M)
    (hi : Integrable (fun x : ℕ×ℤ => (x.1:ℝ)+2*(x.2.natAbs:ℝ)) P)
    (hmean : (∫ x : ℕ×ℤ, (x.1:ℝ)+2*(x.2.natAbs:ℝ) ∂P) ≤ M) :
    shannonEntropy P ≠ ∞ ∧ (shannonEntropy P).toReal ≤ 1 + 2 * Real.log (M+1) := by
  let e := natIntEquivNatNat
  let Q := P.map e
  let : IsProbabilityMeasure Q := inferInstance
  have hle (x : ℕ×ℤ) : ((e x).1:ℝ)+((e x).2:ℝ) ≤ (x.1:ℝ)+2*(x.2.natAbs:ℝ) :=
    add_le_add le_rfl (intCode_le x.2)
  have hi' : Integrable (fun x : ℕ×ℤ => ((e x).1:ℝ)+((e x).2:ℝ)) P := by
    apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact hle x)
  have hqi : Integrable (fun x : ℕ×ℕ => (x.1:ℝ)+(x.2:ℝ)) Q :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable e.measurable.aemeasurable).mpr hi'
  have hqm : (∫ x : ℕ×ℕ, (x.1:ℝ)+(x.2:ℝ) ∂Q) ≤ M := by
    rw [integral_map e.measurable.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    exact (integral_mono_ae hi' hi (Eventually.of_forall hle)).trans hmean
  have h := geometric_pair_entropy M hM hqi hqm
  simpa only [Q,shannonEntropy_equiv P e] using h



lemma map_fiber_ac_prod {A S Y : Type*} [MeasurableSpace A] [MeasurableSpace S]
    [MeasurableSpace Y] (μ : Measure A) (ν : Measure S) (L : Measure Y)
    [SFinite μ] [SFinite ν] [SFinite L]
    (f : A×S → Y) (hf : Measurable f)
    (hac : ∀ᵐ a ∂μ, ν.map (fun s => f (a,s)) ≪ L) :
    (μ.prod ν).map (fun z => (z.1,f z)) ≪ μ.prod L := by
  apply Measure.AbsolutelyContinuous.mk
  intro t ht ht0
  rw [Measure.prod_apply ht] at ht0
  have hz : ∀ᵐ a ∂μ, L {y | (a,y) ∈ t} = 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_left ht)).mp ht0
  rw [Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.prod_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply (lintegral_eq_zero_iff
    (measurable_measure_prodMk_left (ht.preimage (measurable_fst.prodMk hf)))).mpr
  filter_upwards [hac, hz] with a ha hza
  have hh := ha hza
  have ham : Measurable (fun s : S => f (a,s)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have has : MeasurableSet {y : Y | (a,y) ∈ t} :=
    ht.preimage (show Measurable (fun y : Y => (a,y)) from measurable_const.prodMk measurable_id)
  rw [Measure.map_apply ham has] at hh
  exact hh

lemma ae_condKernel_ac_of_joint_ac {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (P : Measure (A×Y)) [IsFiniteMeasure P]
    (R : Measure A) (L : Measure Y) [SFinite R] [SFinite L]
    (hac : P ≪ R.prod L) : ∀ᵐ a ∂P.fst, P.condKernel a ≪ L := by
  obtain ⟨L', hL', hLL', hL'L⟩ := exists_isFiniteMeasure_absolutelyContinuous L
  let := hL'
  have hh : P.fst ⊗ₘ P.condKernel ≪ R ⊗ₘ Kernel.const A L' := by
    rw [P.disintegrate P.condKernel, Measure.compProd_const]
    exact hac.trans ((Measure.AbsolutelyContinuous.refl R).prod hLL')
  filter_upwards [hh.kernel_of_compProd] with a ha
  exact ha.trans hL'L

lemma adjoin_countable_ac {A Y W : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (P : Measure ((A×Y)×W)) [IsFiniteMeasure P]
    (R : Measure A) (L : Measure Y) [SFinite R] [SFinite L]
    (hac : P.fst ≪ R.prod L) :
    P.map (swapLast : (A×Y)×W ≃ᵐ (A×W)×Y) ≪ (R.prod Measure.count).prod L := by
  have h := (joint_ac_fst_prod_count P).trans (hac.prod (Measure.AbsolutelyContinuous.refl (Measure.count : Measure W)))
  have hm := h.map (swapLast : (A×Y)×W ≃ᵐ (A×W)×Y).measurable
  rwa [map_swapLast_prod] at hm


lemma countable_null_transfer {A Y W : Type*} [MeasurableSpace A] [MeasurableSpace Y]
    [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W]
    (N : Measure ((A×W)×Y)) (R : Measure A) (L : Measure Y)
    [SFinite R] [SFinite L]
    (hac : N ≪ (R.prod Measure.count).prod L)
    (p : A → W → Y → Prop)
    (hpm : ∀ w, MeasurableSet {ay : A×Y | p ay.1 w ay.2})
    (hp : ∀ w a, ∀ᵐ y ∂L, p a w y) : ∀ᵐ z ∂N, p z.1.1 z.1.2 z.2 := by
  apply hac.ae_le
  have hm : MeasurableSet {z : (A×W)×Y | p z.1.1 z.1.2 z.2} := by
    have he : {z : (A×W)×Y | p z.1.1 z.1.2 z.2} =
      ⋃ w : W, {z : (A×W)×Y | z.1.2 = w} ∩
        (fun z : (A×W)×Y => (z.1.1,z.2)) ⁻¹' {ay | p ay.1 w ay.2} := by
      ext z; simp
    rw [he]
    exact MeasurableSet.iUnion fun w =>
      (measurableSet_eq_fun measurable_fst.snd measurable_const).inter
        ((hpm w).preimage (measurable_fst.fst.prodMk measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact Filter.Eventually.of_forall fun aw => hp aw.2 aw.1


lemma log_one_add_nonneg (x : ℝ≥0∞) : 0 ≤ Real.log (1+x.toReal) :=
  Real.log_nonneg (le_add_of_nonneg_right ENNReal.toReal_nonneg)

lemma log_one_add_le (x : ℝ≥0∞) : Real.log (1+x.toReal) ≤ x.toReal := by
  simpa using Real.log_le_sub_one_of_pos (show 0 < 1+x.toReal by positivity)

lemma measurable_log_one_add {A : Type*} [MeasurableSpace A] {f : A → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun x => Real.log (1+(f x).toReal)) :=
  (measurable_const.add hf.ennreal_toReal).log

lemma log_one_add_jensen {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ≥0∞)
    (hFm : Measurable F) (hFt : ∀ a, F a ≠ ∞)
    (hFin : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∫⁻ a, ENNReal.ofReal (Real.log (1+(F a).toReal)) ∂μ ≤
      ENNReal.ofReal (Real.log (1+(∫⁻ a, F a ∂μ).toReal)) := by
  have hFi : Integrable (fun a => (F a).toReal) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hFm.ennreal_toReal.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))).mp
    simpa only [ENNReal.ofReal_toReal (hFt _)] using hFin
  have hLi : Integrable (fun a => Real.log (1+(F a).toReal)) μ :=
    hFi.mono' (measurable_log_one_add hFm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_nonneg (log_one_add_nonneg _)]; exact log_one_add_le _)
  let M := 1+(∫⁻ a, F a ∂μ).toReal
  have hM : 0 < M := by dsimp [M]; positivity
  have htangent (a : A) : Real.log (1+(F a).toReal) ≤
      Real.log M + (1+(F a).toReal)/M - 1 := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < (1+(F a).toReal)/M by positivity)
    rw [Real.log_div (by positivity) hM.ne'] at hh
    linarith
  have hupper : Integrable (fun a => Real.log M + (1+(F a).toReal)/M - 1) μ :=
    ((integrable_const _).add (((integrable_const 1).add hFi).div_const M)).sub (integrable_const _)
  have hbound := integral_mono hLi hupper htangent
  have hmean : ∫ a, (1+(F a).toReal)/M ∂μ = 1 := by
    rw [integral_div, integral_add (integrable_const 1) hFi, integral_const,
      integral_toReal hFm.aemeasurable (Filter.Eventually.of_forall fun a => lt_top_iff_ne_top.mpr (hFt a))]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    exact div_self hM.ne'
  rw [integral_sub (f:=fun a => Real.log M+(1+(F a).toReal)/M) (g:=fun _ => 1)
    ((integrable_const _).add (((integrable_const 1).add hFi).div_const M))
    (integrable_const 1), integral_add (f:=fun _ => Real.log M) (g:=fun a => (1+(F a).toReal)/M)
    (integrable_const _) (((integrable_const 1).add hFi).div_const M),
    hmean, integral_const, integral_const] at hbound
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, add_sub_cancel_right] at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal hLi (Filter.Eventually.of_forall fun a => log_one_add_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbound


lemma exp_log_normalization (v : ℝ≥0∞) (hv : v ≠ ∞) (c : ℝ) (hc : 0 ≤ c) (q : ℕ) :
    ENNReal.ofReal (Real.exp ((q:ℝ)*Real.log (1+v.toReal)-(q:ℝ)*Real.log (1+c))) =
      (1+v)^q / (ENNReal.ofReal (1+c))^q := by
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by positivity), Real.exp_log (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_toReal hv]


lemma mixed_entropy_log_bound {A X Z : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [MeasurableSpace Z] (P : Measure (A×X)) [IsProbabilityMeasure P]
    (γ : Measure X) (η : Measure Z) [IsProbabilityMeasure γ] [IsProbabilityMeasure η]
    (hKL : klDiv P (P.fst.prod γ) ≠ ∞)
    (K : (A×X)×Z → ℝ≥0∞) (hKm : Measurable K) (hKt : ∀ z, K z ≠ ∞)
    (hKint : ∀ ax, ∫⁻ z, K (ax,z) ∂η ≠ ∞)
    (C : A → ℝ) (hCm : Measurable C) (hC0 : ∀ a, 0 ≤ C a)
    (hCI : Integrable (fun a => Real.log (1+C a)) P.fst)
    {q : ℕ} (hq : 1 ≤ q)
    (hMoment : ∀ a, ∫⁻ x, (∫⁻ z, K ((a,x),z) ∂η)^q ∂γ ≤ (ENNReal.ofReal (C a))^q) :
    ∫⁻ axz, ENNReal.ofReal (Real.log (1+(K axz).toReal)) ∂P.prod η ≤
      ENNReal.ofReal ((klDiv P (P.fst.prod γ)).toReal / q +
        ∫ a, Real.log (1+C a) ∂P.fst) := by
  let F : A×X → ℝ≥0∞ := fun ax => ∫⁻ z, K (ax,z) ∂η
  have hFm : Measurable F := Measurable.lintegral_prod_right (f:=fun ax z => K (ax,z)) hKm
  have hf : Measurable (fun ax : A×X => (q:ℝ)*Real.log (1+(F ax).toReal)) :=
    measurable_const.mul (measurable_log_one_add hFm)
  have hc : Measurable (fun ax : A×X => (q:ℝ)*Real.log (1+C ax.1)) :=
    measurable_const.mul ((measurable_const.add (hCm.comp measurable_fst)).log)
  have hCc : Integrable (fun ax : A×X => Real.log (1+C ax.1)) P :=
    (integrable_map_measure (measurable_const.add hCm |>.log.aestronglyMeasurable)
      measurable_fst.aemeasurable).mp hCI
  have hcI := hCc.const_mul (q:ℝ)
  have hExp : ∫⁻ ax : A×X, ENNReal.ofReal (Real.exp
      ((q:ℝ)*Real.log (1+(F ax).toReal)-(q:ℝ)*Real.log (1+C ax.1))) ∂P.fst.prod γ ≤ 1 := by
    rw [lintegral_prod (fun ax : A×X => ENNReal.ofReal (Real.exp
      ((q:ℝ)*Real.log (1+(F ax).toReal)-(q:ℝ)*Real.log (1+C ax.1))))
      (by exact (hf.sub hc).exp.ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ _a, (1:ℝ≥0∞) ∂P.fst := by
        apply lintegral_mono; intro a
        have heq : (fun x => ENNReal.ofReal (Real.exp
            ((q:ℝ)*Real.log (1+(F (a,x)).toReal)-(q:ℝ)*Real.log (1+C a)))) =
            (fun x => (1+F (a,x))^q / (ENNReal.ofReal (1+C a))^q) := by
          funext x
          exact exp_log_normalization _ (hKint (a,x)) _ (hC0 a) q
        change (∫⁻ x, ENNReal.ofReal (Real.exp
          ((q:ℝ)*Real.log (1+(F (a,x)).toReal)-(q:ℝ)*Real.log (1+C a))) ∂γ) ≤ 1
        rw [heq]
        simp_rw [div_eq_mul_inv]
        have hpow : Measurable (fun x : X => (1+F (a,x))^q) :=
          (measurable_const.add (hFm.comp (measurable_const.prodMk measurable_id))).pow_const q
        rw [lintegral_mul_const _ hpow]
        have hh := lintegral_one_add_pow_le γ (fun x => F (a,x))
          (hFm.comp (measurable_const.prodMk measurable_id)) hq (hMoment a)
        have he : ENNReal.ofReal (1+C a) = 1+ENNReal.ofReal (C a) := by
          rw [ENNReal.ofReal_add (by norm_num) (hC0 a), ENNReal.ofReal_one]
        rw [he]
        apply (mul_le_mul' hh le_rfl).trans_eq
        exact ENNReal.mul_inv_cancel (by positivity) (by finiteness)
      _ = 1 := by simp
  obtain ⟨hfi, hbi⟩ := entropy_exp_bound P (P.fst.prod γ) hKL _ _ hf hc
    (fun ax => mul_nonneg (Nat.cast_nonneg _) (log_one_add_nonneg _)) hcI hExp
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqne := hqpos.ne'
  have hLi : Integrable (fun ax => Real.log (1+(F ax).toReal)) P := by
    have hh := hfi.div_const (q:ℝ)
    simpa only [mul_div_cancel_left₀ _ hqne] using hh
  have hCeq : ∫ ax : A×X, Real.log (1+C ax.1) ∂P = ∫ a, Real.log (1+C a) ∂P.fst := by
    exact (integral_map measurable_fst.aemeasurable
      (measurable_const.add hCm |>.log.aestronglyMeasurable)).symm
  rw [integral_const_mul, integral_const_mul, hCeq] at hbi
  have hfinal : ∫ ax, Real.log (1+(F ax).toReal) ∂P ≤
      (klDiv P (P.fst.prod γ)).toReal / q + ∫ a, Real.log (1+C a) ∂P.fst := by
    rw [← sub_le_iff_le_add, le_div_iff₀ hqpos]
    nlinarith
  calc
    _ = ∫⁻ ax, ∫⁻ z, ENNReal.ofReal (Real.log (1+(K (ax,z)).toReal)) ∂η ∂P :=
      lintegral_prod _ (measurable_log_one_add hKm |>.ennreal_ofReal.aemeasurable)
    _ ≤ ∫⁻ ax, ENNReal.ofReal (Real.log (1+(F ax).toReal)) ∂P := by
      exact lintegral_mono fun ax => log_one_add_jensen η (fun z => K (ax,z))
        (hKm.comp (measurable_const.prodMk measurable_id)) (fun z => hKt (ax,z)) (hKint ax)
    _ = ENNReal.ofReal (∫ ax, Real.log (1+(F ax).toReal) ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hLi (Filter.Eventually.of_forall fun _ => log_one_add_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal



end CurrentProjection

end

end OAI
