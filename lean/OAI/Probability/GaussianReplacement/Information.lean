import OAI.Probability.GaussianReplacement.CriticalEntropy

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma klDiv_prod_chain {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (P : Measure (A×B)) [IsProbabilityMeasure P]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv P (μ.prod ν) = klDiv P.fst μ + klDiv P (P.fst.prod ν) := by
  have h := klDiv_compProd_eq_add P.fst μ P.condKernel (Kernel.const A ν)
  simpa only [P.disintegrate P.condKernel,Measure.compProd_const] using h

lemma mutualInformation_reference {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (P : Measure (A×B)) [IsProbabilityMeasure P]
    (μ : Measure A) [IsProbabilityMeasure μ] :
    klDiv P (μ.prod P.snd) = klDiv P.fst μ + mutualInformation P :=
  klDiv_prod_chain P μ P.snd

lemma klDiv_map_leftInverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (f : A → B) (g : B → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    klDiv (P.map f) (Q.map f) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q hf)
  have h := klDiv_map_le (P.map f) (Q.map f) hg
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf,he,Measure.map_id] using h

lemma mutualInformation_map_left {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure (A×B)) [IsProbabilityMeasure P]
    (f : A → C) (g : C → A) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    mutualInformation (P.map (Prod.map f id)) = mutualInformation P := by
  have hT : Measurable (Prod.map f (id : B → B)) := hf.prodMap measurable_id
  have hfst : (P.map (Prod.map f id)).fst = P.fst.map f := by
    simp only [Measure.fst,Measure.map_map measurable_fst hT,Measure.map_map hf measurable_fst]
    rfl
  have hsnd : (P.map (Prod.map f id)).snd = P.snd := by
    simp only [Measure.snd,Measure.map_map measurable_snd hT]
    rfl
  unfold mutualInformation
  have hRef : (P.fst.prod P.snd).map (Prod.map f id) = (P.fst.map f).prod P.snd := by
    rw [←Measure.map_prod_map _ _ hf measurable_id,Measure.map_id]
  rw [hfst,hsnd,←hRef]
  exact klDiv_map_leftInverse P (P.fst.prod P.snd) (Prod.map f id) (Prod.map g id)
    hT (hg.prodMap measurable_id) (fun x => by ext <;> simp [hgf x.1])

lemma mutualInformation_swap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) [IsProbabilityMeasure P] :
    mutualInformation (P.map Prod.swap) = mutualInformation P := by
  have hf : (P.map Prod.swap).fst = P.snd := by
    simp only [Measure.fst,Measure.snd,Measure.map_map measurable_fst measurable_swap]; rfl
  have hs : (P.map Prod.swap).snd = P.fst := by
    simp only [Measure.fst,Measure.snd,Measure.map_map measurable_snd measurable_swap]; rfl
  unfold mutualInformation
  rw [hf,hs,←Measure.prod_swap]
  exact klDiv_map_equiv P (P.fst.prod P.snd) MeasurableEquiv.prodComm

lemma mutualInformation_rows_chain {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    mutualInformation (P.map swapLast) = mutualInformation P.fst + rowInformation P γ := by
  have hSW : P.fst.fst = ν := by
    have h := congrArg Measure.fst hInd
    rw [Measure.fst_prod] at h
    convert h using 1
    simp only [Measure.fst,Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_fst measurable_fst,
      Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
    rfl
  have hW : (P.map swapLast).snd = P.fst.snd := by
    simp only [Measure.snd,Measure.fst,Measure.map_map measurable_snd swapLast.measurable,
      Measure.map_map measurable_snd measurable_fst]; rfl
  have h := klDiv_prod_chain P (ν.prod P.fst.snd) γ
  unfold mutualInformation rowInformation
  rw [hInd,hW,←map_swapLast_prod,klDiv_map_equiv,h,hSW]

lemma mutualInformation_independent_rows {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (γ : Measure X) [IsProbabilityMeasure γ] :
    mutualInformation ((P.prod γ).map swapLast) = mutualInformation P := by
  have hf : ((P.prod γ).map swapLast).fst = P.fst.prod γ := by
    rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable]
    change (P.prod γ).map (Prod.map Prod.fst id) = _
    rw [←Measure.map_prod_map P γ measurable_fst measurable_id,Measure.map_id]
    rfl
  have hs : ((P.prod γ).map swapLast).snd = P.snd := by
    rw [Measure.snd,Measure.map_map measurable_snd swapLast.measurable]
    change (P.prod γ).map (Prod.snd ∘ Prod.fst) = _
    rw [←Measure.map_map measurable_snd measurable_fst,←Measure.fst,Measure.fst_prod]
    rfl
  unfold mutualInformation
  rw [hf,hs,←map_swapLast_prod,klDiv_map_equiv]
  have h := klDiv_compProd_left P (P.fst.prod P.snd) (Kernel.const (S×W) γ)
  simpa only [Measure.compProd_const] using h

lemma mutualInformation_reference_comparison {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W]
    (P Q : Measure (Z×W)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hfst : P.fst = Q.fst) (hsnd : P.snd = Q.snd)
    (hPQ : klDiv P Q ≠ ∞) (hQR : klDiv Q (μ.prod Q.snd) ≠ ∞)
    (hi : Integrable (llr Q (μ.prod Q.snd)) P) :
    mutualInformation P ≠ ∞ ∧ mutualInformation Q ≠ ∞ ∧
      (mutualInformation P).toReal = (mutualInformation Q).toReal + (klDiv P Q).toReal +
        (∫ z, llr Q (μ.prod Q.snd) z ∂P) - (∫ z, llr Q (μ.prod Q.snd) z ∂Q) := by
  obtain ⟨hPR,hchain⟩ := klDiv_chain_finite P Q (μ.prod Q.snd) hPQ
    (klDiv_ne_top_iff.mp hQR).1 hi
  have hP := mutualInformation_reference P μ
  have hQ := mutualInformation_reference Q μ
  rw [hsnd,hfst] at hP
  have hbase : klDiv Q.fst μ ≠ ∞ := by
    exact ne_top_of_le_ne_top hQR (hQ ▸ le_add_right le_rfl)
  have hMP : mutualInformation P ≠ ∞ := by
    exact ne_top_of_le_ne_top hPR (hP ▸ le_add_left le_rfl)
  have hMQ : mutualInformation Q ≠ ∞ := by
    exact ne_top_of_le_ne_top hQR (hQ ▸ le_add_left le_rfl)
  refine ⟨hMP,hMQ,?_⟩
  have hP' := congrArg ENNReal.toReal hP
  have hQ' := congrArg ENNReal.toReal hQ
  rw [ENNReal.toReal_add hbase hMP] at hP'
  rw [ENNReal.toReal_add hbase hMQ] at hQ'
  have hQR' : (klDiv Q (μ.prod Q.snd)).toReal = ∫ z, llr Q (μ.prod Q.snd) z ∂Q := by
    exact toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.mp hQR).1 (by simp)
  rw [hQR'] at hQ'
  linarith





lemma density_mutualInformation_comparison {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W]
    (P Q : Measure (Z×W)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Λ : Measure Z) [SigmaFinite Λ] (g : Z → ℝ) (hg : Measurable g) (hgpos : ∀ z, 0<g z)
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hμ : Λ.withDensity (fun z => ENNReal.ofReal (g z)) = μ)
    (p : Z×W → ℝ≥0∞) (hp : Measurable p)
    (hQ : (Λ.prod Q.snd).withDensity p = Q)
    (hfst : P.fst = Q.fst) (hsnd : P.snd = Q.snd) (hPQ : klDiv P Q ≠ ∞)
    (hpP : Integrable (fun z => logPositive (p z)) P)
    (hpQ : Integrable (fun z => logPositive (p z)) Q)
    (hgQ : Integrable (fun z => Real.log (g z)) Q.fst) :
    Integrable (fun z => Real.log (p z).toReal) P ∧
    Integrable (fun z => Real.log (p z).toReal) Q ∧
    mutualInformation P ≠ ∞ ∧ mutualInformation Q ≠ ∞ ∧
    (mutualInformation P).toReal = (mutualInformation Q).toReal + (klDiv P Q).toReal +
      (∫ z, Real.log (p z).toReal ∂P) - (∫ z, Real.log (p z).toReal ∂Q) := by
  let R := μ.prod Q.snd
  have hR : (Λ.prod Q.snd).withDensity (fun z => ENNReal.ofReal (g z.1)) = R := by
    rw [←prod_withDensity_left hg.ennreal_ofReal,hμ]
  obtain ⟨hQR,he⟩ := llr_of_two_densities Q R (Λ.prod Q.snd) p hp hQ
    (fun z => g z.1) (hg.comp measurable_fst) (fun z => hgpos z.1) hR
  have hPQac := (klDiv_ne_top_iff.mp hPQ).1
  have heP := hPQac.ae_le he
  have hgiQ : Integrable (fun z : Z×W => Real.log (g z.1)) Q :=
    (integrable_map_measure hg.log.aestronglyMeasurable measurable_fst.aemeasurable).mp hgQ
  have hgiP : Integrable (fun z : Z×W => Real.log (g z.1)) P :=
    (integrable_map_measure hg.log.aestronglyMeasurable measurable_fst.aemeasurable).mp (by change Integrable _ P.fst; rw [hfst]; exact hgQ)
  have huP : Integrable (fun z => logPositive (p z) - Real.log (g z.1)) P := hpP.sub hgiP
  have huQ : Integrable (fun z => logPositive (p z) - Real.log (g z.1)) Q := hpQ.sub hgiQ
  have hleP : ∀ᵐ z ∂P, llr Q R z ≤ logPositive (p z) - Real.log (g z.1) := by
    filter_upwards [heP] with z hz
    rw [hz]
    exact sub_le_sub_right (le_max_left _ _) _
  have hleQ : ∀ᵐ z ∂Q, llr Q R z ≤ logPositive (p z) - Real.log (g z.1) := by
    filter_upwards [he] with z hz
    rw [hz]
    exact sub_le_sub_right (le_max_left _ _) _
  obtain ⟨hcP,_⟩ := cross_llr_integrable P Q R hPQ hQR _ huP hleP
  obtain ⟨hcQ,hQRfinite⟩ := cross_llr_integrable Q Q R (by simp) hQR _ huQ hleQ
  have hpPi : Integrable (fun z => Real.log (p z).toReal) P := by
    apply (hcP.add hgiP).congr
    filter_upwards [heP] with z hz
    simp only [Pi.add_apply,hz]
    ring
  have hpQi : Integrable (fun z => Real.log (p z).toReal) Q := by
    apply (hcQ.add hgiQ).congr
    filter_upwards [he] with z hz
    simp only [Pi.add_apply,hz]
    ring
  obtain ⟨hMP,hMQ,hinfo⟩ := mutualInformation_reference_comparison P Q μ hfst hsnd hPQ hQRfinite hcP
  refine ⟨hpPi,hpQi,hMP,hMQ,?_⟩
  have hgint : (∫ z : Z×W, Real.log (g z.1) ∂P) = ∫ z : Z×W, Real.log (g z.1) ∂Q := by
    rw [←integral_map measurable_fst.aemeasurable hg.log.aestronglyMeasurable,
      ←integral_map measurable_fst.aemeasurable hg.log.aestronglyMeasurable]
    change (∫ z, Real.log (g z) ∂P.fst) = ∫ z, Real.log (g z) ∂Q.fst
    rw [hfst]
  change _ = _ + _ + (∫ z, llr Q R z ∂P) - (∫ z, llr Q R z ∂Q) at hinfo
  rw [integral_congr_ae heP,integral_congr_ae he,
    integral_sub hpPi hgiP,integral_sub hpQi hgiQ,hgint] at hinfo
  linarith



def observedMessageMap {d k : ℕ} {W : Type*} (p : (Sphere d×W)×Rows k d) :
    (Rows k d×(Fin k→ℝ))×W := ((p.2,label p.2 (p.1.1:Vector d)),p.1.2)

lemma measurable_observedMessageMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (observedMessageMap (d:=d) (k:=k) (W:=W)) :=
  ((measurable_exposedJointMap (d:=d) (k:=k) (W:=W)).fst).prodMk measurable_fst.snd

def observedMessage {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : Measure ((Rows k d×(Fin k→ℝ))×W) :=
  P.map observedMessageMap

instance observedMessage_probability {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (observedMessage P) := by
  unfold observedMessage
  infer_instance

lemma observedMessage_snd {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : (observedMessage P).snd = P.fst.snd := by
  simp only [observedMessage,Measure.snd,Measure.fst,
    Measure.map_map measurable_snd measurable_observedMessageMap,
    Measure.map_map measurable_snd measurable_fst]
  rfl

lemma exposedInformation_chain {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P] :
    mutualInformation (P.map swapLast) = mutualInformation (observedMessage P) + exposedInformation P := by
  let f : Sphere d×Rows k d → (Rows k d×(Fin k→ℝ))×Sphere d :=
    fun z => ((z.2,label z.2 (z.1:Vector d)),z.1)
  let g : ((Rows k d×(Fin k→ℝ))×Sphere d) → Sphere d×Rows k d := fun z => (z.2,z.1.1)
  have hf : Measurable f := by
    have hy : Measurable (fun z : Sphere d×Rows k d => label z.2 (z.1:Vector d)) :=
      measurable_own_label.comp measurable_swap
    exact (measurable_snd.prodMk hy).prodMk measurable_fst
  have hg : Measurable g := measurable_snd.prodMk measurable_fst.fst
  let R := P.map exposedJointMap
  let : IsProbabilityMeasure R := inferInstance
  let : IsProbabilityMeasure (P.map (swapLast : (Sphere d×W)×Rows k d ≃ᵐ _)) :=
    inferInstance
  have hleft : R.map MeasurableEquiv.prodAssoc.symm = (P.map swapLast).map (Prod.map f id) := by
    rw [Measure.map_map (hf.prodMap measurable_id) swapLast.measurable]
    dsimp only [R]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable measurable_exposedJointMap]
    rfl
  have hright : R.map (Prod.map id Prod.snd) = observedMessage P := by
    dsimp only [R,observedMessage]
    rw [Measure.map_map (measurable_id.prodMap measurable_snd) measurable_exposedJointMap]
    rfl
  have h := mutualInformation_chain R
  rw [hleft,mutualInformation_map_left _ f g hf hg (fun _ => rfl),hright] at h
  exact h

lemma observedMessage_fst_of_independence {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) (γ : Measure (Rows k d))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    (observedMessage P).fst = projectionJoint ν γ := by
  have hbase : P.map (fun p : (Sphere d×W)×Rows k d => (p.2,p.1.1)) = γ.prod ν := by
    have h := congrArg (fun μ : Measure (Sphere d×Rows k d) => μ.map Prod.swap) hInd
    rw [Measure.prod_swap,Measure.fst,Measure.map_map measurable_swap measurable_fst,
      Measure.map_map (measurable_swap.comp measurable_fst) swapLast.measurable] at h
    exact h
  rw [projectionJoint,←hbase,
    Measure.map_map (measurable_fst.prodMk measurable_own_label) (measurable_snd.prodMk measurable_fst.fst)]
  rw [observedMessage,Measure.fst,Measure.map_map measurable_fst measurable_observedMessageMap]
  rfl




lemma prod_posterior_map {S W G Z : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] [MeasurableSpace Z] [StandardBorelSpace S] [Nonempty S]
    (P : Measure (S×W)) [IsProbabilityMeasure P] (γ : Measure G) [IsProbabilityMeasure γ]
    (f : S×G → Z) (hf : Measurable f) :
    (P.prod γ).map (fun p => (f (p.1.1,p.2),p.1.2)) =
      (P.snd ⊗ₘ ((messagePosterior P ×ₖ Kernel.const W γ).map f)).map Prod.swap := by
  let κ := messagePosterior P
  have hpost : P.snd ⊗ₘ κ = P.map Prod.swap := by
    have h := congrArg (fun μ : Measure (S×W) => μ.map Prod.swap) (messagePosterior_disintegrate P)
    rw [Measure.map_map measurable_swap measurable_swap] at h
    simpa only [show (Prod.swap ∘ Prod.swap : W×S → W×S) = id from rfl,Measure.map_id] using h
  have hbase : (P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ)).map MeasurableEquiv.prodAssoc.symm =
      (P.map Prod.swap).prod γ := by
    rw [compProd_prod_assoc,hpost]
    have hc : (Kernel.const W γ).comap (Prod.fst : W×S → W) measurable_fst =
        Kernel.const (W×S) γ := by ext x t ht; rfl
    rw [hc,Measure.compProd_const]
  have hbase' : P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ) =
      ((P.map Prod.swap).prod γ).map MeasurableEquiv.prodAssoc := by
    rw [←hbase,MeasurableEquiv.map_map_symm]
  rw [Measure.compProd_map hf]
  change _ = ((P.snd ⊗ₘ (κ ×ₖ Kernel.const W γ)).map (Prod.map id f)).map Prod.swap
  rw [hbase',Measure.map_map (measurable_id.prodMap hf) MeasurableEquiv.prodAssoc.measurable,
    Measure.map_map measurable_swap ((measurable_id.prodMap hf).comp MeasurableEquiv.prodAssoc.measurable)]
  have hp : (P.map Prod.swap).prod γ = (P.prod γ).map (Prod.map Prod.swap id) := by
    rw [←Measure.map_prod_map _ _ measurable_swap measurable_id,Measure.map_id]
  rw [hp,Measure.map_map (measurable_swap.comp ((measurable_id.prodMap hf).comp MeasurableEquiv.prodAssoc.measurable))
    (measurable_swap.prodMap measurable_id)]
  rfl

lemma swapped_compProd_withDensity {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (π : Measure W) (Λ : Measure Z) [SFinite π] [SFinite Λ]
    (κ : Kernel W Z) [IsSFiniteKernel κ] (p : Z×W → ℝ≥0∞) (hp : Measurable p)
    (h : ∀ᵐ w ∂π, Λ.withDensity (fun z => p (z,w)) = κ w) :
    (Λ.prod π).withDensity p = (π ⊗ₘ κ).map Prod.swap := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,
    lintegral_prod_symm _ (hp.indicator ht).aemeasurable,
    Measure.map_apply measurable_swap ht,Measure.compProd_apply (ht.preimage measurable_swap)]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  change _ = κ w ((fun z : Z => (z,w)) ⁻¹' t)
  have ht' : MeasurableSet ((fun z : Z => (z,w)) ⁻¹' t) :=
    ht.preimage (measurable_id.prodMk measurable_const)
  rw [←hw,withDensity_apply _ ht',←lintegral_indicator ht']
  rfl

def posteriorProjectionKernel {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) : Kernel W (Rows k d×(Fin k→ℝ)) :=
  (messagePosterior P ×ₖ Kernel.const W γ).map
    (fun z : Sphere d×Rows k d => (z.2,label z.2 (z.1:Vector d)))

lemma measurable_posteriorProjectionMap {d k : ℕ} :
    Measurable (fun z : Sphere d×Rows k d => (z.2,label z.2 (z.1:Vector d))) :=
  measurable_snd.prodMk (measurable_own_label.comp measurable_swap)

instance posteriorProjectionKernel_markov {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) [IsProbabilityMeasure γ] : IsMarkovKernel (posteriorProjectionKernel P γ) :=
  Kernel.IsMarkovKernel.map _ measurable_posteriorProjectionMap

lemma posteriorProjectionKernel_apply {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) [SFinite γ] (w : W) :
    posteriorProjectionKernel P γ w = projectionJoint (messagePosterior P w) γ := by
  rw [posteriorProjectionKernel,Kernel.map_apply _ measurable_posteriorProjectionMap,
    Kernel.prod_apply,Kernel.const_apply,projectionJoint,←Measure.prod_swap]
  rw [Measure.map_map measurable_posteriorProjectionMap measurable_swap]
  rfl

lemma observedMessage_independent_disintegrate {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    (γ : Measure (Rows k d)) [IsProbabilityMeasure γ] :
    observedMessage (P.prod γ) = (P.snd ⊗ₘ posteriorProjectionKernel P γ).map Prod.swap :=
  prod_posterior_map P γ _ measurable_posteriorProjectionMap

lemma observedMessage_independent_density {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P]
    (γ : Measure (Rows k d)) [IsProbabilityMeasure γ]
    (hAC : ∀ᵐ w ∂P.snd, ∀ᵐ G ∂γ, labelLaw (messagePosterior P w) G ≪ volume) :
    ((γ.prod (volume : Measure (Fin k→ℝ))).prod P.snd).withDensity
      (fun z => exactDensity (messagePosterior P z.2) z.1.1 z.1.2) =
        observedMessage (P.prod γ) := by
  rw [observedMessage_independent_disintegrate]
  apply swapped_compProd_withDensity
  · exact measurable_from_prod_countable_left (fun w => measurable_exactDensity (messagePosterior P w))
  · filter_upwards [hAC] with w hw
    rw [posteriorProjectionKernel_apply]
    exact projectionJoint_withDensity (messagePosterior P w) γ hw



lemma criticalPosterior_probability {d ℓ j : ℕ} (F : Measure (Sphere d))
    [IsProbabilityMeasure F] (q : ℤ) (hη : 0 < F (criticalClass F ℓ j q)) :
    IsProbabilityMeasure (criticalPosterior F ℓ j q) := by
  constructor
  change (F (criticalClass F ℓ j q))⁻¹ * (F.restrict (criticalClass F ℓ j q)) Set.univ = 1
  simp only [Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hη.ne' (measure_ne_top F _)

lemma criticalPosterior_ae_class {d ℓ j : ℕ} (F : Measure (Sphere d))
    [IsFiniteMeasure F] (q : ℤ) :
    ∀ᵐ s ∂criticalPosterior F ℓ j q, s ∈ criticalClass F ℓ j q := by
  exact (Measure.smul_absolutelyContinuous).ae_le (ae_restrict_mem (measurableSet_criticalClass F ℓ j q))

lemma criticalPosterior_cover_entropy {d n ℓ j : ℕ} (F : Measure (Sphere d))
    [IsProbabilityMeasure F] (D : ℝ) (hD : 0 ≤ D) (hF : LocalGrowth F n D)
    (hℓ : ℓ < n) (q : ℤ) (hη : 0 < F (criticalClass F ℓ j q))
    (hAC : ∀ᵐ G ∂gaussianRows ℓ d, labelLaw (criticalPosterior F ℓ j q) G ≪ volume)
    (hpos : Integrable (fun z : Rows ℓ d×Sphere d =>
      logPositive (exactDensity (criticalPosterior F ℓ j q) z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows ℓ d).prod (criticalPosterior F ℓ j q))) :
    Integrable (fun z : Rows ℓ d×Sphere d =>
      Real.log (exactDensity (criticalPosterior F ℓ j q) z.1 (label z.1 (z.2:Vector d))).toReal)
      ((gaussianRows ℓ d).prod (criticalPosterior F ℓ j q)) ∧
    -(∫ z : Rows ℓ d×Sphere d,
      Real.log (exactDensity (criticalPosterior F ℓ j q) z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows ℓ d).prod (criticalPosterior F ℓ j q)) ≤ 1 + 5*(ℓ:ℝ) - q := by
  let := criticalPosterior_probability F q hη
  obtain ⟨C,hsub,hcard,hcover⟩ := criticalClass_cover F D hD hF hℓ q
  have hC : C.Nonempty := by
    obtain ⟨x,hx⟩ := nonempty_of_measure_ne_zero hη.ne'
    obtain ⟨y,hy,_⟩ := hcover x hx
    exact ⟨y,hy⟩
  have hc : ∀ᵐ s ∂criticalPosterior F ℓ j q, ∃ c∈C, dist s c ≤ 2*criticalRadius j :=
    (criticalPosterior_ae_class F q).mono (fun s hs => hcover s hs)
  obtain ⟨hi,hb⟩ := projection_cover_entropy (criticalPosterior F ℓ j q) hAC hpos hC
    (criticalRadius_pos j) hc
  refine ⟨hi,hb.trans ?_⟩
  have hl := Real.log_le_log (show (0:ℝ) < C.card by exact_mod_cast hC.card_pos) hcard
  rw [Real.log_div (Real.exp_pos _).ne' (pow_pos (criticalRadius_pos j) _).ne',
    Real.log_exp,Real.log_pow] at hl
  linarith



lemma projection_positive_reference {d k : ℕ} [Nonempty (Sphere d)]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν] :
    ∃ g : Rows k d×(Fin k→ℝ) → ℝ, Measurable g ∧ (∀ z, 0<g z) ∧
      IsProbabilityMeasure (((gaussianRows k d).prod (volume : Measure (Fin k→ℝ))).withDensity
        (fun z => ENNReal.ofReal (g z))) ∧
      Integrable (fun z => Real.log (g z)) (projectionJoint ν (gaussianRows k d)) := by
  classical
  let c : Sphere d := Classical.choice inferInstance
  let C : Finset (Sphere d) := {c}
  have hC : C.Nonempty := Finset.singleton_nonempty _
  let g : Rows k d×(Fin k→ℝ) → ℝ := fun z => coverPDF C 1 z.1 z.2
  have hg : Measurable g := measurable_coverPDF C 1
  refine ⟨g,hg,fun z => coverPDF_pos hC (by norm_num) z.1 z.2,?_,?_⟩
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      lintegral_prod _ hg.ennreal_ofReal.aemeasurable]
    simp only [g,lintegral_coverPDF hC (by norm_num : (0:ℝ)<1),lintegral_const,measure_univ,mul_one]
  · exact (integrable_map_measure hg.log.aestronglyMeasurable
      (measurable_fst.prodMk measurable_own_label).aemeasurable).mpr
        (log_coverPDF_joint_integrable ν hC (by norm_num))

lemma independent_rows_signal {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (γ : Measure G) [IsProbabilityMeasure γ] :
    ((P.prod γ).map swapLast).fst = P.fst.prod γ := by
  rw [Measure.fst,Measure.map_map measurable_fst swapLast.measurable]
  change (P.prod γ).map (Prod.map Prod.fst id) = _
  rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
  rfl

lemma swapLast_snd {S W G : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace G] (P : Measure ((S×W)×G)) : (P.map swapLast).snd = P.fst.snd := by
  rw [Measure.snd,Measure.fst,Measure.snd,Measure.map_map measurable_snd swapLast.measurable,
    Measure.map_map measurable_snd measurable_fst]
  rfl



lemma exposedInformation_density_comparison {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty W] [Nonempty (Sphere d)]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows k d))
    (hH : shannonEntropy P.fst.snd ≠ ∞)
    (hAC : ∀ᵐ w ∂P.fst.snd, ∀ᵐ G ∂gaussianRows k d, labelLaw (messagePosterior P.fst w) G ≪ volume)
    (hpP : Integrable (fun z => logPositive (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2))
      (observedMessage P))
    (hpQ : Integrable (fun z => logPositive (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2))
      (observedMessage (P.fst.prod (gaussianRows k d)))) :
    Integrable (fun z => Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal)
      (observedMessage P) ∧
    Integrable (fun z => Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal)
      (observedMessage (P.fst.prod (gaussianRows k d))) ∧
    exposedInformation P ≠ ∞ ∧ exposedInformation (P.fst.prod (gaussianRows k d)) ≠ ∞ ∧
    (exposedInformation (P.fst.prod (gaussianRows k d))).toReal ≤ (exposedInformation P).toReal +
      (∫ z, Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal ∂observedMessage P) -
      (∫ z, Real.log (exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2).toReal
        ∂observedMessage (P.fst.prod (gaussianRows k d))) := by
  let : IsProbabilityMeasure (P.map (swapLast : (Sphere d×W)×Rows k d ≃ᵐ _)) :=
    inferInstance
  let γ := gaussianRows k d
  let Q := P.fst.prod γ
  let O := observedMessage P
  let R := observedMessage Q
  have hs : P.fst.fst = ν := by
    have hh := congrArg Measure.fst hInd
    rw [Measure.fst_prod] at hh
    convert hh using 1
    simp only [Measure.fst,Measure.map_map measurable_fst measurable_fst,
      Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_fst (measurable_fst.comp swapLast.measurable)]
    rfl
  have hQI : (Q.map swapLast).fst = ν.prod γ := by rw [independent_rows_signal,hs]
  have hOf : O.fst = projectionJoint ν γ := observedMessage_fst_of_independence P ν γ hInd
  have hRf : R.fst = projectionJoint ν γ := observedMessage_fst_of_independence Q ν γ hQI
  have hfs : O.fst = R.fst := hOf.trans hRf.symm
  have hss : O.snd = R.snd := by simp only [O,R,Q,observedMessage_snd,Measure.fst_prod]
  obtain ⟨hk,_⟩ := rowInformation_le_entropy P ν γ hInd (by simpa only [swapLast_snd] using hH)
  have hDPI : klDiv O R ≤ rowInformation P γ := klDiv_map_le P Q measurable_observedMessageMap
  have hOR : klDiv O R ≠ ∞ := ne_top_of_le_ne_top hk hDPI
  let p : (Rows k d×(Fin k→ℝ))×W → ℝ≥0∞ :=
    fun z => exactDensity (messagePosterior P.fst z.2) z.1.1 z.1.2
  have hp : Measurable p := measurable_from_prod_countable_left (fun w => measurable_exactDensity (messagePosterior P.fst w))
  have hdens : ((γ.prod (volume : Measure (Fin k→ℝ))).prod R.snd).withDensity p = R := by
    dsimp only [R,Q]
    rw [observedMessage_snd,Measure.fst_prod]
    exact observedMessage_independent_density P.fst γ hAC
  obtain ⟨g,hg,hgp,hprob,hgi⟩ := projection_positive_reference (k:=k) ν
  let μ := (γ.prod (volume : Measure (Fin k→ℝ))).withDensity (fun z => ENNReal.ofReal (g z))
  let : IsProbabilityMeasure μ := hprob
  obtain ⟨hiP,hiQ,hMP,hMQ,heq⟩ := density_mutualInformation_comparison O R
    (γ.prod volume) g hg hgp μ rfl p hp hdens hfs hss hOR hpP hpQ (by rwa [hRf])
  have hinput : mutualInformation (P.map swapLast) ≠ ∞ :=
    (countable_information_le_entropy _ (by simpa only [swapLast_snd] using hH)).1
  have hinputQ : mutualInformation (Q.map swapLast) ≠ ∞ := by
    rw [mutualInformation_independent_rows]
    exact (countable_information_le_entropy _ hH).1
  have hchainP := exposedInformation_chain P
  have hchainQ := exposedInformation_chain Q
  have hJP : exposedInformation P ≠ ∞ := ne_top_of_le_ne_top hinput (hchainP ▸ le_add_left le_rfl)
  have hJQ : exposedInformation Q ≠ ∞ := ne_top_of_le_ne_top hinputQ (hchainQ ▸ le_add_left le_rfl)
  refine ⟨hiP,hiQ,hJP,hJQ,?_⟩
  have hinputEq : mutualInformation (P.map swapLast) = mutualInformation (Q.map swapLast) + rowInformation P γ := by
    rw [mutualInformation_independent_rows]
    exact mutualInformation_rows_chain P ν γ hInd
  have he := congrArg ENNReal.toReal hinputEq
  rw [ENNReal.toReal_add hinputQ hk] at he
  have heP := congrArg ENNReal.toReal hchainP
  have heQ := congrArg ENNReal.toReal hchainQ
  rw [ENNReal.toReal_add hMP hJP] at heP
  rw [ENNReal.toReal_add hMQ hJQ] at heQ
  have hb := ENNReal.toReal_mono hk hDPI
  linarith



end CurrentProjection

end

end OAI
