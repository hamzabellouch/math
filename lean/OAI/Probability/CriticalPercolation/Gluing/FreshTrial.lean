import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def allOpen (F : Set E) : Set (Set E) := {ω | F⊆ω}

lemma measurable_allOpen_block [Countable E] (F : Set E) :
    MeasurableSet[blockSigma F] (allOpen F) := by
  have he : allOpen F=⋂ e : F, {ω : Set E | (e:E)∈ω} := by
    ext ω
    simp only [allOpen,Set.mem_ofPred_eq,Set.mem_iInter]
    exact ⟨fun h e => h e.property,fun h e he => h ⟨e,he⟩⟩
  rw [he]
  apply MeasurableSet.iInter
  intro e
  have hm : MeasurableSet[coordinateSigma (e:E)] {ω : Set E | (e:E)∈ω} :=
    ⟨{True},MeasurableSet.singleton _,by ext ω; simp⟩
  exact (le_iSup_of_le (e:E) (le_iSup_of_le e.property le_rfl) :
    coordinateSigma (e:E)≤blockSigma F) _ hm

lemma allOpen_inter_lower_le [Countable E] (q : E → unitInterval) (F : Set E)
    (B : Set (Set E)) (hB : MeasurableSet B) (hBl : IsLowerSet B) :
    (law q).real (allOpen F∩B)≤(law q).real (allOpen F)*(law q).real B := by
  let C := forceOn F Set.univ ⁻¹' B
  have hmC : MeasurableSet[blockSigma Fᶜ] C := hB.preimage (measurable_forceOn_block F _)
  have hi := ((independent_blocks q F).indepSet_of_measurableSet
    (measurable_allOpen_block F) hmC).measure_inter_eq_mul
  have he : allOpen F∩B=allOpen F∩C := by
    ext ω
    by_cases hω : F⊆ω
    · have hf : forceOn F Set.univ ω=ω := by
        ext e
        by_cases he : e∈F
        · simp only [mem_forceOn,ite_eq_left he,Set.mem_univ,true_iff]
          exact hω he
        · simp only [mem_forceOn,ite_eq_right he]
      simp only [Set.mem_inter_iff,allOpen,Set.mem_ofPred_eq,hω,true_and,C,Set.mem_preimage,hf]
    · simp only [Set.mem_inter_iff,allOpen,Set.mem_ofPred_eq,hω,false_and]
  have hsub : C⊆B := by
    intro ω hω
    apply hBl _ hω
    intro e he
    by_cases heF : e∈F <;> simp [heF,he]
  have hr : (law q).real (allOpen F∩B)=(law q).real (allOpen F)*(law q).real C := by
    simp only [measureReal_def,he,hi,ENNReal.toReal_mul]
  rw [hr]
  exact mul_le_mul_of_nonneg_left (measureReal_mono hsub) measureReal_nonneg

lemma integrable_blockProbability_real (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    Integrable (fun σ => (blockProbability q S A σ).toReal) (law q) := by
  have hm := (measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl
  apply (integrable_const (1:ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with σ
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (by simp) (blockProbability_le_one q S A σ)

lemma integral_blockProbability_real (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ σ, (blockProbability q S A σ).toReal ∂law q)=(law q).real A := by
  have hm := (measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl
  rw [integral_toReal hm.aemeasurable (ae_of_all _ (fun σ =>
    (blockProbability_le_one q S A σ).trans_lt ENNReal.one_lt_top)),
    lintegral_blockProbability q S A hA]
  rfl

theorem good_trial_bound [Countable E] (q : E → unitInterval) (S F : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hAu : IsUpperSet A)
    (η lam : ℝ) (hlam : 0<lam) (hmean : 1-η≤(law q).real A) :
    (law q).real (allOpen F∩{σ | (blockProbability q S A σ).toReal<1-lam})≤
      (law q).real (allOpen F)*η/lam := by
  let g : Set E → ℝ := fun σ => (blockProbability q S A σ).toReal
  let B : Set (Set E) := {σ | g σ<1-lam}
  have hg : Measurable g :=
    ((measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl).ennreal_toReal
  have hgi : Integrable g (law q) := integrable_blockProbability_real q S A hA
  have hg1 : ∀ σ, g σ≤1 := fun σ =>
    ENNReal.toReal_mono (by simp) (blockProbability_le_one q S A σ)
  have hgm : Monotone g := by
    intro σ τ h
    exact ENNReal.toReal_mono (ne_of_lt ((blockProbability_le_one q S A τ).trans_lt
      ENNReal.one_lt_top)) (blockProbability_monotone q S A hAu h)
  have hBm : MeasurableSet B := measurableSet_lt hg measurable_const
  have hBl : IsLowerSet B := fun _ _ h hB => (hgm h).trans_lt hB
  have hmark : lam*(law q).real B≤η := by
    have hcomp : Integrable (fun σ => lam*B.indicator (1 : Set E → ℝ) σ) (law q) :=
      ((integrable_const (1:ℝ)).indicator hBm).const_mul lam
    have hd : Integrable (fun σ => 1-g σ) (law q) := (integrable_const 1).sub hgi
    have hi := integral_mono hcomp hd (fun σ => by
      by_cases hσ : σ∈B
      · rw [Set.indicator_of_mem hσ]
        have hh : g σ<1-lam := hσ
        dsimp only [Pi.one_apply]
        linarith
      · rw [Set.indicator_of_notMem hσ,mul_zero]
        exact sub_nonneg.mpr (hg1 σ))
    rw [integral_const_mul,integral_indicator_one hBm,integral_sub (integrable_const 1) hgi,
      integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
    have he := integral_blockProbability_real q S A hA
    change (∫ σ, g σ ∂law q)=(law q).real A at he
    rw [he] at hi
    linarith
  have hh := allOpen_inter_lower_le q F B hBm hBl
  have hb : (law q).real B≤η/lam := (le_div_iff₀ hlam).mpr (by nlinarith [hmark])
  exact hh.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hb (show 0≤(law q).real (allOpen F) from measureReal_nonneg))

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
