import OAI.Probability.GaussianReplacement.ActualRow

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory




def conditionalMutualInformation {Z A B : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure (Z×(A×B))) [IsFiniteMeasure P] : ℝ≥0∞ := by
  classical
  exact if h : Nonempty (A×B) then
    letI := h
    InformationTheory.klDiv P (P.fst ⊗ₘ (P.condKernel.fst ×ₖ P.condKernel.snd))
  else 0

lemma kernel_prod_eq_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel Z A) (η : Kernel Z B) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ×ₖ η = κ ⊗ₖ η.comap Prod.fst measurable_fst := by
  ext z s hs
  rw [Kernel.prod_apply' _ _ _ hs, Kernel.compProd_apply hs]
  rfl

lemma compProd_prod_assoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z A) (η : Kernel Z B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ (κ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm =
      (μ ⊗ₘ κ) ⊗ₘ η.comap Prod.fst measurable_fst := by
  rw [kernel_prod_eq_compProd, Measure.compProd_assoc]

def swapAssoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] :
    Z×(A×B) ≃ᵐ (Z×B)×A :=
  ((MeasurableEquiv.refl Z).prodCongr MeasurableEquiv.prodComm).trans MeasurableEquiv.prodAssoc.symm

lemma compProd_prod_swapAssoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z A) (η : Kernel Z B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ (κ ×ₖ η)).map swapAssoc = (μ ⊗ₘ η) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  change (μ ⊗ₘ (κ ×ₖ η)).map (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap) = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap), ← Measure.compProd_map measurable_swap,
    Kernel.map_prod_swap, compProd_prod_assoc]

lemma fst_map_swapAssoc_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z (A×B)) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map swapAssoc).fst = μ ⊗ₘ κ.snd := by
  rw [Kernel.snd_eq]
  rw [Measure.compProd_map measurable_snd]
  rw [Measure.fst, Measure.map_map measurable_fst swapAssoc.measurable]
  rfl



lemma conditionalKL_chain {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [Nonempty A]
    (μ : Measure Z) [IsProbabilityMeasure μ] (κ : Kernel Z (A×B)) [IsMarkovKernel κ]
    (π : Measure B) [IsProbabilityMeasure π] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z π)) =
      klDiv (μ ⊗ₘ κ.snd) (μ.prod π) +
      klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  let R := (μ ⊗ₘ κ).map swapAssoc
  have hR : R.fst = μ ⊗ₘ κ.snd := fst_map_swapAssoc_compProd μ κ
  have hchain := klDiv_compProd_eq_add R.fst (μ.prod π) R.condKernel
    (κ.fst.comap Prod.fst measurable_fst)
  rw [R.disintegrate R.condKernel, hR] at hchain
  have hleft := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z π)) swapAssoc
  rw [compProd_prod_swapAssoc, Measure.compProd_const] at hleft
  have hright := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) swapAssoc
  rw [compProd_prod_swapAssoc] at hright
  exact hleft.symm.trans (hchain.trans (congrArg (klDiv (μ ⊗ₘ κ.snd) (μ.prod π) + ·) hright))


def mutualInformation {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) : ℝ≥0∞ := klDiv P (P.fst.prod P.snd)

lemma fst_map_assoc_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z (A×B)) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map MeasurableEquiv.prodAssoc.symm).fst = μ ⊗ₘ κ.fst := by
  rw [Kernel.fst_eq, Measure.compProd_map measurable_fst, Measure.fst,
    Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

lemma mutualInformation_chain {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] :
    mutualInformation (P.map MeasurableEquiv.prodAssoc.symm) =
      mutualInformation (P.map (Prod.map id Prod.snd)) + conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let Q := P.map MeasurableEquiv.prodAssoc.symm
  let R := P.map (Prod.map id Prod.snd)
  let : IsProbabilityMeasure Q := inferInstance
  let : IsProbabilityMeasure R := inferInstance
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hQ : Q.fst = μ ⊗ₘ κ.fst := by
    change (P.map MeasurableEquiv.prodAssoc.symm).fst = _
    rw [← hP]
    exact fst_map_assoc_compProd μ κ
  have hR : R = μ ⊗ₘ κ.snd := by
    rw [Kernel.snd_eq,Measure.compProd_map measurable_snd,hP]
  have hRf : R.fst = μ := by rw [hR,Measure.fst_compProd]
  have hRs : R.snd = Q.snd := by
    dsimp only [R,Q,Measure.snd]
    rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd),
      Measure.map_map measurable_snd MeasurableEquiv.prodAssoc.symm.measurable]
    rfl
  have hleft := klDiv_map_equiv P (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z Q.snd)) MeasurableEquiv.prodAssoc.symm
  rw [compProd_prod_assoc] at hleft
  have hconst : (Kernel.const Z Q.snd).comap (Prod.fst : Z×A → Z) measurable_fst =
      Kernel.const (Z×A) Q.snd := by ext x t ht; rfl
  rw [hconst,Measure.compProd_const,← hQ] at hleft
  have hc := conditionalKL_chain μ κ Q.snd
  have hSmall : klDiv (μ ⊗ₘ κ.snd) (μ.prod Q.snd) = mutualInformation R := by
    rw [← hR,← hRf,← hRs]
    rfl
  rw [hP,hSmall] at hc
  have hCM : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simp only [conditionalMutualInformation,dite_eq_left (inferInstance : Nonempty (A×B))]
    rfl
  rw [hCM]
  exact hleft.trans hc

lemma conditionalMutualInformation_le_entropy {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [Nonempty A] [Nonempty B]
    [Countable B] [MeasurableSingletonClass B]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P]
    (hH : shannonEntropy (P.map MeasurableEquiv.prodAssoc.symm).snd ≠ ∞) :
    conditionalMutualInformation P ≠ ∞ ∧
      (conditionalMutualInformation P).toReal ≤
        (shannonEntropy (P.map MeasurableEquiv.prodAssoc.symm).snd).toReal := by
  let : IsProbabilityMeasure (P.map MeasurableEquiv.prodAssoc.symm) :=
    inferInstance
  have h := countable_information_le_entropy (P.map MeasurableEquiv.prodAssoc.symm) hH
  have hle : conditionalMutualInformation P ≤ mutualInformation (P.map MeasurableEquiv.prodAssoc.symm) := by
    rw [mutualInformation_chain P]
    exact le_add_left le_rfl
  exact ⟨ne_top_of_le_ne_top h.1 hle,(ENNReal.toReal_mono h.1 hle).trans h.2⟩

lemma conditionalMutualInformation_compProd {Z A B : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B] (μ : Measure Z) [IsFiniteMeasure μ]
    (κ : Kernel Z (A×B)) [IsMarkovKernel κ] :
    conditionalMutualInformation (μ ⊗ₘ κ) = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  simp only [conditionalMutualInformation,dite_eq_left (inferInstance : Nonempty (A×B)),Measure.fst_compProd]
  congr 1
  apply Measure.compProd_congr
  filter_upwards [condKernel_compProd μ κ] with z hz
  simp only [Kernel.prod_apply,Kernel.fst_apply,Kernel.snd_apply,hz]

lemma conditionalMutualInformation_map_right_le {Z A B C : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [StandardBorelSpace A] [StandardBorelSpace B] [StandardBorelSpace C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] (f : B → C) (hf : Measurable f) :
    conditionalMutualInformation (P.map (Prod.map id (Prod.map id f))) ≤
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let g : A×B → A×C := Prod.map id f
  have hg : Measurable g := measurable_id.prodMap hf
  let : IsMarkovKernel (κ.map g) := Kernel.IsMarkovKernel.map κ hg
  have hT : Measurable (Prod.map (id : Z → Z) g) := measurable_id.prodMap hg
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hmap : P.map (Prod.map id g) = μ ⊗ₘ κ.map g := by
    rw [Measure.compProd_map hg,hP]
  have hfst : (κ.map g).fst = κ.fst := by
    rw [Kernel.fst_eq,←Kernel.map_comp_right _ hg measurable_fst,Kernel.fst_eq]
    rfl
  have hsnd : (κ.map g).snd = κ.snd.map f := by
    rw [Kernel.snd_eq,Kernel.snd_eq,←Kernel.map_comp_right _ hg measurable_snd,
      ←Kernel.map_comp_right _ measurable_snd hf]
    rfl
  have hRef : μ ⊗ₘ ((κ.map g).fst ×ₖ (κ.map g).snd) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id g) := by
    have hk : κ.fst ×ₖ κ.snd.map f = (κ.fst ×ₖ κ.snd).map g := by
      simpa only [Kernel.map_id] using Kernel.map_prod_map κ.fst κ.snd measurable_id hf
    rw [hfst,hsnd,hk,Measure.compProd_map hg]
  change conditionalMutualInformation (P.map (Prod.map id g)) ≤ _
  have hCM := conditionalMutualInformation_compProd μ (κ.map g)
  have hCM' : conditionalMutualInformation (P.map (Prod.map id g)) =
      klDiv (P.map (Prod.map id g)) ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id g)) := by
    simpa only [←hmap,hRef] using hCM
  rw [hCM']
  have h := klDiv_map_le P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) hT
  have hCM0 : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simpa only [hP] using conditionalMutualInformation_compProd μ κ
  rwa [hCM0]




lemma rowInformation_eq_conditionalMutualInformation {S W X : Type*}
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace X]
    [StandardBorelSpace W] [StandardBorelSpace X] [Nonempty W] [Nonempty X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    rowInformation P γ = conditionalMutualInformation (P.map MeasurableEquiv.prodAssoc) := by
  let Q := P.map (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X))
  let : IsProbabilityMeasure Q := inferInstance
  have hX : P.snd = γ := by
    have h := congrArg Measure.snd hInd
    rw [Measure.snd_prod] at h
    convert h using 1
    simp only [Measure.snd, Measure.fst, Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_snd (measurable_fst.comp swapLast.measurable)]
    rfl
  have hQ : Q.map MeasurableEquiv.prodAssoc.symm = P :=
    MeasurableEquiv.prodAssoc.map_symm_map
  have hR : Q.map (Prod.map id Prod.snd) = ν.prod γ := by
    trans (P.map swapLast).fst
    · dsimp only [Q,Measure.fst]
      rw [Measure.map_map (measurable_id.prodMap measurable_snd)
        MeasurableEquiv.prodAssoc.measurable,
        Measure.map_map measurable_fst swapLast.measurable]
      rfl
    · exact hInd
  have hc := mutualInformation_chain Q
  rw [hQ,hR] at hc
  have hzero : mutualInformation (ν.prod γ) = 0 := by
    simp [mutualInformation, klDiv_self]
  rw [hzero,zero_add] at hc
  simpa only [rowInformation,mutualInformation,hX] using hc

lemma conditionalMutualInformation_swap {S A B : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (P : Measure (S×(A×B))) [IsProbabilityMeasure P] :
    conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let e : S×(A×B) ≃ᵐ S×(B×A) :=
    (MeasurableEquiv.refl S).prodCongr MeasurableEquiv.prodComm
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  let : IsMarkovKernel (κ.map Prod.swap) := Kernel.IsMarkovKernel.map κ measurable_swap
  have hf : (κ.map Prod.swap).fst = κ.snd := by
    rw [Kernel.fst_eq, ← Kernel.map_comp_right _ measurable_swap measurable_fst, Kernel.snd_eq]
    rfl
  have hs : (κ.map Prod.swap).snd = κ.fst := by
    rw [Kernel.snd_eq, ← Kernel.map_comp_right _ measurable_swap measurable_snd, Kernel.fst_eq]
    rfl
  have href : μ ⊗ₘ ((κ.map Prod.swap).fst ×ₖ (κ.map Prod.swap).snd) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map e := by
    rw [hf,hs, ← Kernel.map_prod_swap, Measure.compProd_map measurable_swap]
    rfl
  have hQ : μ ⊗ₘ κ.map Prod.swap = P.map (Prod.map id Prod.swap) := by
    rw [Measure.compProd_map measurable_swap,hP]
  have hcm : conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      klDiv (P.map (Prod.map id Prod.swap)) ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map e) := by
    simpa only [hQ,href] using conditionalMutualInformation_compProd μ (κ.map Prod.swap)
  have hcm0 : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simpa only [hP] using conditionalMutualInformation_compProd μ κ
  rw [hcm,hcm0]
  exact klDiv_map_equiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) e


lemma rowInformation_eq_sourceConditionalInformation {S W X : Type*}
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace X]
    [StandardBorelSpace W] [StandardBorelSpace X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    rowInformation P γ = conditionalMutualInformation
      (P.map (fun p => (p.1.1,(p.2,p.1.2)))) := by
  let := nonempty_of_isProbabilityMeasure P
  let : Nonempty W := ⟨(Classical.choice (inferInstance : Nonempty ((S×W)×X))).1.2⟩
  let : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty ((S×W)×X))).2⟩
  let : IsProbabilityMeasure (P.map (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X))) :=
    inferInstance
  rw [rowInformation_eq_conditionalMutualInformation P ν γ hInd]
  have he := conditionalMutualInformation_swap
    (P.map (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X)))
  have hfun : (Prod.map id Prod.swap ∘
      (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X))) =
      (fun p : (S×W)×X => (p.1.1,(p.2,p.1.2))) := rfl
  simpa only [Measure.map_map (measurable_id.prodMap measurable_swap)
    MeasurableEquiv.prodAssoc.measurable, hfun] using he.symm




def actualConditionalRowInformation {d m : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsFiniteMeasure P] : ℝ≥0∞ :=
  conditionalMutualInformation (P.map (fun p => (p.1.1,(p.2,p.1.2))))

structure ActualRowSourceConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : actualConditionalRowInformation P ≠ ∞
  row_le_entropy : (actualConditionalRowInformation P).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (actualConditionalRowInformation P).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (actualConditionalRowInformation P).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (actualConditionalRowInformation P).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((actualConditionalRowInformation P).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)

theorem actualRowSourceMain {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hEntropy : shannonEntropy (P.map swapLast).snd ≠ ∞)
    (ρ : PositiveMessage (P.map swapLast).snd → Measure (Sphere d))
    [∀ w, IsFiniteMeasure (ρ w)]
    (_hρac : ∀ w, ρ w ≪ uniformSphere d)
    (B D : PositiveMessage (P.map swapLast).snd → ℝ)
    (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w)
    (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w))
    (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w))
    (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d
      (completeFamily (P.map swapLast).snd B 1 sw.2) (completeFamily (P.map swapLast).snd D 1 sw.2))) P.fst) :
    ActualRowSourceConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1) := by
  have h := actualRowMain hdim P ν hInd H hν hEntropy ρ _hρac B D hB hD hgB hgD hCI
  have hi := rowInformation_eq_sourceConditionalInformation P ν (gaussianRows m d) hInd
  refine {
    row_finite := by simpa only [actualConditionalRowInformation, ← hi] using h.row_finite
    row_le_entropy := by simpa only [actualConditionalRowInformation, ← hi] using h.row_le_entropy
    conditional_density := by simpa only [actualConditionalRowInformation, ← hi] using h.conditional_density
    actual_limit := by simpa only [actualConditionalRowInformation, ← hi] using h.actual_limit
    smoothed_bound := by simpa only [actualConditionalRowInformation, ← hi] using h.smoothed_bound
    exact_integrable := by simpa only [actualConditionalRowInformation, ← hi] using h.exact_integrable
    exact_bound := by simpa only [actualConditionalRowInformation, ← hi] using h.exact_bound
    entropy_bound := by simpa only [actualConditionalRowInformation, ← hi] using h.entropy_bound
    positive_log_integrable := by simpa only [actualConditionalRowInformation, ← hi] using h.positive_log_integrable
    extended_log_bound := by simpa only [actualConditionalRowInformation, ← hi] using h.extended_log_bound
  }



theorem actualRowSourceRefinement {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (e : Sphere d×W → E) (he : Measurable e)
    (hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    actualConditionalRowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) =
      actualConditionalRowInformation P := by
  let F : (Sphere d×W)×Rows m d → (Sphere d×(W×E))×Rows m d :=
    fun p => ((p.1.1,(p.1.2,e p.1)),p.2)
  have hF : Measurable F :=
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (he.comp measurable_fst))).prodMk measurable_snd
  let Q := P.map F
  let : IsProbabilityMeasure Q := inferInstance
  have hIndQ : (Q.map swapLast).fst = ν.prod (gaussianRows m d) := by
    trans (P.map swapLast).fst
    · dsimp only [Q,Measure.fst]
      rw [Measure.map_map swapLast.measurable hF,
        Measure.map_map measurable_fst (swapLast.measurable.comp hF),
        Measure.map_map measurable_fst swapLast.measurable]
      rfl
    · exact hInd
  have hiQ := rowInformation_eq_sourceConditionalInformation Q ν (gaussianRows m d) hIndQ
  have hi := rowInformation_eq_sourceConditionalInformation P ν (gaussianRows m d) hInd
  change actualConditionalRowInformation Q = actualConditionalRowInformation P
  calc
    _ = rowInformation Q (gaussianRows m d) := hiQ.symm
    _ = rowInformation P (gaussianRows m d) := actualRowRefinement P e he hEntropy
    _ = _ := hi



def alignedExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) : Measure ((Sphere d×W)×Rows (m+r) d) :=
  (actualExperiment (r:=r) P).map (fun p => (p.1.1,Fin.append p.1.2 p.2))

lemma measurable_alignedMap {d m r : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (fun p : ((Sphere d×W)×Rows m d)×Rows r d => (p.1.1,Fin.append p.1.2 p.2)) :=
  measurable_fst.fst.prodMk ((measurable_append (E:=Vector d) m r).comp (measurable_fst.snd.prodMk measurable_snd))

instance alignedExperiment_probability {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (alignedExperiment (r:=r) P) := by
  unfold alignedExperiment
  infer_instance

def exposedJointMap {d k : ℕ} {W : Type*} (p : (Sphere d×W)×Rows k d) :
    (Rows k d×(Fin k → ℝ))×(Sphere d×W) := ((p.2,label p.2 (p.1.1:Vector d)),p.1)

lemma measurable_exposedJointMap {d k : ℕ} {W : Type*} [MeasurableSpace W] :
    Measurable (exposedJointMap (d:=d) (k:=k) (W:=W)) := by
  have hY : Measurable (fun p : (Sphere d×W)×Rows k d => label p.2 (p.1.1:Vector d)) :=
    (measurable_own_label (d:=d) (k:=k)).comp (measurable_snd.prodMk measurable_fst.fst)
  exact (measurable_snd.prodMk hY).prodMk measurable_fst

def exposedInformation {d k : ℕ} {W : Type*} [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsFiniteMeasure P] : ℝ≥0∞ :=
  conditionalMutualInformation (P.map exposedJointMap)





end CurrentProjection

end

end OAI
