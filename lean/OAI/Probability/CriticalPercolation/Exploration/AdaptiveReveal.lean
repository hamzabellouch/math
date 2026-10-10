import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct

structure RevealPartition (E I : Type*) [Fintype I] where
  block : I → Set E
  cell : I → Set (Set E)
  measurable : ∀ i, MeasurableSet[blockSigma (block i)] (cell i)
  disjoint : Pairwise (Disjoint on cell)
  cover : (⋃ i, cell i)=Set.univ

namespace RevealPartition
variable {E I : Type*} [Fintype I] (P : RevealPartition E I)

lemma cell_measurable (i : I) : MeasurableSet (P.cell i) :=
  (blockSigma_le (P.block i)) _ (P.measurable i)

lemma exists_cell (σ : Set E) : ∃ i, σ∈P.cell i := by
  have h : σ∈⋃ i, P.cell i := by rw [P.cover]; trivial
  exact Set.mem_iUnion.mp h

lemma cell_unique {σ : Set E} {i j : I} (hi : σ∈P.cell i) (hj : σ∈P.cell j) : i=j := by
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint h) hi hj

@[instance_reducible] def historySigma : MeasurableSpace (Set E) where
  MeasurableSet' A := ∀ i, MeasurableSet[blockSigma (P.block i)] (A∩P.cell i)
  measurableSet_empty := by intro i; simp
  measurableSet_compl := by
    intro A hA i
    have he : Aᶜ∩P.cell i=P.cell i\(A∩P.cell i) := by ext σ; simp; tauto
    rw [he]
    exact (P.measurable i).diff (hA i)
  measurableSet_iUnion := by
    intro A hA i
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (fun n => hA n i)

lemma historySigma_le : P.historySigma ≤ (inferInstance : MeasurableSpace (Set E)) := by
  intro A hA
  have he : A=⋃ i, A∩P.cell i := by rw [← Set.inter_iUnion,P.cover,Set.inter_univ]
  rw [he]
  exact MeasurableSet.iUnion (fun i => (blockSigma_le (P.block i)) _ (hA i))

lemma cell_history_measurable (i : I) : MeasurableSet[P.historySigma] (P.cell i) := by
  intro j
  by_cases hij : i=j
  · subst j
    simpa using P.measurable i
  · have he := Set.disjoint_iff_inter_eq_empty.mp (P.disjoint hij)
    rw [he]
    exact @MeasurableSet.empty (Set E) (blockSigma (P.block j))

def probability (q : E → unitInterval) (A : Set (Set E)) (σ : Set E) : ℝ≥0∞ :=
  ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ

lemma probability_on_cell (q : E → unitInterval) (A : Set (Set E))
    {σ : Set E} {i : I} (hi : σ∈P.cell i) :
    P.probability q A σ=blockProbability q (P.block i) A σ := by
  rw [probability,Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    exact hji (P.cell_unique hj hi)
  · simp

lemma probability_le_one (q : E → unitInterval) (A : Set (Set E)) (σ : Set E) :
    P.probability q A σ≤1 := by
  obtain ⟨i,hi⟩ := P.exists_cell σ
  rw [P.probability_on_cell q A hi]
  exact blockProbability_le_one _ _ _ _

lemma probability_measurable (q : E → unitInterval) (A : Set (Set E))
    (hA : MeasurableSet A) : @Measurable (Set E) ℝ≥0∞ P.historySigma inferInstance
      (P.probability q A) := by
  intro U hU i
  have he : P.probability q A ⁻¹' U∩P.cell i=
      blockProbability q (P.block i) A ⁻¹' U∩P.cell i := by
    ext σ
    constructor <;> intro h
    · exact ⟨by change blockProbability q (P.block i) A σ∈U
                rw [← P.probability_on_cell q A h.2]; exact h.1,h.2⟩
    · exact ⟨by rw [Set.mem_preimage,P.probability_on_cell q A h.2]; exact h.1,h.2⟩
  rw [he]
  exact ((measurable_blockProbability q (P.block i) A hA) hU).inter (P.measurable i)

theorem setLIntegral_probability (q : E → unitInterval) (A B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet[P.historySigma] B) :
    (∫⁻ σ in B, P.probability q A σ ∂law q)=law q (A∩B) := by
  have hmB := P.historySigma_le _ hB
  have hf (i : I) : Measurable ((P.cell i).indicator (blockProbability q (P.block i) A)) :=
    ((measurable_blockProbability q (P.block i) A hA).mono (blockSigma_le _) le_rfl).indicator
      (P.cell_measurable i)
  change (∫⁻ σ in B, ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ ∂law q)=_
  rw [lintegral_finsetSum _ (fun i _ => hf i)]
  have he (i : I) :
      (∫⁻ σ in B, (P.cell i).indicator (blockProbability q (P.block i) A) σ ∂law q)=
      law q (A∩(B∩P.cell i)) := by
    rw [lintegral_indicator (P.cell_measurable i),Measure.restrict_restrict
      (P.cell_measurable i),Set.inter_comm (P.cell i) B]
    exact setLIntegral_blockProbability q (P.block i) A (B∩P.cell i) hA (hB i)
  simp_rw [he]
  have hd : Pairwise (Disjoint on (fun i => A∩(B∩P.cell i))) := by
    intro i j hij
    exact (P.disjoint hij).mono (fun _ h => h.2.2) (fun _ h => h.2.2)
  rw [← tsum_fintype (L := .unconditional _),← measure_iUnion hd (fun i => hA.inter (hmB.inter (P.cell_measurable i)))]
  congr 1
  rw [← Set.inter_iUnion,← Set.inter_iUnion,P.cover,Set.inter_univ]

def enlarge (T : I → Set E) (hT : ∀ i, P.block i⊆T i) : RevealPartition E I where
  block := T
  cell := P.cell
  measurable i := (by
    have hmono : blockSigma (P.block i) ≤ blockSigma (T i) :=
      iSup₂_mono' (fun e he => ⟨e,hT i he,le_rfl⟩)
    exact hmono _ (P.measurable i))
  disjoint := P.disjoint
  cover := P.cover

def decide {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (d : I → Set E → J)
    (hd : ∀ i, @Measurable (Set E) J (blockSigma (P.block i)) inferInstance (d i)) :
    RevealPartition E (I×J) where
  block ij := P.block ij.1
  cell ij := P.cell ij.1∩(d ij.1 ⁻¹' {ij.2})
  measurable ij := (P.measurable ij.1).inter (hd ij.1 (MeasurableSet.singleton _))
  disjoint := by
    intro ij kl hne
    apply Set.disjoint_left.mpr
    intro σ hσ hτ
    have hi : ij.1=kl.1 := P.cell_unique hσ.1 hτ.1
    have hj : ij.2=kl.2 := by
      have ht : d kl.1 σ=kl.2 := hτ.2
      rw [← hi] at ht
      exact hσ.2.symm.trans ht
    exact hne (Prod.ext hi hj)
  cover := by
    apply Set.eq_univ_of_forall
    intro σ
    obtain ⟨i,hi⟩ := P.exists_cell σ
    exact Set.mem_iUnion.mpr ⟨(i,d i σ),hi,rfl⟩

lemma historySigma_le_enlarge (T : I → Set E) (hT : ∀ i, P.block i⊆T i) :
    P.historySigma ≤ (P.enlarge T hT).historySigma := by
  intro A hA i
  have hmono : blockSigma (P.block i) ≤ blockSigma (T i) :=
    iSup₂_mono' (fun e he => ⟨e,hT i he,le_rfl⟩)
  exact hmono _ (hA i)

lemma historySigma_le_decide {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (d : I → Set E → J)
    (hd : ∀ i, @Measurable (Set E) J (blockSigma (P.block i)) inferInstance (d i)) :
    P.historySigma ≤ (P.decide d hd).historySigma := by
  intro A hA ij
  change MeasurableSet[blockSigma (P.block ij.1)]
    (A∩(P.cell ij.1∩(d ij.1 ⁻¹' {ij.2})))
  rw [← Set.inter_assoc]
  exact (hA ij.1).inter (hd ij.1 (MeasurableSet.singleton _))

lemma measureReal_inter_le (q : E → unitInterval) (A B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet[P.historySigma] B)
    (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ σ∈B, P.probability q A σ≤ENNReal.ofReal ε) :
    (law q).real (B∩A)≤ε*(law q).real B := by
  have hh : law q (A∩B)≤ENNReal.ofReal ε*law q B := by
    rw [← P.setLIntegral_probability q A B hA hB]
    calc
      (∫⁻ σ in B, P.probability q A σ ∂law q) ≤
          ∫⁻ _ in B, ENNReal.ofReal ε ∂law q :=
        setLIntegral_mono' (P.historySigma_le _ hB) hb
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)) hh
  simpa only [Set.inter_comm A B,ENNReal.toReal_mul,ENNReal.toReal_ofReal hε,
    Measure.real] using ht

end RevealPartition
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
