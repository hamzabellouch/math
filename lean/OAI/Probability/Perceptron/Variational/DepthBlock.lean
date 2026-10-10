import Mathlib
import OAI.Probability.Perceptron.Variational.BlockFocus

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

lemma indexedDepthLaw_block_mass (k : ℕ) (z : Fin k → ℝ)
    (r : ℕ) (A : FiniteBlock (Fin (k+1)) r) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))) {R | finiteBlock r R = A} =
      ∫⁻ b, indexedBlockSample k A b ∂indexedCascadeBaseLaw k z := by
  have hE : MeasurableSet {R : FiniteOverlap (Fin (k+1)) | finiteBlock r R = A} :=
    measurableSet_eq_fun (finiteBlock_measurable r) measurable_const
  rw [← lintegral_indicator_one hE]
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq]
  rw [indexedDepthLaw_lintegral_prefix k z r (fun B => if B = A then 1 else 0)]
  apply lintegral_congr
  intro b
  rw [indexedBlockSample_eq_measure,← lintegral_indicator_one ((Set.to_countable _).measurableSet)]
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq]

lemma indexedDepthLaw_focused_mass (k : ℕ) (z : Fin k → ℝ) (r d : ℕ)
    (A : FiniteBlock (Fin (k+1)) r) (i : Fin r) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))
      {R | finiteBlock r R = A ∧ d ≤ (R i r).val} =
        ∫⁻ b, indexedBlockFocused k d A i b ∂indexedCascadeBaseLaw k z := by
  let E : Set (FiniteOverlap (Fin (k+1))) := {R | finiteBlock r R = A ∧ d ≤ (R i r).val}
  have hE : MeasurableSet E := by
    exact (measurableSet_eq_fun (finiteBlock_measurable r) measurable_const).inter
      ((Set.to_countable {l : Fin (k+1) | d ≤ l.val}).measurableSet.preimage (by fun_prop))
  change (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))) E = _
  rw [← lintegral_indicator_one hE]
  rw [indexedDepthLaw_lintegral k z (E.indicator 1) (measurable_const.indicator hE)]
  apply lintegral_congr
  intro b
  let S : Set ((Fin r → IndexedLeaf k) × IndexedLeaf k) :=
    {p | (fun a c => indexedCommonDepth k (p.1 a) (p.1 c)) = A ∧
      d ≤ (indexedCommonDepth k (p.1 i) p.2).val}
  have hh := (infiniteReplica_prefix_fresh_preserving (indexedLeafProbability k b) r).lintegral_comp
    (f := S.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator ((Set.to_countable S).measurableSet))
  calc
    _ = ∫⁻ xs, S.indicator 1 ((fun j : Fin r => xs j.val),xs r)
        ∂Measure.infinitePi (fun _ : ℕ => indexedLeafProbability k b) := rfl
    _ = ∫⁻ p, S.indicator 1 p
        ∂(Measure.pi (fun _ : Fin r => indexedLeafProbability k b)).prod (indexedLeafProbability k b) := hh
    _ = _ := by
      rw [lintegral_indicator_one ((Set.to_countable S).measurableSet),indexedBlockFocused_eq_measure]

theorem indexedDepthLaw_focused_formula (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (r d : ℕ) (hd : d ≤ k) (A : FiniteBlock (Fin (k+1)) r) (i : Fin r) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))
      {R | finiteBlock r R = A ∧ d ≤ (R i r).val} =
      (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))) {R | finiteBlock r R = A} *
        ENNReal.ofReal (((∑ j, if d ≤ (A i j).val then (1:ℝ) else 0) -
          (if h : d = 0 then 0 else z ⟨d-1,by omega⟩)) / r) := by
  rw [indexedDepthLaw_focused_mass,indexedDepthLaw_block_mass,
    indexedBlockFocused_integral k z hz hz0 hz1 d hd A i,Fintype.card_fin]

lemma indexedDepthLaw_one_block_ae (k : ℕ) (z : Fin k → ℝ) :
    ∀ᵐ R ∂(indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))),
      finiteBlock 1 R = fun _ _ => Fin.last k := by
  filter_upwards [indexedDepthLaw_geometry k z] with R hR
  funext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  simpa only [hi,hj,finiteBlock,Fin.val_zero] using hR.2.1 0

lemma indexedDepthLaw_pair_tail (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (d : ℕ) (hd : d ≤ k) :
    (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))) {R | d ≤ (R 0 1).val} =
      ENNReal.ofReal (1 - (if h : d = 0 then 0 else z ⟨d-1,by omega⟩)) := by
  let μ := (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1))))
  let A : FiniteBlock (Fin (k+1)) 1 := fun _ _ => Fin.last k
  have hB : μ {R | finiteBlock 1 R = A} = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [indexedDepthLaw_one_block_ae k z] with R hR
    change (finiteBlock 1 R = A) = True
    exact propext ⟨fun _ => trivial, fun _ => hR⟩
  have hC : μ {R | finiteBlock 1 R = A ∧ d ≤ (R (0:Fin 1) 1).val} =
      μ {R | d ≤ (R 0 1).val} := by
    apply measure_congr
    filter_upwards [indexedDepthLaw_one_block_ae k z] with R hR
    change (finiteBlock 1 R = A ∧ d ≤ (R 0 1).val) = (d ≤ (R 0 1).val)
    exact propext ⟨fun h => h.2, fun h => ⟨hR,h⟩⟩
  have h := indexedDepthLaw_focused_formula k z hz hz0 hz1 1 d hd A 0
  change μ _ = μ _ * _ at h
  rw [hB,hC] at h
  simpa only [A,Fintype.sum_unique,Fin.val_last,ite_eq_left hd,Nat.cast_one,div_one,one_mul] using h

lemma measureReal_fin_atom_from_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ)
    (f : Ω → Fin (k+1)) (hf : Measurable f) (E : Set Ω) (hE : MeasurableSet E)
    (c : Fin (k+1)) :
    μ.real {x | x ∈ E ∧ f x = c} =
      μ.real {x | x ∈ E ∧ c.val ≤ (f x).val} -
        μ.real {x | x ∈ E ∧ c.val+1 ≤ (f x).val} := by
  have hs : MeasurableSet {x | x ∈ E ∧ c.val+1 ≤ (f x).val} :=
    hE.inter ((Set.to_countable {l : Fin (k+1) | c.val+1 ≤ l.val}).measurableSet.preimage hf)
  have he : {x | x ∈ E ∧ f x = c} =
      {x | x ∈ E ∧ c.val ≤ (f x).val} \ {x | x ∈ E ∧ c.val+1 ≤ (f x).val} := by
    apply Set.ext
    intro x
    change (x ∈ E ∧ f x = c) ↔
      (x ∈ E ∧ c.val ≤ (f x).val) ∧ ¬ (x ∈ E ∧ c.val+1 ≤ (f x).val)
    constructor
    · rintro ⟨hx,hxc⟩
      simp only [hxc,le_refl,and_true,Nat.not_succ_le_self,and_false,not_false_eq_true]
      exact hx
    · intro hx
      have hn : ¬ c.val+1 ≤ (f x).val := fun h => hx.2 ⟨hx.1.1,h⟩
      have hl := hx.1.2
      exact ⟨hx.1.1,Fin.ext (by omega)⟩
  rw [he,measureReal_sdiff (by intro x hx; exact ⟨hx.1, Nat.le_trans (Nat.le_succ _) hx.2⟩) hs]

theorem finiteGG_of_depth_thresholds (k : ℕ)
    (μ : Measure (FiniteOverlap (Fin (k+1)))) [IsProbabilityMeasure μ]
    (hh : ∀ r, 1 ≤ r → ∀ (i : Fin r) (A : FiniteBlock (Fin (k+1)) r)
      (d : ℕ), d ≤ k+1 →
      μ.real {R | finiteBlock r R = A ∧ d ≤ (R i r).val} =
        μ.real {R | finiteBlock r R = A} * μ.real {R | d ≤ (R 0 1).val} / r +
          (∑ j ∈ Finset.univ.erase i,
            μ.real {R | finiteBlock r R = A ∧ d ≤ (R i j).val}) / r) : FiniteGG μ := by
  classical
  intro r hr i A c
  have hE : MeasurableSet {R : FiniteOverlap (Fin (k+1)) | finiteBlock r R = A} :=
    measurableSet_eq_fun (finiteBlock_measurable r) measurable_const
  have hm (i j : ℕ) : Measurable (fun R : FiniteOverlap (Fin (k+1)) => R i j) := by fun_prop
  have hAtom (a b : ℕ) : μ.real {R | finiteBlock r R = A ∧ R a b = c} =
      μ.real {R | finiteBlock r R = A ∧ c.val ≤ (R a b).val} -
        μ.real {R | finiteBlock r R = A ∧ c.val+1 ≤ (R a b).val} :=
    measureReal_fin_atom_from_tails μ k (fun R => R a b)
      (hm a b) {R | finiteBlock r R = A} hE c
  have hPair := measureReal_fin_atom_from_tails μ k (fun R => R 0 1)
    (hm 0 1) univ MeasurableSet.univ c
  simp only [Set.mem_univ,true_and] at hPair
  simp_rw [hAtom]
  rw [hPair,hh r hr i A c.val (by omega),hh r hr i A (c.val+1) (by omega),
    Finset.sum_sub_distrib]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
