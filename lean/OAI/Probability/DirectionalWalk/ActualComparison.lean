import OAI.Probability.DirectionalWalk.SignedInformation

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section ActualComparison
variable {α G : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

noncomputable def experimentLaw (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) (n : ℕ) :
    Measure (((ℕ × (ℕ × ℕ)) × G) × (ThreeLists α × ThreeLists α)) :=
  ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (signedChunkLaw ν L n)).map
    (fun p => ((threeHeight L (joinThree p.2),p.1.2+signedTotal (D false) p.2.1),p.2))

noncomputable def experimentReference (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) (n : ℕ) :
    Measure (((ℕ × (ℕ × ℕ)) × G) × (ThreeLists α × ThreeLists α)) :=
  (experimentLaw ν L D n).fst ⊗ₘ
    (signedThreeKernel (ν false) (L false) ×ₖ signedThreeKernel (ν true) (L true)).comap Prod.fst measurable_fst

lemma experiment_kl_comparison (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (D : Bool → α → G)
    (hgap : ∀ r, Integrable (informationOf (sumLaw (commonGapLaw ν L D) r) id) (sumLaw (commonGapLaw ν L D) r))
    (n : ℕ) [NeZero n]
    (hD : Integrable (informationOf (signedChunkLaw ν L n) (fun a => signedTotal (D false) a.1)) (signedChunkLaw ν L n)) :
    InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n) ≠ ∞ ∧
      (InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n)).toReal ≤
        6*(1+Real.log (8*((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1)) +
        1+Real.log 16 + entropyOf (sumLaw (commonGapLaw ν L D) (14*n)) id -
        entropyOf (sumLaw (commonGapLaw ν L D) n) id := by
  let π := markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)
  let ρ := signedChunkLaw ν L n
  let T : (ℕ × G) × (ThreeLists α × ThreeLists α) → ℕ × G :=
    fun p => (p.1.1+threeCount L (joinThree p.2),
      p.1.2+signedTotal (D false) p.2.1+signedTotal (D true) p.2.2)
  let : IsMarkovKernel (signedThreeKernel (ν false) (L false)) := signedThreeKernel_markov _ _ (fun H => hu H false)
  let : IsMarkovKernel (signedThreeKernel (ν true) (L true)) := signedThreeKernel_markov _ _ (fun H => hu H true)
  have hmark : (π.prod ρ).map T = markedSumLaw (commonGapLaw ν L D) (totalCountLaw n) :=
    signed_buffer_marked ν L hL he D n
  have hent := marked_count_entropy_difference (commonGapLaw ν L D) hgap n
  have hpair : Integrable (informationOf (π.prod ρ) T) (π.prod ρ) := by
    have ht := hent.2.1
    rw [← hmark,integrable_informationOf_map_iff] at ht
    exact ht
  have hT := integrable_informationOf_comp (π.prod ρ) T Prod.fst hpair
  have hS := integrable_informationOf_comp (π.prod ρ) T Prod.snd hpair
  have hU := integrable_informationOf_comp π id Prod.fst hent.1
  have hd := integrable_informationOf_comp π id Prod.snd hent.1
  have hzpair := integrable_informationOf_pair (π.prod ρ) (fun p => p.1.2)
    (fun p => signedTotal (D false) p.2.1)
    (integrable_informationOf_prod_fst π ρ Prod.snd hd)
    (integrable_informationOf_prod_snd π ρ (fun a => signedTotal (D false) a.1) hD)
  have hZ := integrable_informationOf_comp (π.prod ρ) _ (fun p : G × G => p.1+p.2) hzpair
  have hkl := threeChunk_kl_uniform ν L hL he hW hu c hc hlo n
  dsimp only at hkl
  rw [← signedChunk_kl ν L hu n] at hkl
  have hb := buffered_reference_comparison π ρ (threeHeight L ∘ joinThree)
    (signedTotal (D false)) (signedTotal (D true)) (threeCount L ∘ joinThree)
    (signedThreeKernel (ν false) (L false)) (signedThreeKernel (ν true) (L true))
    hkl.1 hU hd hZ hT hS
  have ht : entropyOf (π.prod ρ) (fun p =>
      (p.1.2+signedTotal (D false) p.2.1+signedTotal (D true) p.2.2,
        p.1.1+threeCount L (joinThree p.2))) =
      entropyOf (markedSumLaw (commonGapLaw ν L D) (totalCountLaw n)) id := by
    rw [entropyOf_pair_comm]
    change entropyOf (π.prod ρ) T = _
    rw [← hmark,entropyOf_map]
    rfl
  have hπ : entropyOf π (fun p => (p.2,p.1)) = entropyOf π id := by
    rw [entropyOf_pair_comm]
    rfl
  change InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n) ≠ ∞ ∧ _
  refine ⟨hb.1,?_⟩
  dsimp only [Function.comp_apply] at hb
  rw [ht,hπ] at hb
  have hh := hent.2.2
  dsimp only [π,ρ] at hb hh ⊢
  dsimp only [experimentLaw,experimentReference]
  linarith only [hb.2,hkl.2,hh]
end ActualComparison

lemma sumLaw_lattice_information {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (n : ℕ) :
    Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n) := by
  let a := 1+∑ i, ∫ x, |(x i : ℝ)| ∂ν
  have hm (i : Fin q) : (∫ x, |(x i : ℝ)| ∂ν) ≤ a := by
    have h : (∫ x, |(x i : ℝ)| ∂ν) ≤ ∑ j : Fin q, ∫ x, |(x j : ℝ)| ∂ν :=
      Finset.single_le_sum (f := fun j : Fin q => ∫ x, |(x j : ℝ)| ∂ν) (fun j _ => integral_nonneg (fun x : Fin q → ℤ => abs_nonneg (x j : ℝ))) (Finset.mem_univ i)
    dsimp [a]
    linarith
  exact (sumLaw_lattice_entropy ν hi a (by
    dsimp [a]
    have h : 0 ≤ ∑ i : Fin q, ∫ x, |(x i : ℝ)| ∂ν := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => abs_nonneg _))
    linarith) hm n).1

lemma lattice_experiment_kl_comparison {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {q : ℕ}
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hlo : ∀ H, ENNReal.ofReal c ≤ renewalPairMass ν L H)
    (D : Bool → α → Fin q → ℤ) (hi : ∀ b i, Integrable (fun a => (D b a i : ℝ)) (ν b))
    (n : ℕ) [NeZero n] :
    InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n) ≠ ∞ ∧
      (InformationTheory.klDiv (experimentLaw ν L D n) (experimentReference ν L D n)).toReal ≤
        6*(1+Real.log (8*((∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν)+1)+1)) +
        1+Real.log 16 + entropyOf (sumLaw (commonGapLaw ν L D) (14*n)) id -
        entropyOf (sumLaw (commonGapLaw ν L D) n) id := by
  exact experiment_kl_comparison ν L hL he hW hu c hc hlo D
    (sumLaw_lattice_information _ (commonGapLaw_lattice_integrable ν L hL he hW D hi)) n
    (signed_chunk_positive_info ν L hL he hW (D false) (hi false) n)

end DirectionalZeroOne

end OAI
