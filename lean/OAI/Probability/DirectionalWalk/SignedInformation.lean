import OAI.Probability.DirectionalWalk.TotalEntropy

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section SignedKL
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def signedChunkLaw (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) : Measure (ThreeLists α × ThreeLists α) :=
  (threeChunkLaw ν L n).map splitThree

instance signedChunkLaw_probability (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (n : ℕ) [NeZero n] : IsProbabilityMeasure (signedChunkLaw ν L n) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma signedChunk_kl (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ)
    (hu : ∀ H b, Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (L b) H) ≠ 0)
    (n : ℕ) [NeZero n] :
    InformationTheory.klDiv
      ((signedChunkLaw ν L n).map (fun a => (threeHeight L (joinThree a),a)))
      ((signedChunkLaw ν L n).map (threeHeight L ∘ joinThree) ⊗ₘ
        (signedThreeKernel (ν false) (L false) ×ₖ signedThreeKernel (ν true) (L true))) =
    InformationTheory.klDiv ((threeChunkLaw ν L n).map (fun a => (threeHeight L a,a)))
      ((threeChunkLaw ν L n).map (threeHeight L) ⊗ₘ threeBridgeKernel ν L) := by
  let : IsMarkovKernel (threeBridgeKernel ν L) := threeBridgeKernel_markov ν L hu
  have hf : (signedChunkLaw ν L n).map (threeHeight L ∘ joinThree) =
      (threeChunkLaw ν L n).map (threeHeight L) := by
    rw [signedChunkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
  rw [hf,← threeBridgeKernel_split ν L hu,Measure.compProd_map (measurable_of_countable _)]
  have hg : (signedChunkLaw ν L n).map (fun a => (threeHeight L (joinThree a),a)) =
      ((threeChunkLaw ν L n).map (fun a => (threeHeight L a,a))).map
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ℕ × (ℕ × ℕ))) splitThreeEquiv) := by
    rw [signedChunkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
  rw [hg]
  exact klDiv_map_equiv _ _ (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) splitThreeEquiv)
end SignedKL

section SignedTotals
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {G : Type*} [AddCommGroup G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

noncomputable def signedTotal (D : α → G) (a : ThreeLists α) : G :=
  listTotal D a.1 + (listTotal D a.2.1 + listTotal D a.2.2)

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma threeTotal_split (D : Bool → α → G) (a : ThreeChunk α) :
    signedTotal (D false) (splitThree a).1 + signedTotal (D true) (splitThree a).2 = threeTotal D a := by
  dsimp [signedTotal,splitThree,threeTotal,pairTotal]
  abel

lemma signed_buffer_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (signedChunkLaw ν L n)).map
      (fun p => (p.1.1+threeCount L (joinThree p.2),
        p.1.2+signedTotal (D false) p.2.1+signedTotal (D true) p.2.2)) =
      markedSumLaw (commonGapLaw ν L D) (totalCountLaw n) := by
  have hp := Measure.map_prod_map (markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n))
    (threeChunkLaw ν L n) measurable_id (measurable_of_countable splitThree)
  simp only [Measure.map_id] at hp
  rw [signedChunkLaw,hp,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hf : (fun p : (ℕ × G) × ThreeChunk α =>
      (p.1.1+threeCount L (joinThree (splitThree p.2)),
        p.1.2+signedTotal (D false) (splitThree p.2).1+signedTotal (D true) (splitThree p.2).2)) =
      (fun p => (p.1.1+threeCount L p.2,p.1.2+threeTotal D p.2)) := by
    funext p
    rw [join_splitThree,add_assoc,threeTotal_split]
  change Measure.map (fun p : (ℕ × G) × ThreeChunk α =>
    (p.1.1+threeCount L (joinThree (splitThree p.2)),
      p.1.2+signedTotal (D false) (splitThree p.2).1+signedTotal (D true) (splitThree p.2).2)) _ = _
  rw [hf,bufferedChunkLaw_marked ν L hL he D]
end SignedTotals
section InformationTransport
variable {Ω Ξ A : Type*} [Countable Ω] [Countable Ξ] [Countable A]
  [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace A]
  [MeasurableSingletonClass Ω] [MeasurableSingletonClass Ξ] [MeasurableSingletonClass A]

omit [Countable A] [MeasurableSingletonClass A] in
lemma integrable_informationOf_map_iff (μ : Measure Ω) (F : Ω → Ξ) (X : Ξ → A) :
    Integrable (informationOf (μ.map F) X) (μ.map F) ↔
      Integrable (informationOf μ (X ∘ F)) μ := by
  rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable,informationOf_map]

omit [Countable A] [MeasurableSingletonClass A] in
lemma integrable_informationOf_prod_fst (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (X : Ω → A)
    (hi : Integrable (informationOf μ X) μ) :
    Integrable (informationOf (μ.prod ν) (X ∘ Prod.fst)) (μ.prod ν) := by
  rw [← integrable_informationOf_map_iff,Measure.map_fst_prod,measure_univ,one_smul]
  exact hi

omit [Countable A] [MeasurableSingletonClass A] in
lemma integrable_informationOf_prod_snd (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (X : Ξ → A)
    (hi : Integrable (informationOf ν X) ν) :
    Integrable (informationOf (μ.prod ν) (X ∘ Prod.snd)) (μ.prod ν) := by
  rw [← integrable_informationOf_map_iff,Measure.map_snd_prod,measure_univ,one_smul]
  exact hi
end InformationTransport

lemma entropyOf_pair_comm {Ω A B : Type*} [Countable Ω] [Countable A] [Countable B]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass Ω] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure Ω) (X : Ω → A) (Y : Ω → B) :
    entropyOf μ (fun ω => (X ω,Y ω)) = entropyOf μ (fun ω => (Y ω,X ω)) := by
  unfold entropyOf
  rw [informationOf_pair_comm]

section ExperimentInformation
variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma signed_chunk_positive_integrable (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : α → ℝ) (hi : Integrable D (ν false)) (n : ℕ) [NeZero n] :
    Integrable (fun a => signedTotal D a.1) (signedChunkLaw ν L n) := by
  rw [signedChunkLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  have h0 := listTotal_window_integrable ν L hL he hW false D hi n n
  have h1 := listTotal_window_integrable ν L hL he hW false D hi (7*n) n
  exact (h0.comp_fst _).add (((h1.comp_fst _).add (h0.comp_snd _)).comp_snd _)

lemma signed_chunk_positive_info {q : ℕ}
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : α → Fin q → ℤ) (hi : ∀ i, Integrable (fun a => (D a i : ℝ)) (ν false))
    (n : ℕ) [NeZero n] :
    Integrable (informationOf (signedChunkLaw ν L n) (fun a => signedTotal D a.1)) (signedChunkLaw ν L n) := by
  apply integrable_informationOf_lattice
  intro i
  have h := signed_chunk_positive_integrable ν L hL he hW (fun a => (D a i : ℝ)) (hi i) n
  simpa only [signedTotal,listTotal,Pi.add_apply,Finset.sum_apply,Int.cast_add,Int.cast_sum] using h
end ExperimentInformation

end DirectionalZeroOne

end OAI
