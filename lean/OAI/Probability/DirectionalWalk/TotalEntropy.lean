import OAI.Probability.DirectionalWalk.CountWindows

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section ChunkSums
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]
  {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma map_add_product {E F M : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable E] [Countable F] [MeasurableSingletonClass E] [MeasurableSingletonClass F]
    [AddCommMonoid M] [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → M) (g : F → M) :
    (μ.prod ν).map (fun p => f p.1+g p.2) = (μ.map f).conv (ν.map g) := by
  rw [Measure.conv,Measure.map_prod_map μ ν (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

noncomputable def threeCount {α : Type*} (L : Bool → α → ℕ) (a : ThreeChunk α) : ℕ :=
  listCommonCount L a.1 + (listCommonCount L a.2.1 + listCommonCount L a.2.2)

noncomputable def threeTotal (D : Bool → α → G) (a : ThreeChunk α) : G :=
  pairTotal D a.1 + (pairTotal D a.2.1 + pairTotal D a.2.2)

noncomputable def threeCountLaw (n : ℕ) : Measure ℕ :=
  (countWindowLaw n n).conv ((countWindowLaw (7*n) n).conv (countWindowLaw n n))

noncomputable def totalCountLaw (n : ℕ) : Measure ℕ :=
  (countWindowLaw n n).conv (threeCountLaw n)

instance threeCountLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (threeCountLaw n) := by
  unfold threeCountLaw
  infer_instance

instance totalCountLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (totalCountLaw n) := by
  unfold totalCountLaw
  infer_instance

lemma threeChunkLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    (threeChunkLaw ν L n).map (fun a => (threeCount L a,threeTotal D a)) =
      markedSumLaw (commonGapLaw ν L D) (threeCountLaw n) := by
  change ((windowCommonLaw ν L n n).prod
    ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))).map
      (fun a => (listCommonCount L a.1,pairTotal D a.1)+
        ((listCommonCount L a.2.1,pairTotal D a.2.1)+(listCommonCount L a.2.2,pairTotal D a.2.2))) = _
  rw [map_add_product (windowCommonLaw ν L n n)
    ((windowCommonLaw ν L (7*n) n).prod (windowCommonLaw ν L n n))
    (fun a => (listCommonCount L a,pairTotal D a))
    (fun a => (listCommonCount L a.1,pairTotal D a.1)+(listCommonCount L a.2,pairTotal D a.2)),
    map_add_product (windowCommonLaw ν L (7*n) n) (windowCommonLaw ν L n n)
    (fun a => (listCommonCount L a,pairTotal D a)) (fun a => (listCommonCount L a,pairTotal D a))]
  simp_rw [windowCommonLaw_marked ν L hL he D,markedSumLaw_conv]
  rfl

lemma bufferedChunkLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (threeChunkLaw ν L n)).map
      (fun p => (p.1.1+threeCount L p.2,p.1.2+threeTotal D p.2)) =
      markedSumLaw (commonGapLaw ν L D) (totalCountLaw n) := by
  change ((markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n)).prod (threeChunkLaw ν L n)).map
      (fun p => id p.1+(threeCount L p.2,threeTotal D p.2)) = _
  rw [map_add_product (markedSumLaw (commonGapLaw ν L D) (countWindowLaw n n))
    (threeChunkLaw ν L n) id (fun a => (threeCount L a,threeTotal D a)),Measure.map_id,threeChunkLaw_marked ν L hL he D,markedSumLaw_conv]
  rfl

lemma totalCountLaw_bounds (n : ℕ) [NeZero n] :
    ∀ᵐ r ∂totalCountLaw n, 10*n ≤ r ∧ r ≤ 14*n := by
  have h (k : ℕ) : ∀ᵐ r ∂countWindowLaw k n, k ≤ r ∧ r ≤ k+n :=
    (countWindowLaw_ae k n).mono (fun _ h => ⟨h.1,h.2.le⟩)
  have h3 := convolution_ae_bounds (countWindowLaw (7*n) n) (countWindowLaw n n)
    (7*n) (7*n+n) n (n+n) (h (7*n)) (h n)
  have h2 := convolution_ae_bounds (countWindowLaw n n)
    ((countWindowLaw (7*n) n).conv (countWindowLaw n n))
    n (n+n) (7*n+n) ((7*n+n)+(n+n)) (h n) h3
  have h1 := convolution_ae_bounds (countWindowLaw n n) (threeCountLaw n)
    n (n+n) (n+(7*n+n)) ((n+n)+((7*n+n)+(n+n))) (h n) h2
  have hlow : n+(n+(7*n+n)) = 10*n := by omega
  have hhi : (n+n)+((n+n)+((7*n+n)+(n+n))) = 14*n := by omega
  simpa only [hlow,hhi,totalCountLaw] using h1
end ChunkSums
lemma atomInfo_integrable_nat_bounded (θ : Measure ℕ) [IsProbabilityMeasure θ]
    (M : ℕ) (hM : ∀ᵐ n ∂θ, n ≤ M) :
    Integrable (atomInfo θ) θ ∧ discreteEntropy θ ≤ 1+Real.log (M+2) := by
  have hi : Integrable (fun n : ℕ => (n : ℝ)) θ := by
    apply (integrable_const (M : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    filter_upwards [hM] with n hn
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using (Nat.cast_le.mpr hn : (n : ℝ) ≤ M)
  have hm : (∫ n : ℕ, (n : ℝ) ∂θ) ≤ M+1 := by
    calc
      _ ≤ ∫ _ : ℕ, (M : ℝ) ∂θ := integral_mono_ae hi (integrable_const _) (hM.mono (fun _ h => Nat.cast_le.mpr h))
      _ ≤ M+1 := by simp
  simpa only [add_assoc,show (1 : ℝ)+1=2 by norm_num] using entropy_nat_moment θ hi (M+1) (by positivity) hm

section TotalEntropy
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

lemma marked_count_entropy_difference (ν : Measure G) [IsProbabilityMeasure ν]
    (hi : ∀ r, Integrable (informationOf (sumLaw ν r) id) (sumLaw ν r))
    (n : ℕ) [NeZero n] :
    Integrable (informationOf (markedSumLaw ν (countWindowLaw n n)) id) (markedSumLaw ν (countWindowLaw n n)) ∧
    Integrable (informationOf (markedSumLaw ν (totalCountLaw n)) id) (markedSumLaw ν (totalCountLaw n)) ∧
    entropyOf (markedSumLaw ν (totalCountLaw n)) id - entropyOf (markedSumLaw ν (countWindowLaw n n)) id ≤
      1+Real.log 16+entropyOf (sumLaw ν (14*n)) id-entropyOf (sumLaw ν n) id := by
  have hc : ∀ᵐ r ∂countWindowLaw n n, n ≤ r ∧ r ≤ 2*n := (countWindowLaw_ae n n).mono (fun _ h => by omega)
  have hT := totalCountLaw_bounds n
  have he := atomInfo_integrable_nat_bounded (totalCountLaw n) (14*n) (hT.mono (fun _ h => h.2))
  have hb := markedSumLaw_entropy_bounds ν (countWindowLaw n n) hi (countWindowLaw_entropy n n).1 n (2*n) hc
  have ht := markedSumLaw_entropy_bounds ν (totalCountLaw n) hi he.1 (10*n) (14*n) hT
  refine ⟨hb.1,ht.1,?_⟩
  rw [(countWindowLaw_entropy n n).2] at hb
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hl : Real.log ((14*n : ℕ)+2 : ℝ) ≤ Real.log 16+Real.log n := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  linarith [ht.2.2,hb.2.1,he.2]
end TotalEntropy
lemma integrable_informationOf_lattice {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ℕ} (X : Ω → Fin q → ℤ) (hi : ∀ i, Integrable (fun ω => (X ω i : ℝ)) μ) :
    Integrable (informationOf μ X) μ := by
  have hn : ∀ i : Fin q, 0 ≤ ∫ ω, |(X ω i : ℝ)| ∂μ := fun i => integral_nonneg (fun ω => abs_nonneg _)
  have hs : 0 ≤ ∑ i : Fin q, ∫ ω, |(X ω i : ℝ)| ∂μ := Finset.sum_nonneg (fun i _ => hn i)
  exact (entropyOf_lattice_moment μ q X (fun i => (hi i).abs)
    (1+∑ i : Fin q, ∫ ω, |(X ω i : ℝ)| ∂μ) (by linarith) (fun i => by
      have h := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
      linarith)).1

lemma listTotal_nth_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (b : Bool) (D : α → ℝ) (hi : Integrable D (ν b)) (r : ℕ) :
    Integrable (fun a => listTotal D (a b)) (nthCommonLaw ν L r) := by
  rw [nthCommonLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_nthCommonList L r).aemeasurable]
  have hb := commonBlock_integrable_total ν L hL he hW b D hi
  rw [commonBlockLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_firstCommonBlock L).aemeasurable] at hb
  have hi' (i : ℕ) : Integrable (fun Z => listTotal D (commonBlocks L Z i b)) (twoTapeLaw ν) := by
    exact ((commonRestart_measurePreserving ν L hL he).iterate i).integrable_comp_of_integrable hb
  have hs := integrable_finsetSum (Finset.range r) (fun i _ => hi' i)
  apply hs.congr
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  filter_upwards [hZ,ae_common_iterates ν L hL he] with Z hZ hiter
  exact (nthCommonList_total L D Z hZ hiter r b).symm

lemma listTotal_window_integrable {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hW : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (b : Bool) (D : α → ℝ) (hi : Integrable D (ν b)) (k n : ℕ) [NeZero n] :
    Integrable (fun a => listTotal D (a b)) (windowCommonLaw ν L k n) := by
  unfold windowCommonLaw
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n))
  rw [integrable_finsetSum_measure]
  intro i _
  exact listTotal_nth_integrable ν L hL he hW b D hi (k+i)

end DirectionalZeroOne

end OAI
