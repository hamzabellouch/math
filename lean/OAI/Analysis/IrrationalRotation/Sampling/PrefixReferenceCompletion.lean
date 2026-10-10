import OAI.Analysis.IrrationalRotation.Sampling.ProductPrefixCircle
import OAI.Analysis.IrrationalRotation.Sampling.PrefixReferenceIdentification

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling
open OneCoordinateCoupling CouplingMixture

def collapsePrefixPattern (D : ℕ) (pattern : PrefixIndex D → Bool)
    (z : PrefixPairs D) : PrefixPairs D :=
  fun i => if pattern i then z i else ((z i).1, (z i).1)

def prefixPatternEvent (D : ℕ) (pattern : PrefixIndex D → Bool) : Set (PrefixPairs D) :=
  {z | ∀ i, pattern i = true → (z i).1 < (z i).2}

lemma collapsePrefixPattern_measurable (D : ℕ) (pattern : PrefixIndex D → Bool) :
    Measurable (collapsePrefixPattern D pattern) := by
  apply Measurable.of_eval
  intro i
  cases hp : pattern i <;> simp only [collapsePrefixPattern, hp, Bool.false_eq_true,
    ite_false, ite_true] <;> fun_prop

lemma prefixPatternEvent_measurable (D : ℕ) (pattern : PrefixIndex D → Bool) :
    MeasurableSet (prefixPatternEvent D pattern) := by
  simp only [prefixPatternEvent, ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_lt ((measurable_pi_apply i).fst) ((measurable_pi_apply i).snd)

lemma prefixPattern_restrict_map (D : ℕ) (pattern : PrefixIndex D → Bool) :
    ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)).map (collapsePrefixPattern D pattern) =
      Measure.pi (fun i => if pattern i then triangleLaw else diagonal baseLaw) := by
  let A : PrefixIndex D → Set (ℝ × ℝ) :=
    fun i => if pattern i then {z | z.1 < z.2} else Set.univ
  have hA : prefixPatternEvent D pattern = Set.univ.pi A := by
    ext z
    simp only [prefixPatternEvent, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      forall_const]
    apply forall_congr'
    intro i
    cases hp : pattern i <;> simp [A, hp]
  rw [hA, Measure.restrict_pi_pi]
  have hm (i : PrefixIndex D) :
      Measurable (fun z : ℝ × ℝ => if pattern i then z else (z.1,z.1)) := by
    cases hp : pattern i <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      fun_prop
  have hi (i : PrefixIndex D) :
      ((baseLaw.prod baseLaw).restrict (A i)).map
        (fun z : ℝ × ℝ => if pattern i then z else (z.1,z.1)) =
        if pattern i then triangleLaw else diagonal baseLaw := by
    cases hp : pattern i
    · simpa [A, hp] using uniform_pair_map_diagonal
    · simp [A, hp, triangleLaw]
  have (i : PrefixIndex D) : IsFiniteMeasure ((baseLaw.prod baseLaw).restrict (A i)) :=
    inferInstance
  have (i : PrefixIndex D) : IsFiniteMeasure
      (((baseLaw.prod baseLaw).restrict (A i)).map
        (fun z : ℝ × ℝ => if pattern i then z else (z.1,z.1))) := inferInstance
  change (Measure.pi (fun i => (baseLaw.prod baseLaw).restrict (A i))).map
    (fun z i => if pattern i then z i else ((z i).1,(z i).1)) = _
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [hi]

def selectedPrefixPattern (D : ℕ) (pattern : PrefixIndex D → Bool) : Finset ℕ :=
  (Finset.univ.filter (fun i => pattern i = true)).image Subtype.val

lemma mem_selectedPrefixPattern (D : ℕ) (pattern : PrefixIndex D → Bool) (i : ℕ) :
    i ∈ selectedPrefixPattern D pattern ↔
      ∃ hi : i ∈ Finset.range D, pattern ⟨i, hi⟩ = true := by
  classical
  simp only [selectedPrefixPattern, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hji⟩
    subst i
    exact ⟨j.property, hj⟩
  · rintro ⟨hi, hp⟩
    exact ⟨⟨i, hi⟩, hp, rfl⟩

lemma selectedPrefixPattern_subset (D : ℕ) (pattern : PrefixIndex D → Bool) :
    selectedPrefixPattern D pattern ⊆ Finset.range D := by
  intro i hi
  exact ((mem_selectedPrefixPattern D pattern i).1 hi).choose

lemma mem_selectedPrefixPattern_subtype (D : ℕ) (pattern : PrefixIndex D → Bool)
    (i : PrefixIndex D) : i.val ∈ selectedPrefixPattern D pattern ↔ pattern i = true := by
  rw [mem_selectedPrefixPattern]
  exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨i.property, hp⟩⟩

lemma realTriangularEvent_eq_payload_preimage (D : ℕ) (pattern : PrefixIndex D → Bool) :
    realTriangularEvent (selectedPrefixPattern D pattern) =
      referencePayload D ⁻¹' (prefixPatternEvent D pattern ×ˢ Set.univ) := by
  ext xz
  change (∀ i ∈ selectedPrefixPattern D pattern, xz.1 i < xz.2 i) ↔ _
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
    prefixPatternEvent, Set.mem_ofPred_eq, referencePayload]
  constructor
  · intro h i hi
    exact h i ((mem_selectedPrefixPattern_subtype D pattern i).2 hi)
  · intro h i hi
    obtain ⟨hiD, hip⟩ := (mem_selectedPrefixPattern D pattern i).1 hi
    exact h ⟨i, hiD⟩ hip

lemma assemble_collapse_referencePayload (D : ℕ) (pattern : PrefixIndex D → Bool)
    (xz : Endpoint × Endpoint) :
    assemblePrefixPair D
      (collapsePrefixPattern D pattern (referencePayload D xz).1,
        (referencePayload D xz).2) =
      (xz.1, realSelectedEndpoint (selectedPrefixPattern D pattern) xz.1 xz.2) := by
  apply Prod.ext <;> funext i
  · by_cases hi : i ∈ Finset.range D
    · cases hp : pattern ⟨i, hi⟩ <;>
        simp only [assemblePrefixPair, dite_eq_left hi, collapsePrefixPattern, referencePayload, hp, Bool.false_eq_true, ite_false, ite_true]
    · simp only [assemblePrefixPair, dite_eq_right hi, referencePayload]
  · by_cases hi : i ∈ Finset.range D
    · have hmem := mem_selectedPrefixPattern_subtype D pattern ⟨i, hi⟩
      cases hp : pattern ⟨i, hi⟩ <;>
        simp only [assemblePrefixPair, dite_eq_left hi, collapsePrefixPattern, referencePayload, hp, Bool.false_eq_true, ite_false, ite_true]
      all_goals simp_all only [realSelectedEndpoint, Bool.false_eq_true, not_false_eq_true, ite_eq_left, ite_eq_right]
    · have hn : i ∉ selectedPrefixPattern D pattern :=
        fun h => hi (selectedPrefixPattern_subset D pattern h)
      simp only [assemblePrefixPair, dite_eq_right hi, referencePayload, realSelectedEndpoint, ite_eq_right hn]

theorem prefixPatternLaw_eq_realTriangularLaw (D : ℕ) (pattern : PrefixIndex D → Bool) :
    ((Measure.pi (fun i : PrefixIndex D =>
      if pattern i then triangleLaw else CouplingMixture.diagonal baseLaw)).prod
        (baseTailLaw D)).map (assemblePrefixPair D) =
      realTriangularLaw (selectedPrefixPattern D pattern) := by
  have : IsFiniteMeasure (Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)) :=
    inferInstance
  have : IsFiniteMeasure ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)) := inferInstance
  have : SigmaFinite ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)) := IsFiniteMeasure.toSigmaFinite _
  let R : PrefixPairs D × TailValues D → PrefixPairs D × TailValues D :=
    Prod.map (collapsePrefixPattern D pattern) id
  have hR : Measurable R := (collapsePrefixPattern_measurable D pattern).prodMap measurable_id
  have hfun : (fun xz : Endpoint × Endpoint =>
      (xz.1, realSelectedEndpoint (selectedPrefixPattern D pattern) xz.1 xz.2)) =
      (assemblePrefixPair D ∘ R) ∘ referencePayload D := by
    funext xz
    exact (assemble_collapse_referencePayload D pattern xz).symm
  symm
  rw [realTriangularLaw, hfun, realTriangularEvent_eq_payload_preimage,
    ← Measure.map_map ((assemblePrefixPair_measurable D).comp hR)
      (referencePayload_measurable D),
    referencePayload_restrict D _ (prefixPatternEvent_measurable D pattern),
    ← Measure.map_map (assemblePrefixPair_measurable D) hR]
  change (((((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
      (prefixPatternEvent D pattern)).prod (baseTailLaw D)).map
        (Prod.map (collapsePrefixPattern D pattern) id)).map (assemblePrefixPair D)) = _
  rw [← Measure.map_prod_map
      ((Measure.pi (fun _ : PrefixIndex D => baseLaw.prod baseLaw)).restrict
        (prefixPatternEvent D pattern)) (baseTailLaw D)
      (collapsePrefixPattern_measurable D pattern) measurable_id,
    Measure.map_id, prefixPattern_restrict_map]

theorem prefixReferencePairLaw_absolutelyContinuous (D : ℕ) :
    prefixReferencePairLaw D ≪
      ∑ I ∈ (Finset.range D).powerset, realTriangularLaw I := by
  classical
  unfold prefixReferencePairLaw prefixReferenceLaw
  rw [← Measure.sum_fintype, Measure.prod_sum_left,
    Measure.map_sum (assemblePrefixPair_measurable D).aemeasurable]
  apply Measure.absolutelyContinuous_sum_left
  intro pattern
  rw [prefixPatternLaw_eq_realTriangularLaw]
  apply Measure.absolutelyContinuous_of_le
  exact Finset.single_le_sum (fun I _ => bot_le)
    (Finset.mem_powerset.mpr (selectedPrefixPattern_subset D pattern))

theorem circle_prefix_absolutelyContinuous_triangular_sum (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) :
    ProductModel.prefixPairLaw (circlePairLaw P) D ≪
      ∑ I ∈ (Finset.range D).powerset, ProductModel.triangularLaw I := by
  have h := map_absolutelyContinuous_sum_triangularLaw (Finset.range D).powerset
    ((prefixPairLaw_absolutelyContinuous P hsum D).trans
      (prefixReferencePairLaw_absolutelyContinuous D))
  simpa only [map_prefixPairLaw_circle] using h

end Invariant233.OrderedProductCoupling

end

end OAI
