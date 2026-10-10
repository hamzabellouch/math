import OAI.Analysis.IrrationalRotation.Sampling.ProductPrefixDomination
import OAI.Analysis.IrrationalRotation.Sampling.ProductPrefixConditioning

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Invariant233.ProductCoordinateSplit

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

theorem map_split_cond_prefix
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p]
    (s : Set ((i : Subtype p) → X i)) (hs : MeasurableSet s) :
    (cond (Measure.infinitePi μ)
      ((fun x (i : Subtype p) => x i) ⁻¹' s)).map
      (MeasurableEquiv.piEquivPiSubtypeProd X p) =
    (cond (Measure.infinitePi (fun i : Subtype p => μ i)) s).prod
      (Measure.infinitePi (fun i : {i // ¬p i} => μ i)) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd X p
  have he := measurePreserving_split μ p
  have hpre : (fun x (i : Subtype p) => x i) ⁻¹' s =
      e ⁻¹' (s ×ˢ (Set.univ : Set ((i : {i // ¬p i}) → X i))) := by
    ext x
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  have hprefix : MeasurePreserving (fun x (i : Subtype p) => x i)
      (Measure.infinitePi μ) (Measure.infinitePi fun i : Subtype p => μ i) :=
    measurePreserving_fst.comp he
  have hmass : Measure.infinitePi μ ((fun x (i : Subtype p) => x i) ⁻¹' s) =
      Measure.infinitePi (fun i : Subtype p => μ i) s :=
    hprefix.measure_preimage hs.nullMeasurableSet
  change (cond (Measure.infinitePi μ) _).map e = _
  rw [ProbabilityTheory.cond, Measure.map_smul _ e.measurable.aemeasurable, hmass, hpre,
    ← Measure.restrict_map e.measurable (hs.prod MeasurableSet.univ), he.map_eq,
    ← Measure.prod_restrict, Measure.restrict_univ, ProbabilityTheory.cond, Measure.prod_smul_left]

end Invariant233.ProductCoordinateSplit

namespace Invariant233.OrderedProductCoupling

theorem prefix_payload_cond_map (P : Parameters) (D : ℕ)
    (s : Set (PrefixIndex D → CoordinateSample)) (hs : MeasurableSet s) :
    (cond (law P) ((fun ω (i : PrefixIndex D) => ω i) ⁻¹' s)).map
      (fun ω => ((fun i : PrefixIndex D => (ω i).2),
        (fun i : TailIndex D => (ω i).2.1))) =
    ((cond (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)) s).map
      (fun ω (i : PrefixIndex D) => (ω i).2)).prod (leftTailLaw P D) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => CoordinateSample)
    (fun i => i ∈ Finset.range D)
  let f : (PrefixIndex D → CoordinateSample) → PrefixPairs D := fun ω i => (ω i).2
  let g : (TailIndex D → CoordinateSample) → TailValues D := fun ω i => (ω i).2.1
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have he : (cond (law P) ((fun ω (i : PrefixIndex D) => ω i) ⁻¹' s)).map e =
      (cond (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)) s).prod
        (Measure.infinitePi (fun i : TailIndex D => coordinateLaw P i)) :=
    ProductCoordinateSplit.map_split_cond_prefix (coordinateLaw P)
      (fun i => i ∈ Finset.range D) s hs
  have ht : (Measure.infinitePi (fun i : TailIndex D => coordinateLaw P i)).map g =
      leftTailLaw P D :=
    Measure.infinitePi_map_pi _ (fun _ => measurable_snd.fst)
  change (cond (law P) _).map ((Prod.map f g) ∘ e) = _
  rw [← Measure.map_map (hf.prodMap hg) e.measurable, he,
    ← Measure.map_prod_map _ _ hf hg, ht]

theorem prefixPairLaw_cond_factorization (P : Parameters) (D : ℕ)
    (s : Set (PrefixIndex D → CoordinateSample)) (hs : MeasurableSet s) :
    (cond (law P) ((fun ω (i : PrefixIndex D) => ω i) ⁻¹' s)).map
      (fun ω => (leftEndpoint ω,
        hybridEndpoint (fun i => decide (i ∈ Finset.range D)) ω)) =
    (((cond (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)) s).map
      (fun ω (i : PrefixIndex D) => (ω i).2)).prod
        (leftTailLaw P D)).map (assemblePrefixPair D) := by
  rw [← prefix_payload_cond_map P D s hs,
    Measure.map_map (assemblePrefixPair_measurable D) (by fun_prop)]
  congr 1
  funext ω
  apply Prod.ext <;> funext i
  all_goals
    by_cases hi : i ∈ Finset.range D
    · simp_all [assemblePrefixPair, hybridEndpoint, leftEndpoint, rightEndpoint,
        Finset.mem_range]
    · simp_all [assemblePrefixPair, hybridEndpoint, leftEndpoint, rightEndpoint,
        Finset.mem_range]

theorem prefixPairLaw_cond_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) (s : Set Sample) :
    (cond (law P) s).map (fun ω => (leftEndpoint ω,
      hybridEndpoint (fun i => decide (i ∈ Finset.range D)) ω)) ≪
      prefixReferencePairLaw D := by
  have h := (cond_absolutelyContinuous (μ := law P) (s := s)).map
    (leftEndpoint_measurable.prodMk
      (hybridEndpoint_measurable (fun i => decide (i ∈ Finset.range D))))
  exact h.trans (prefixPairLaw_absolutelyContinuous P hsum D)

end Invariant233.OrderedProductCoupling

namespace Invariant233.ProductCoordinateSplit

theorem cond_fintype_pi {ι : Type*} {X : ι → Type*} [Fintype ι]
    [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (s : (i : ι) → Set (X i)) :
    cond (Measure.pi μ) (Set.univ.pi s) =
      Measure.pi (fun i => cond (μ i) (s i)) := by
  classical
  symm
  apply Measure.pi_eq
  intro t ht
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi ht),
    ← Set.pi_inter_distrib, Measure.pi_pi, Measure.pi_pi]
  simp_rw [Measure.restrict_apply (ht _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact (ENNReal.prod_inv_distrib (fun i hi j hj hij => Or.inr (measure_ne_top (μ j) (s j))))

end Invariant233.ProductCoordinateSplit

namespace Invariant233.OrderedProductCoupling

theorem prefix_label_cond_eq_pi (P : Parameters) (D : ℕ)
    (c : PrefixIndex D → Option (Fin 5)) :
    cond (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i))
      {ω | ∀ i, (ω i).1 = c i} =
    Measure.pi (fun i : PrefixIndex D => cond (coordinateLaw P i) {z | z.1 = c i}) := by
  rw [Measure.infinitePi_eq_pi]
  have hset : {ω : PrefixIndex D → CoordinateSample | ∀ i, (ω i).1 = c i} =
      Set.univ.pi (fun i : PrefixIndex D => {z : CoordinateSample | z.1 = c i}) := by
    ext ω
    simp
  rw [hset]
  exact ProductCoordinateSplit.cond_fintype_pi
    (fun i : PrefixIndex D => coordinateLaw P i) (fun i => {z | z.1 = c i})

end Invariant233.OrderedProductCoupling

namespace Invariant233.OrderedProductCoupling

theorem prefix_label_pair_factorization (P : Parameters) (D : ℕ)
    (c : PrefixIndex D → Option (Fin 5)) :
    (cond (law P) {ω | ∀ i : PrefixIndex D, (ω i).1 = c i}).map
      (fun ω => (leftEndpoint ω,
        hybridEndpoint (fun i => decide (i ∈ Finset.range D)) ω)) =
    ((Measure.pi (fun i : PrefixIndex D =>
      (cond (coordinateLaw P i) {z | z.1 = c i}).map Prod.snd)).prod
        (leftTailLaw P D)).map (assemblePrefixPair D) := by
  have hs : MeasurableSet {ω : PrefixIndex D → CoordinateSample |
      ∀ i, (ω i).1 = c i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton (c i))
  have h := prefixPairLaw_cond_factorization P D _ hs
  rw [prefix_label_cond_eq_pi] at h
  have : ∀ i : PrefixIndex D, IsFiniteMeasure
      ((cond (coordinateLaw P i) {z | z.1 = c i}).map
        (Prod.snd : CoordinateSample → ℝ × ℝ)) := fun _ => inferInstance
  rw [Measure.pi_map_pi (X := fun _ : PrefixIndex D => CoordinateSample)
    (Y := fun _ : PrefixIndex D => ℝ × ℝ) (μ := fun i : PrefixIndex D =>
    cond (coordinateLaw P i) {z | z.1 = c i})
      (f := fun _ => Prod.snd) (hμ := fun i => inferInstance) (fun _ => measurable_snd.aemeasurable)] at h
  exact h

end Invariant233.OrderedProductCoupling

end

end OAI
