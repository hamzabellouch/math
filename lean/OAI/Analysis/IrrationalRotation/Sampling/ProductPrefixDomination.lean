import OAI.Analysis.IrrationalRotation.Model.ProductPrefixDomination
import OAI.Analysis.IrrationalRotation.Sampling.PrefixDomination
import OAI.Analysis.IrrationalRotation.Couplings.ProductCoupling
import OAI.Analysis.IrrationalRotation.Product.ProductCoordinateSplit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling CouplingMixture

instance sourcePairLaw_isProbabilityMeasure (P : Parameters) (i : ℕ) :
    IsProbabilityMeasure (pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)) :=
  pairLaw_isProbabilityMeasure (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)

instance leftTailLaw_isProbabilityMeasure (P : Parameters) (D : ℕ) :
    IsProbabilityMeasure (leftTailLaw P D) := by
  have : ∀ i : TailIndex D,
      IsProbabilityMeasure ((coordinateLaw P i).map (fun z => z.2.1)) :=
    fun _ => inferInstance
  unfold leftTailLaw
  infer_instance

instance baseTailLaw_isProbabilityMeasure (D : ℕ) :
    IsProbabilityMeasure (baseTailLaw D) := by
  unfold baseTailLaw
  infer_instance

lemma assemblePrefixPair_measurable (D : ℕ) : Measurable (assemblePrefixPair D) := by
  apply Measurable.prodMk
  all_goals
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ Finset.range D
    · simp only [dite_eq_left hi]
      fun_prop
    · simp only [dite_eq_right hi]
      fun_prop

lemma prefixPairsLaw_absolutelyContinuous (P : Parameters) (D : ℕ) :
    prefixPairsLaw P D ≪ prefixReferenceLaw D := by
  unfold prefixPairsLaw prefixReferenceLaw
  rw [← Invariant233.pi_add_eq_sum_bool
    (fun _ : PrefixIndex D => diagonal baseLaw) (fun _ => triangleLaw)]
  apply Invariant233.fintype_pi_absolutelyContinuous
  intro i
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  exact pairLaw_absolutelyContinuous_diagonal_add_triangle
    (by linarith [P.m_ge i])
    (CouplingMarginalBounds.width_pos hm0 (P.a_lower i)) (P.a_upper i)
    (CouplingMarginalBounds.width_pos hm0 (P.b_lower i)) (P.b_upper i)

lemma prefix_payload_map (P : Parameters) (D : ℕ) :
    (law P).map (fun ω =>
      ((fun i : PrefixIndex D => (ω i).2), (fun i : TailIndex D => (ω i).2.1))) =
      (prefixPairsLaw P D).prod (leftTailLaw P D) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => CoordinateSample)
    (fun i => i ∈ Finset.range D)
  let f : (PrefixIndex D → CoordinateSample) → PrefixPairs D := fun ω i => (ω i).2
  let g : (TailIndex D → CoordinateSample) → TailValues D := fun ω i => (ω i).2.1
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have he := ProductCoordinateSplit.measurePreserving_split (coordinateLaw P)
    (fun i => i ∈ Finset.range D)
  have : ∀ i : PrefixIndex D, IsProbabilityMeasure ((coordinateLaw P i).map Prod.snd) :=
    fun _ => inferInstance
  have hp : (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)).map f =
      prefixPairsLaw P D := by
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_snd), Measure.infinitePi_eq_pi]
    simp only [coordinateLaw_map_pair]
    rfl
  have ht : (Measure.infinitePi (fun i : TailIndex D => coordinateLaw P i)).map g =
      leftTailLaw P D :=
    Measure.infinitePi_map_pi _ (fun _ => measurable_snd.fst)
  change (law P).map ((Prod.map f g) ∘ e) = _
  have heq : (law P).map e =
      (Measure.infinitePi (fun i : PrefixIndex D => coordinateLaw P i)).prod
        (Measure.infinitePi (fun i : TailIndex D => coordinateLaw P i)) := he.map_eq
  rw [← Measure.map_map (hf.prodMap hg) e.measurable, heq]
  rw [← Measure.map_prod_map _ _ hf hg, hp, ht]

lemma prefixPairLaw_factorization (P : Parameters) (D : ℕ) :
    prefixPairLaw P D =
      ((prefixPairsLaw P D).prod (leftTailLaw P D)).map (assemblePrefixPair D) := by
  rw [← prefix_payload_map]
  rw [Measure.map_map (assemblePrefixPair_measurable D) (by fun_prop)]
  unfold prefixPairLaw
  congr 1
  funext ω
  apply Prod.ext <;> funext i
  all_goals
    by_cases hi : i ∈ Finset.range D
    · simp_all [assemblePrefixPair, hybridEndpoint, leftEndpoint, rightEndpoint, Finset.mem_range]
    · simp_all [assemblePrefixPair, hybridEndpoint, leftEndpoint, rightEndpoint, Finset.mem_range]

lemma leftEndpoint_map_infinitePi (P : Parameters) :
    (law P).map leftEndpoint = Measure.infinitePi
      (fun i => (coordinateLaw P i).map (fun z => z.2.1)) :=
  Measure.infinitePi_map_pi _ (fun _ => measurable_snd.fst)

lemma leftTailLaw_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) : leftTailLaw P D ≪ baseTailLaw D := by
  obtain ⟨H, _, _, _, _, hH⟩ := exists_hybrid_density P (fun _ => false)
    hsum (le_refl (∑' i, energyBound P i))
  have hleft : (law P).map leftEndpoint =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
    have heq : hybridEndpoint (fun _ => false) = leftEndpoint := by
      funext ω i
      rfl
    rw [heq] at hH
    exact hH
  have hac : (law P).map leftEndpoint ≪ baseMeasure := by
    rw [hleft]
    exact withDensity_absolutelyContinuous _ _
  have hmap := hac.map (show Measurable (fun x (i : TailIndex D) => x i) from by fun_prop)
  rw [leftEndpoint_map_infinitePi] at hmap
  have : ∀ i, IsProbabilityMeasure ((coordinateLaw P i).map (fun z => z.2.1)) :=
    fun _ => inferInstance
  have htail : (Measure.infinitePi
      (fun i => (coordinateLaw P i).map (fun z => z.2.1))).map
      (fun x (i : TailIndex D) => x i) = leftTailLaw P D :=
    Measure.infinitePi_map_restrict' _
  have hbase : baseMeasure.map (fun x (i : TailIndex D) => x i) = baseTailLaw D :=
    Measure.infinitePi_map_restrict' _
  rwa [htail, hbase] at hmap

lemma prefixPairLaw_absolutelyContinuous (P : Parameters)
    (hsum : Summable (energyBound P)) (D : ℕ) :
    prefixPairLaw P D ≪ prefixReferencePairLaw D := by
  rw [prefixPairLaw_factorization]
  exact ((prefixPairsLaw_absolutelyContinuous P D).prod
    (leftTailLaw_absolutelyContinuous P hsum D)).map (assemblePrefixPair_measurable D)

end Invariant233.OrderedProductCoupling

end

end OAI
