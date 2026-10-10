import OAI.Analysis.IrrationalRotation.Sampling.ProductPrefixDomination
import OAI.Analysis.IrrationalRotation.Analysis.RealTriangularLaw
import OAI.Analysis.IrrationalRotation.Couplings.PrefixHybrid

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

def referencePayload (D : ℕ) (xz : Endpoint × Endpoint) :
    PrefixPairs D × TailValues D :=
  ((fun i => (xz.1 i, xz.2 i)), fun i => xz.1 i)

lemma referencePayload_measurable (D : ℕ) :
    Measurable (referencePayload D) := by
  unfold referencePayload
  fun_prop

theorem referencePayload_map (D : ℕ) :
    (baseMeasure.prod baseMeasure).map (referencePayload D) =
      (Measure.pi (fun _ : PrefixIndex D =>
        OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw)).prod
          (baseTailLaw D) := by
  let A := PrefixIndex D → ℝ
  let μ : Measure A := Measure.pi (fun _ => OneCoordinateCoupling.baseLaw)
  let ν := baseTailLaw D
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => ℝ)
    (fun i => i ∈ Finset.range D)
  have hs : MeasurePreserving e baseMeasure (μ.prod ν) := by
    simpa only [e, μ, ν, A, baseMeasure, baseTailLaw, Measure.infinitePi_eq_pi] using
      ProductCoordinateSplit.measurePreserving_split
        (fun _ : ℕ => OneCoordinateCoupling.baseLaw) (fun i => i ∈ Finset.range D)
  have hr : MeasurePreserving (Finset.range D).restrict baseMeasure μ :=
    ⟨Finset.measurable_restrict _, Measure.infinitePi_map_restrict _⟩
  have ha := measurePreserving_prodAssoc μ ν μ
  have hb := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have hc := (measurePreserving_prodAssoc μ μ ν).symm
  have hd := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (PrefixIndex D)
    (fun _ => OneCoordinateCoupling.baseLaw)
    (fun _ => OneCoordinateCoupling.baseLaw)).symm
  have h := ((hd.prod (MeasurePreserving.id ν)).comp
    (hc.comp (hb.comp (ha.comp (hs.prod hr))))).map_eq
  convert h using 1
  congr 1

theorem referencePayload_restrict (D : ℕ) (s : Set (PrefixPairs D))
    (hs : MeasurableSet s) :
    ((baseMeasure.prod baseMeasure).restrict
      (referencePayload D ⁻¹' (s ×ˢ Set.univ))).map (referencePayload D) =
      ((Measure.pi (fun _ : PrefixIndex D =>
        OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw)).restrict s).prod
        (baseTailLaw D) := by
  rw [← Measure.restrict_map (referencePayload_measurable D) (hs.prod .univ),
    referencePayload_map, ← Measure.restrict_prod_eq_prod_univ]

theorem referencePayload_restrict_pi (D : ℕ) (s : PrefixIndex D → Set (ℝ × ℝ))
    (hs : ∀ i, MeasurableSet (s i)) :
    ((baseMeasure.prod baseMeasure).restrict
      (referencePayload D ⁻¹' ((Set.univ.pi s) ×ˢ Set.univ))).map (referencePayload D) =
      (Measure.pi (fun i : PrefixIndex D =>
        (OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw).restrict (s i))).prod
        (baseTailLaw D) := by
  rw [referencePayload_restrict D _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]

theorem uniform_pair_map_diagonal :
    (OneCoordinateCoupling.baseLaw.prod OneCoordinateCoupling.baseLaw).map
      (fun z : ℝ × ℝ => (z.1, z.1)) =
        CouplingMixture.diagonal OneCoordinateCoupling.baseLaw := by
  have hf : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  rw [show (fun z : ℝ × ℝ => (z.1, z.1)) = (fun x : ℝ => (x, x)) ∘ Prod.fst from rfl,
    ← Measure.map_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  rfl

theorem reference_map_prefixPairLaw_circle (P : Parameters) (D : ℕ) :
    (prefixPairLaw P D).map circlePairEndpoint =
      ProductModel.prefixPairLaw (circlePairLaw P) D := by
  rw [prefixPairLaw, Measure.map_map circlePairEndpoint_measurable (leftEndpoint_measurable.prodMk (hybridEndpoint_measurable _)),
    ProductModel.prefixPairLaw, circlePairLaw,
    Measure.map_map (ProductModel.measurable_prefixPair D)
      (circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable)]
  congr 1
  funext ω
  apply Prod.ext <;> funext i
  · rfl
  · by_cases hi : i < D <;> simp [hi, circlePairEndpoint, circleEndpoint, hybridEndpoint,
      ProductModel.prefixPair, ProductModel.prefixEndpoint_apply,
      circleLeftEndpoint, circleRightEndpoint, Finset.mem_range]

end Invariant233.OrderedProductCoupling

end

end OAI
