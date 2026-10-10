import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTuplePerturbation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CartanVanishingHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHaarInvariance
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SeparatedTupleVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProducts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceFiniteSubexponential

namespace OAI

/-! # Controlled Cartan increments from separated endpoint tuples

The actual factor action gives the small-height corrections. The resulting
measurable increment set retains the separate templates, its lower volume,
and the original thickened lifts of every endpoint.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup F.D.carrier]
  [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]

theorem exists_controlled_increment_volume
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (μ : Measure F.N.carrier) (ν : Measure F.D.carrier)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] [SigmaFinite μ] [SigmaFinite ν]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (h : ℕ) (E : Fin h → Set W)
    (hE : ∀ i, IsCompact (E i)) (h0 : ∀ i, (0 : W) ∈ E i) (β : Fin h → M.Bases)
    (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (E i)) (β i).val)
    (scale RH R η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) (hη : Tendsto η atTop (𝓝 0))
    (s : ℕ → Finset (Fin h → G))
    (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier))
    (U : Set ((Fin h → F.N.carrier) × (Fin h → F.D.carrier))) (hU : IsCompact U)
    {ρ : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin h → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ / 2)
    (hsep : ∀ n x, x ∈ s n → ∀ y, y ∈ s n → x ≠ y → ρ ≤ dist x y)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hh : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hinc : ∀ n x, x ∈ s n → ∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n)) :
    ∃ (Q : Fin h → ℕ → ℝ) (RD : ℕ → ℝ),
      (∀ i n, 0 ≤ Q i n) ∧ (∀ i, HasSubexponentialUpperBoundSeq scale (Q i)) ∧
      (∀ n, 0 ≤ RD n) ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n, ∃ I : Set (Fin h → F.N.carrier), IsCompact I ∧ MeasurableSet I ∧
        ((s n).card : ℝ≥0∞) * ((Measure.pi fun _ : Fin h => μ).prod
          (Measure.pi fun _ : Fin h => ν)) U ≤
          (Measure.pi fun _ : Fin h => μ) I *
            (Measure.pi fun _ : Fin h => ν)
              {d | ∀ i, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d i))‖ ≤ RD n} ∧
        (∀ u ∈ I, ∀ i, u i ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          (E i) (β i) (scale n) (Q i n)) ∧
        (∀ u ∈ I, ∃ x ∈ s n, ∃ z ∈ U,
          prefixCoordinateEquiv h u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let KN := ⋃ i : Fin h, (fun z : (Fin h → F.N.carrier) × (Fin h → F.D.carrier) => z.1 i) '' U
  let KD := ⋃ i : Fin h, (fun z : (Fin h → F.N.carrier) × (Fin h → F.D.carrier) => z.2 i) '' U
  have hKN : IsCompact KN := isCompact_iUnion (fun i => hU.image
    ((continuous_apply i).comp continuous_fst))
  have hKD : IsCompact KD := isCompact_iUnion (fun i => hU.image
    ((continuous_apply i).comp continuous_snd))
  obtain ⟨RN, hRN, hN⟩ := exists_compact_exponential_coordinate_bound F.N.equiv F.ExpN
    chartN hchartN (WordBasisSelections.basis M.letter M.wordList γ) hKN
  obtain ⟨RDC, hRDC, hD⟩ := exists_compact_exponential_coordinate_bound F.D.equiv F.ExpD
    chartD hchartD (finBasis ℝ H) hKD
  choose S hS0 hS hbound using fun i => M.exists_vanishing_height_adjoint_bound
    T hunimod eW b₀ (WordBasisSelections.basis M.letter M.wordList (β i))
    scale RH (fun _ => RN) η hs hscale hRH0 (fun _ => hRN) hRH
    (sequence_subexponential_upper_const hs RN) hη
  obtain ⟨SC, hSC0, hSC, hSle⟩ := finite_subexponential_envelope hs S hS0 hS
  obtain ⟨Q, hQ0, hQ, hperturb⟩ := M.exists_subexponential_tuple_perturbation T hunimod eW
    F.N.equiv F.ExpN F.isExpN dynkinN b₀ h E hE h0 β hβ scale R SC hs hscale hR0 hSC0 hR hSC
  obtain ⟨RD, hRD0, hRD, hprod⟩ := exists_sequence_cartan_product_bound H F.D.equiv F.ExpD hbijD
    F.isExpD dynkinD scale RH (fun _ => RDC) hs hRH0 (fun _ => hRDC) hRH
      (sequence_subexponential_upper_const hs RDC)
  have hφ := F.action_preserves_haar T M hExpG realize haarN haarD dynkinN hunimod μ
  have hφc (d : F.D.carrier) : Continuous (F.action d) := by
    apply F.closedN.isEmbedding.isInducing.continuous_iff.mpr
    change Continuous (fun u => F.inclusionN (F.action d u))
    simp only [F.conjugation]
    exact (continuous_const.mul F.closedN.continuous).mul continuous_const
  have hDlog (z) (hz : z ∈ U) (i : Fin h) :
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (z.2 i))‖ ≤ RDC := by
    obtain ⟨v, hv, hb⟩ := hD (mem_iUnion.mpr ⟨i, ⟨z, hz, rfl⟩⟩)
    change (F.ExpD ∘ F.D.equiv) v = z.2 i at hv
    rw [← hv]
    change ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (F.ExpD (F.D.equiv v)))‖ ≤ RDC
    simpa only [cartanLog_exp] using hb
  refine ⟨Q, RD, hQ0, hQ, hRD0, hRD, ?_⟩
  intro n
  obtain ⟨I, hIc, hI, hvol, hwitness⟩ := exists_increment_volume_of_separated_tuples F.action
    F.inclusionN F.inclusionD F.conjugation μ ν hφ hφc h (s n) (p n) U hU
    (hp n) hsmall (hsep n)
    {d | ∀ i, ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD (d i))‖ ≤ RD n}
    (by intro x hx z hz i; exact hprod n _ _ (hd n x hx i) (hDlog z hz i))
  refine ⟨I, hIc, hI, hvol, ?_, hwitness⟩
  intro u hu
  obtain ⟨x, hx, z, hz, he⟩ := hwitness u hu
  let η' := fun j => F.action ((p n x).2 j) (z.1 j)
  have hη' (i j : Fin h) : η' j ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
      (WordBasisSelections.basis M.letter M.wordList (β i)) (SC n) := by
    obtain ⟨v, hv, hb⟩ := hN (mem_iUnion.mpr ⟨j, ⟨z, hz, rfl⟩⟩)
    change (F.ExpN ∘ F.N.equiv) v = z.1 j at hv
    refine ⟨cartanIdealAdjointAutomorphism T H
      (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 j)) v, ?_,
        (hbound i n γ _ v (hd n x hx j) (hh n x hx j) hb).trans (hSle i n)⟩
    change F.ExpN _ = F.action ((p n x).2 j) (z.1 j)
    rw [← hv, cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      hbijN hbijD dynkinN]
    exact (integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbijN dynkinN F.isExpN
      M.bound_zero _ v).symm
  have hu' : u = (prefixCoordinateEquiv h).symm (fun j => (p n x).1 j * η' j) := by
    rw [← he, MeasurableEquiv.symm_apply_apply]
  rw [hu']
  exact hperturb n (p n x).1 η' (hinc n x hx) hη'

end PolycyclicRecognition.CartanWordModel

end

end OAI
