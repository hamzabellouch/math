import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixSelfConditional

namespace OAI

/-! # Pointwise constancy of the actual future kernel on a conull chart

The normalized leaf measure depends only on the transverse coordinate.
After removing one null set, equal transverse coordinates and equal
complete future names therefore give exactly the same ambient kernel.
This is stronger than constancy for almost every pair sampled from that
kernel, and is the local input for the refined-future entropy comparison.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries=allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

lemma ae_coordinates_mem_of_ae_coordinateMeasure
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X (d+1)))
    (E : Set ((UpperRootTransverse (d+1) × V) × c.Time))
    (hE : ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ E) :
    ∀ᵐ x ∂μ, ∀ z ∈ B.domain, C.timeParam c hP hf g z=x → z ∈ E := by
  have hsub : ∀ᵐ z ∂μ.comap B.param, z.val ∈ E :=
    ae_of_ae_map measurable_subtype_coe.aemeasurable hE
  have H : ∀ᵐ x ∂(μ.comap B.param).map B.param,
      ∀ z : B.domain, B.param z=x → z.val ∈ E := by
    apply B.embedding.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hsub] with z hz w hw
    have he : w=z := B.embedding.injective hw
    simpa only [he] using hz
  rw [B.embedding.measurableEmbedding.map_comap] at H
  have H' := (ae_restrict_iff' B.range_open.measurableSet).mp H
  filter_upwards [H'] with x hx
  intro z hz hzx
  exact hx ⟨⟨z,hz⟩,hzx⟩ ⟨z,hz⟩ hzx

theorem exists_conull_futureKernel_coordinate_constancy
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v=x → v=1)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (κ : Kernel (X (d+1)) (X (d+1)))
    (hκ : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP hf g
    ∃ E : Set ((UpperRootTransverse (d+1) × V) × c.Time),
      (∀ᵐ z ∂B.coordinateMeasure μ, z ∈ E) ∧
      ∀ z ∈ E, ∀ w ∈ E, z.1=w.1 →
        (∀ k : ℕ, Q (T^[k+1] (F z))=Q (T^[k+1] (F w))) →
        κ (F z)=κ (F w) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP hf g
  let K := B.regularLeafKernel R hBR μ hfree
  let L := fun z : (UpperRootTransverse (d+1) × V) × c.Time =>
    ((anchorNormalize (K z.1) (countableFutureFiber T Q F z)).restrict
      (countableFutureFiber T Q F z)).map (fun t => F (z.1,t))
  have hspec : ∀ᵐ z ∂B.coordinateMeasure μ, κ (F z)=L z := by
    filter_upwards [B.ae_coordinate_of_ambient μ hκ,
      B.ae_normalized_uncentered_eq_regularLeaf R hBR μ hfree] with z hz hn
    rw [hz,←B.map_uncentered_future_eq_ambient μ ell hell Q 1 z]
    change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
      (countableFutureFiber T Q F z)).restrict
      (countableFutureFiber T Q F z)).map (fun t => F (z.1,t)))=L z
    rw [hn]
  refine ⟨{z | κ (F z)=L z},hspec,?_⟩
  intro z hz w hw hzw hname
  have hfiber : countableFutureFiber T Q F z=countableFutureFiber T Q F w := by
    ext t
    simp only [countableFutureFiber,mem_ofPred_eq]
    rw [hzw]
    exact forall_congr' (fun k => by rw [hname k])
  rw [hz,hw]
  change ((anchorNormalize (K z.1) (countableFutureFiber T Q F z)).restrict
      (countableFutureFiber T Q F z)).map (fun t => F (z.1,t)) = _
  rw [hzw,hfiber]

/-- One ambient conull set works for every pair of coordinates in this
actual injective box, rather than merely for almost every sampled pair. -/
theorem exists_conull_futureKernel_chart_constancy
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v=x → v=1)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (κ : Kernel (X (d+1)) (X (d+1)))
    (hκ : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP hf g
    ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
      ∀ z ∈ B.domain, ∀ w ∈ B.domain, F z ∈ E → F w ∈ E → z.1=w.1 →
        (∀ k : ℕ, Q (T^[k+1] (F z))=Q (T^[k+1] (F w))) →
        κ (F z)=κ (F w) := by
  obtain ⟨E,hE,hconst⟩ := B.exists_conull_futureKernel_coordinate_constancy
    R hBR μ hfree ell hell Q κ hκ
  let F := C.timeParam c hP hf g
  let A := {x | ∀ z ∈ B.domain, F z=x → z ∈ E}
  refine ⟨A,B.ae_coordinates_mem_of_ae_coordinateMeasure μ E hE,?_⟩
  intro z hz w hw hzA hwA hzw hname
  exact hconst z (hzA z hz rfl) w (hwA w hw rfl) hzw hname

end RootPrefixBox
end DukePrimeDegree

end

end OAI
