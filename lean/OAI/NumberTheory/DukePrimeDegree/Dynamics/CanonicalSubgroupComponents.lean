import OAI.NumberTheory.DukePrimeDegree.Dynamics.LatticeInvariantVersions
import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizerKernelCovariance

namespace OAI

/-!
# Ergodic components over the full subgroup's invariant sigma algebra

The orbit averages come from a countable dense subgroup. Their L²
limits extend to the full group and have exactly invariant measurable
versions. Consequently the full invariant sigma conditional kernel,
the same kernel used by diagonal covariance, has ergodic components.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_canonical_subgroup_ergodic_decomposition
    {n : ℕ} (H : Subgroup (G n))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ) :
    condExpKernel μ (actionInvariantSigma H (X n)) ∘ₘ
        μ.trim (actionInvariantSigma_le H (X n)) = μ ∧
      ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
        ErgodicSMul H (X n) (condExpKernel μ (actionInvariantSigma H (X n)) z) := by
  classical
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense H
  let : Countable s := hs.to_subtype
  let S := FreeGroup s
  let φ : S →* H := FreeGroup.lift (fun a : s => (a : H))
  have hdφ : DenseRange φ := hd.mono (by
    intro h hh
    exact ⟨FreeGroup.of ⟨h, hh⟩, FreeGroup.lift_apply_of⟩)
  let : MulAction S (X n) := MulAction.compHom (X n) φ
  have hpS (a : S) : MeasurePreserving (fun x : X n => a • x) μ μ :=
    latticeSubgroup_preserving H μ hH (φ a)
  let m := actionInvariantSigma H (X n)
  let : MeasurableSpace (X n) := xMeasurableSpace n
  have hm : m ≤ xMeasurableSpace n := actionInvariantSigma_le H (X n)
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdec := invariant_kernel_decomposition m μ
    (fun a : S => fun x : X n => a • x) hpS hm (fun a => iInf_le _ (φ a))
  refine ⟨hdec.1, ?_⟩
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet (X n))
  have hCcount : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  let : Countable C := hCcount.to_subtype
  have hCgen : xMeasurableSpace n = MeasurableSpace.generateFrom C := by
    simp only [C, generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
    rfl
  have hCpi : IsPiSystem C := fun _ hA _ hB _ =>
    isSetAlgebra_generateSetAlgebra.inter_mem hA hB
  have hCm (B : C) : MeasurableSet (B : Set (X n)) := by
    change @MeasurableSet (X n) (xMeasurableSpace n) _
    rw [hCgen]
    exact MeasurableSpace.measurableSet_generateFrom B.property
  have hAv (B : C) := exists_invariant_orbit_average_limit μ hpS
    ((memLp_const (1 : ℝ)).indicator (hCm B) :
      MemLp ((B : Set (X n)).indicator (fun _ => (1 : ℝ))) 2 μ)
  choose v hv hvfix F hF hlim using hAv
  have hvLp (B : C) : MemLp (v B) 2 μ := by
    have hb : ∀ᵐ y ∂μ, v B y ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [hlim B] with y hy
      apply isClosed_Icc.mem_of_tendsto hy
      exact Eventually.of_forall fun k => orbitConvexHull_interval
        (fun x => by by_cases hx : x ∈ (B : Set (X n)) <;> simp [hx]) (hF B k) y
    exact memLp_of_bounded hb
      ((hv B).mono (actionInvariantSigma_le S (X n)) le_rfl).aestronglyMeasurable 2
  have hversions (B : C) : ∃ w : X n → ℝ, Measurable[m] w ∧ w =ᵐ[μ] v B := by
    have hfull := lattice_function_ae_fixed_of_dense H φ hdφ μ hH (v B) (hvLp B)
      (fun a => Eventually.of_forall (hvfix B a))
    obtain ⟨w, hw, heq, _⟩ := lattice_pointwise_invariant_version H μ hH (v B)
      ((hv B).mono (actionInvariantSigma_le S (X n)) le_rfl) (hvLp B) hfull
    exact ⟨w, hw, heq⟩
  choose w hw hweq using hversions
  have hlimw (B : C) : ∀ᵐ y ∂μ,
      Tendsto (fun k => F B k y) atTop (𝓝 (w B y)) := by
    filter_upwards [hlim B, hweq B] with y hy he
    rwa [he]
  have hlimfiber (B : C) : ∀ᵐ z ∂τ, ∀ᵐ y ∂κ z,
      Tendsto (fun k => F B k y) atTop (𝓝 (w B y)) := by
    apply Measure.ae_ae_of_ae_comp
    change ∀ᵐ y ∂κ ∘ₘ τ, Tendsto (fun k => F B k y) atTop (𝓝 (w B y))
    rw [show κ ∘ₘ τ = μ from hdec.1]
    exact hlimw B
  have hconst (B : C) : ∀ᵐ z ∂τ, ∀ᵐ y ∂κ z, w B y = w B z :=
    condExpKernel_ae_constant m μ hm (hw B)
  filter_upwards [hdec.2, ae_all_iff.mpr hlimfiber, ae_all_iff.mpr hconst]
    with z hz hzl hzc
  have hpSz (a : S) : MeasurePreserving (fun y : X n => a • y) (κ z) (κ z) :=
    ⟨(hpS a).measurable, hz a⟩
  have hSerg : ErgodicSMul S (X n) (κ z) := by
    apply ergodicSMul_of_orbit_indicator_limits (κ z) hpSz C hCgen hCpi
    intro B hB
    refine ⟨w ⟨B, hB⟩ z, F ⟨B, hB⟩, hF ⟨B, hB⟩, ?_⟩
    filter_upwards [hzl ⟨B, hB⟩, hzc ⟨B, hB⟩] with y hy hwy
    simpa only [hwy] using hy
  let : ErgodicSMul S (X n) (κ z) := hSerg
  have hpHz (h : H) : MeasurePreserving (fun y : X n => h • y) (κ z) (κ z) :=
    preserving_of_dense_action φ hdφ (κ z) hpSz h
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro h B hB
    exact (hpHz h).measure_preimage hB.nullMeasurableSet
  · intro B hB hfix
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := S) hB
    intro a
    exact hfix (φ a)

end DukePrimeDegree

end

end OAI
