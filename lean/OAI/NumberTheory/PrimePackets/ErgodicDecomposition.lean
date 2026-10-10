import Mathlib
import OAI.NumberTheory.PrimePackets.KernelEntropy

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
namespace PrimeDegreePackets

 

theorem condExpKernel_invariant {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hm : m ≤ mY) {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hfix : m ≤ MeasurableSpace.invariants T) :
    ∀ᵐ x ∂μ.trim hm, Measure.map T (condExpKernel μ m x) = condExpKernel μ m x := by
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdiag : τ ⊗ₘ κ = @Measure.map Y (Y × Y) mY (m.prod mY) Function.diag μ :=
    compProd_trim_condExpKernel hm
  have hprod : τ ⊗ₘ κ.map T = τ ⊗ₘ κ := by
    rw [Measure.compProd_map hT.measurable, hdiag]
    apply Measure.ext_prod
    intro A B hA hB
    have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
      (measurable_id'' hm).prodMk measurable_id
    rw [Measure.map_apply (measurable_id.prodMap hT.measurable) (hA.prod hB),
      Measure.map_apply hδ
        ((measurable_id.prodMap hT.measurable) (hA.prod hB)),
      Measure.map_apply hδ (hA.prod hB)]
    change μ (A ∩ T ⁻¹' B) = μ (A ∩ B)
    conv_lhs => rw [← (hfix _ hA).2, ← Set.preimage_inter]
    exact hT.measure_preimage ((hm _ hA |>.inter hB).nullMeasurableSet)
  let : IsMarkovKernel (κ.map T) := Kernel.IsMarkovKernel.map κ hT.measurable
  have H₁ := condKernel_compProd τ (κ.map T)
  have H₂ := condKernel_compProd τ κ
  have H₁' : (τ ⊗ₘ κ).condKernel =ᵐ[τ] κ.map T := by
    simpa only [hprod] using H₁
  have H := H₁'.symm.trans H₂
  filter_upwards [H] with x hx
  change (κ.map T) x = κ x at hx
  simpa only [Kernel.map_apply _ hT.measurable] using hx

 

theorem invariant_kernel_decomposition {Y I : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Countable I]
    (μ : Measure Y) [IsProbabilityMeasure μ] (T : I → Y → Y)
    (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hm : m ≤ mY)
    (hfix : ∀ i, m ≤ MeasurableSpace.invariants (T i)) :
    condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
      ∀ᵐ x ∂μ.trim hm, ∀ i, Measure.map (T i) (condExpKernel μ m x) =
        condExpKernel μ m x := by
  exact ⟨condExpKernel_comp_trim hm, ae_all_iff.mpr
    (fun i => condExpKernel_invariant m μ hm (hT i) (hfix i))⟩

 

theorem condExpKernel_ae_constant {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hm : m ≤ mY) {f : Y → ℝ} (hf : Measurable[m] f) :
    ∀ᵐ x ∂μ.trim hm, ∀ᵐ y ∂condExpKernel μ m x, f y = f x := by
  have hfull : Measurable f := hf.mono hm le_rfl
  have hset : @MeasurableSet (Y × Y) (m.prod mY) {p | f p.2 = f p.1} :=
    measurableSet_eq_fun (hfull.comp measurable_snd) (hf.comp measurable_fst)
  let : MeasurableSpace (Y × Y) := m.prod mY
  apply (Measure.ae_compProd_iff hset).mp
  rw [compProd_trim_condExpKernel hm]
  have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  exact (@ae_map_iff Y (Y × Y) mY (m.prod mY) μ Function.diag
    hδ.aemeasurable (fun p => f p.2 = f p.1) hset).mpr
      (Eventually.of_forall fun _ => rfl)

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem action_ergodic_decomposition {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [mY : MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ) :
    condExpKernel μ (actionInvariantSigma H Y) ∘ₘ
      μ.trim (actionInvariantSigma_le H Y) = μ ∧
      ∀ᵐ x ∂μ.trim (actionInvariantSigma_le H Y),
        ErgodicSMul H Y (condExpKernel μ (actionInvariantSigma H Y) x) := by
  let m := actionInvariantSigma H Y
  let : MeasurableSpace Y := mY
  let hm := actionInvariantSigma_le H Y
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdec := invariant_kernel_decomposition m μ (fun g : H => fun y : Y => g • y)
    hp hm (fun g => iInf_le _ g)
  refine ⟨hdec.1,?_⟩
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet Y)
  have hCcount : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  have hCgen : mY = MeasurableSpace.generateFrom C := by
    simp only [C,generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
    rfl
  have hCpi : IsPiSystem C := fun _ hA _ hB _ =>
    isSetAlgebra_generateSetAlgebra.inter_mem hA hB
  have hCm (B : C) : MeasurableSet (B : Set Y) := by
    change @MeasurableSet Y mY _
    rw [hCgen]
    exact MeasurableSpace.measurableSet_generateFrom B.property
  let : Countable C := hCcount.to_subtype
  have hAv (B : C) := exists_invariant_orbit_average_limit μ hp
    ((memLp_const (1:ℝ)).indicator (hCm B) :
      MemLp ((B:Set Y).indicator (fun _ => (1:ℝ))) 2 μ)
  choose v hv hvfix F hF hlim using hAv
  have hlimfiber (B : C) : ∀ᵐ x ∂τ, ∀ᵐ y ∂κ x,
      Tendsto (fun k => F B k y) atTop (𝓝 (v B y)) := by
    apply Measure.ae_ae_of_ae_comp
    change ∀ᵐ y ∂κ ∘ₘ τ, Tendsto (fun k => F B k y) atTop (𝓝 (v B y))
    rw [show κ ∘ₘ τ = μ from hdec.1]
    exact hlim B
  have hconst (B : C) : ∀ᵐ x ∂τ, ∀ᵐ y ∂κ x, v B y = v B x :=
    condExpKernel_ae_constant m μ hm (hv B)
  filter_upwards [hdec.2,ae_all_iff.mpr hlimfiber,ae_all_iff.mpr hconst]
    with x hx hxl hxc
  have hpx (g : H) : MeasurePreserving (fun y : Y => g • y) (κ x) (κ x) :=
    ⟨(hp g).measurable,hx g⟩
  apply ergodicSMul_of_orbit_indicator_limits (κ x) hpx C hCgen hCpi
  intro B hB
  refine ⟨v ⟨B,hB⟩ x,F ⟨B,hB⟩,hF ⟨B,hB⟩,?_⟩
  filter_upwards [hxl ⟨B,hB⟩,hxc ⟨B,hB⟩] with y hy hyc
  simpa only [hyc] using hy

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem preserving_of_dense_action {G H Y : Type*} [Group G] [Group H]
    [TopologicalSpace G] [FirstCountableTopology G] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [HasOuterApproxClosed Y] [MulAction G Y] [ContinuousSMul G Y]
    («φ» : H →* G) (hdense : DenseRange «φ») (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ h : H, MeasurePreserving (fun y : Y => «φ» h • y) ν ν) (g : G) :
    MeasurePreserving (fun y : Y => g • y) ν ν := by
  refine ⟨(continuous_const_smul g).measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (continuous_const_smul g).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  have hcont : Continuous (fun a : G => ∫ y, f (a • y) ∂ν) :=
    continuous_of_dominated
      (fun a => (f.continuous.comp (continuous_const_smul a)).aestronglyMeasurable)
      (fun a => ae_of_all _ (fun y => f.norm_coe_le_norm (a • y)))
      (integrable_const ‖f‖)
      (ae_of_all _ (fun y => f.continuous.comp (continuous_id.smul continuous_const)))
  refine hdense.induction_on (p := fun a : G => (∫ y, f (a • y) ∂ν) = ∫ y, f y ∂ν)
    g (isClosed_eq hcont continuous_const) ?_
  intro h
  rw [← integral_map (hp h).measurable.aemeasurable f.continuous.aestronglyMeasurable,
    (hp h).map_eq]

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem continuous_action_ergodic_decomposition {G Y : Type*} [Group G]
    [TopologicalSpace G] [FirstCountableTopology G] [TopologicalSpace.SeparableSpace G] [TopologicalSpace Y] [mY : MeasurableSpace Y]
    [BorelSpace Y] [HasOuterApproxClosed Y] [StandardBorelSpace Y] [Nonempty Y]
    [MulAction G Y] [ContinuousSMul G Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hp : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ) :
    ∃ (m : MeasurableSpace Y) (hm : m ≤ mY),
      letI : MeasurableSpace Y := mY
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
        ∀ᵐ x ∂μ.trim hm, ErgodicSMul G Y (condExpKernel μ m x) := by
  obtain ⟨s,hs,hd⟩ := TopologicalSpace.exists_countable_dense G
  let : Countable s := hs.to_subtype
  let H := FreeGroup s
  let «φ» : H →* G := FreeGroup.lift (fun a : s => (a:G))
  have hdφ : DenseRange «φ» := hd.mono (by
    intro g hg
    exact ⟨FreeGroup.of ⟨g,hg⟩,FreeGroup.lift_apply_of⟩)
  let : MulAction H Y := MulAction.compHom Y «φ»
  have hpH (h : H) : MeasurePreserving (fun y : Y => h • y) μ μ := hp («φ» h)
  have hdec := action_ergodic_decomposition μ hpH
  refine ⟨actionInvariantSigma H Y,actionInvariantSigma_le H Y,hdec.1,?_⟩
  filter_upwards [hdec.2] with x hx
  let ν := condExpKernel μ (actionInvariantSigma H Y) x
  let : ErgodicSMul H Y ν := hx
  have hν (g : G) : MeasurePreserving (fun y : Y => g • y) ν ν :=
    preserving_of_dense_action «φ» hdφ ν (fun h =>
      ⟨(hp («φ» h)).measurable,by
        ext B hB
        rw [Measure.map_apply (hp («φ» h)).measurable hB]
        exact SMulInvariantMeasure.measure_preimage_smul h hB⟩) g
  refine { measure_preimage_smul := fun g _ hs => (hν g).measure_preimage hs.nullMeasurableSet
           aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  intro B hB hBfix
  exact ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hB (fun h : H => hBfix («φ» h))

end PrimeDegreePackets

open MeasureTheory Set Topology UniformSpace TopologicalSpace
namespace PrimeDegreePackets

lemma standardBorel_of_measurableEquiv {Y Z : Type*} [MeasurableSpace Y]
    [MeasurableSpace Z] [StandardBorelSpace Z] (e : Y ≃ᵐ Z) : StandardBorelSpace Y := by
  let := upgradeStandardBorel Z
  let : TopologicalSpace Y := (inferInstance : TopologicalSpace Z).induced e
  have : BorelSpace Y := e.measurableEmbedding.borelSpace ⟨rfl⟩
  have : PolishSpace Y := e.toEquiv.polishSpace_induced
  infer_instance

 

theorem standardBorel_of_sigmaCompact {Y : Type*} [TopologicalSpace Y]
    [MetrizableSpace Y] [TopologicalSpace.SeparableSpace Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] : StandardBorelSpace Y := by
  let : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  let : MeasurableSpace (Completion Y) := borel (Completion Y)
  have : BorelSpace (Completion Y) := ⟨rfl⟩
  have he : IsEmbedding (fun y : Y => (y : Completion Y)) :=
    Completion.coe_isometry.isEmbedding
  have hm : MeasurableSet (range (fun y : Y => (y : Completion Y))) := by
    have H : range (fun y : Y => (y : Completion Y)) =
        ⋃ n, (fun y : Y => (y : Completion Y)) '' compactCovering Y n := by
      rw [←image_iUnion,iUnion_compactCovering,image_univ]
    rw [H]
    exact MeasurableSet.iUnion (fun n =>
      ((isCompact_compactCovering Y n).image he.continuous).isClosed.measurableSet)
  let : StandardBorelSpace (range (fun y : Y => (y : Completion Y))) := hm.standardBorel
  exact standardBorel_of_measurableEquiv he.toHomeomorph.toMeasurableEquiv

end PrimeDegreePackets


namespace PrimeDegreePackets

instance xStandardBorel (n : ℕ) : StandardBorelSpace (X n) :=
  standardBorel_of_sigmaCompact

 
instance diagonalLogAction (d : ℕ) : MulAction (Multiplicative (LogCoordinates d)) (X (d+1)) where
  smul u x := rightAction x (diagonalFlow u.toAdd)
  one_smul x := by
    change rightAction x (diagonalFlow 0) = x
    rw [diagonalFlow_zero,rightAction_one]
  mul_smul u v x := by
    change rightAction x (diagonalFlow (u.toAdd + v.toAdd)) =
      rightAction (rightAction x (diagonalFlow v.toAdd)) (diagonalFlow u.toAdd)
    rw [rightAction_mul,←diagonalFlow_add,add_comm u.toAdd v.toAdd]

instance diagonalLogAction_continuous (d : ℕ) :
    ContinuousSMul (Multiplicative (LogCoordinates d)) (X (d+1)) where
  continuous_smul := by
    change Continuous (fun p : Multiplicative (LogCoordinates d) × X (d+1) =>
      rightAction p.2 (diagonalFlow p.1.toAdd))
    exact (continuous_rightAction_uncurry (d+1)).comp
      (continuous_snd.prodMk ((continuous_diagonalFlow d).comp continuous_fst))

 

theorem diagonal_positive_ergodic_decomposition (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ)
    (hball : OrdinaryBallBound (d+1) μ) :
    ∃ (m : MeasurableSpace (X (d+1))) (hm : m ≤ xMeasurableSpace (d+1)),
      let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
      ∀ᵐ z ∂μ.trim hm,
        ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) (condExpKernel μ m z) ∧
        0 < measureEntropy (condExpKernel μ m z)
          (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
            (regularDiagonalWeights_sum d) 1)) := by
  have hp (u : Multiplicative (LogCoordinates d)) :
      MeasurePreserving (fun x : X (d+1) => u • x) μ μ :=
    ⟨(continuous_rightAction _).measurable,hA u.toAdd⟩
  obtain ⟨m,hm,hdec,herg⟩ := continuous_action_ergodic_decomposition μ hp
  let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
  refine ⟨m,hm,hdec,?_⟩
  have hinv : ∀ᵐ z ∂μ.trim hm, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (condExpKernel μ m z) =
        condExpKernel μ m z := by
    filter_upwards [herg] with z hz
    let := hz
    intro u
    exact (measurePreserving_smul (Multiplicative.ofAdd u) (condExpKernel μ m z)).map_eq
  have hball' : OrdinaryBallBound (d+1) (condExpKernel μ m ∘ₘ μ.trim hm) := by
    rw [hdec]
    exact hball
  have hprobtrim : @IsProbabilityMeasure (X (d+1)) m (μ.trim hm) := by
    constructor
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_univ
  have hpos := @positive_entropy_components_ae d (X (d+1)) m
    (μ.trim hm) hprobtrim (condExpKernel μ m) inferInstance hball' hinv
  exact herg.and hpos

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem packet_probability_subsequence_bounded_discr (d : ℕ) (hodd : Odd (d+1))
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (N : ℕ) (hN : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    ∃ (ν : ProbabilityMeasure (X (d+1))) («φ» : ℕ → ℕ), StrictMono «φ» ∧
      Tendsto (fun i => packetProbability (M («φ» i)) (σ («φ» i)) (hn («φ» i)) hodd)
        atTop (𝓝 ν) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  have htight := packet_tight_bounded_discr d hodd K M σ hn N hN hQ
  let p := fun i => packetProbability (M i) (σ i) (hn i) hodd
  have ht : IsTightMeasureSet {((μ : ProbabilityMeasure (X (d+1))) : Measure (X (d+1))) |
      μ ∈ Set.range p} := by
    convert htight using 1
    ext μ
    simp only [Set.mem_ofPred_eq,Set.mem_range]
    constructor
    · rintro ⟨ν,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨p i,⟨i,rfl⟩,rfl⟩
  obtain ⟨ν,_,«φ»,hφ,hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
      (fun i => subset_closure (Set.mem_range_self i))
  exact ⟨ν,«φ»,hφ,hlim⟩

 

theorem packet_limit_positive_ergodic_components_bounded_discr
    (d : ℕ) (hodd : Odd (d+1))
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (N : ℕ) (hN : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν)) :
    ∃ (m : MeasurableSpace (X (d+1))) (hm : m ≤ xMeasurableSpace (d+1)),
      let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
      condExpKernel (ν : Measure (X (d+1))) m ∘ₘ (ν : Measure (X (d+1))).trim hm = ν ∧
      ∀ᵐ z ∂(ν : Measure (X (d+1))).trim hm,
        ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
          (condExpKernel (ν : Measure (X (d+1))) m z) ∧
        0 < measureEntropy (condExpKernel (ν : Measure (X (d+1))) m z)
          (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
            (regularDiagonalWeights_sum d) 1)) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  apply diagonal_positive_ergodic_decomposition d ν
  · exact packet_limit_diagonal_invariant d hodd K M σ hn ν hlim
  · intro Ω hΩ
    exact packet_limit_ball_bound_bounded_discr d hodd K M σ hn N hN hQ ν hlim hΩ

end PrimeDegreePackets

open scoped ENNReal Topology
namespace PrimeDegreePackets

section Transitive
variable {H Y : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
  [MeasurableSpace Y]

 

theorem ae_constant_of_transitive_right_action
    (a : Y → H → Y) (ha : Measurable (fun p : Y × H => a p.1 p.2))
    (hmul : ∀ x g h, a (a x g) h = a x (g*h))
    (htrans : ∀ x y, ∃ g, a x g = y)
    (η : Measure H) [SigmaFinite η] [η.IsMulLeftInvariant] [NeZero η]
    (ρ : Measure Y) [SigmaFinite ρ] [NeZero ρ]
    (f : Y → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ g, (fun x => f (a x g)) =ᵐ[ρ] f) :
    ∃ c : ℝ≥0∞, f =ᵐ[ρ] (fun _ => c) := by
  have hmeas : MeasurableSet {p : Y × H | f (a p.1 p.2) = f p.1} :=
    measurableSet_eq_fun (hf.comp ha) (hf.comp measurable_fst)
  have hall : ∀ᵐ x ∂ρ, ∀ᵐ g ∂η, f (a x g) = f x :=
    (Measure.ae_ae_comm hmeas).mpr (Eventually.of_forall hinv)
  obtain ⟨x,hx⟩ := hall.exists
  refine ⟨f x,hall.mono ?_⟩
  intro y hy
  obtain ⟨g,hg⟩ := htrans x y
  have hshift : ∀ᵐ h ∂η, f (a x (g*h)) = f x :=
    (measurePreserving_mul_left η g).quasiMeasurePreserving.ae hx
  have hxy : ∀ᵐ h ∂η, f (a y h) = f x := by
    simpa only [← hmul,hg] using hshift
  obtain ⟨h,hh₁,hh₂⟩ := (hy.and hxy).exists
  exact hh₁.symm.trans hh₂

 

theorem invariant_probability_unique_transitive
    (a : Y → H → Y) (ha : Measurable (fun p : Y × H => a p.1 p.2))
    (e : H → Y ≃ᵐ Y) (he : ∀ g x, e g x = a x g)
    (hmul : ∀ x g h, a (a x g) h = a x (g*h))
    (htrans : ∀ x y, ∃ g, a x g = y)
    (η : Measure H) [SigmaFinite η] [η.IsMulLeftInvariant] [NeZero η]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ g, Measure.map (fun x => a x g) μ = μ)
    (hν : ∀ g, Measure.map (fun x => a x g) ν = ν) : μ = ν := by
  let ρ := μ+ν
  have hρ : ∀ g, Measure.map (fun x => a x g) ρ = ρ := by
    intro g
    change Measure.map (fun x => a x g) (μ+ν) = μ+ν
    have hg : Measurable (fun x => a x g) :=
      ha.comp (measurable_id.prodMk (measurable_const (a := g)))
    rw [Measure.map_add μ ν hg]
    rw [hμ,hν]
  have : NeZero ρ := ⟨by
    intro h
    have := congrArg (fun m : Measure Y => m Set.univ) h
    simp [ρ] at this⟩
  have Hμ : ∃ c : ℝ≥0∞, μ = c • ρ := by
    have hinv (g : H) : (fun x => μ.rnDeriv ρ (a x g)) =ᵐ[ρ] μ.rnDeriv ρ := by
      have H := (e g).measurableEmbedding.rnDeriv_map μ ρ
      have heq : (e g : Y → Y) = (fun x => a x g) := funext (he g)
      rw [heq,hμ,hρ] at H
      exact H
    obtain ⟨c,hc⟩ := ae_constant_of_transitive_right_action a ha hmul htrans η ρ
      (μ.rnDeriv ρ) (Measure.measurable_rnDeriv _ _) hinv
    refine ⟨c,?_⟩
    rw [← Measure.withDensity_rnDeriv_eq μ ρ (Measure.absolutelyContinuous_of_le (show μ ≤ ρ from Measure.le_add_right le_rfl)),
      withDensity_congr_ae hc,withDensity_const]
  have Hν : ∃ c : ℝ≥0∞, ν = c • ρ := by
    have hinv (g : H) : (fun x => ν.rnDeriv ρ (a x g)) =ᵐ[ρ] ν.rnDeriv ρ := by
      have H := (e g).measurableEmbedding.rnDeriv_map ν ρ
      have heq : (e g : Y → Y) = (fun x => a x g) := funext (he g)
      rw [heq,hν,hρ] at H
      exact H
    obtain ⟨c,hc⟩ := ae_constant_of_transitive_right_action a ha hmul htrans η ρ
      (ν.rnDeriv ρ) (Measure.measurable_rnDeriv _ _) hinv
    refine ⟨c,?_⟩
    rw [← Measure.withDensity_rnDeriv_eq ν ρ (Measure.absolutelyContinuous_of_le (show ν ≤ ρ from Measure.le_add_left le_rfl)),
      withDensity_congr_ae hc,withDensity_const]
  obtain ⟨c,hc⟩ := Hμ
  obtain ⟨b,hb⟩ := Hν
  have hceq : c*(2:ℝ≥0∞) = b*2 := by
    have h₁ := congrArg (fun m : Measure Y => m Set.univ) hc
    have h₂ := congrArg (fun m : Measure Y => m Set.univ) hb
    simp only [measure_univ,Measure.smul_apply,smul_eq_mul,ρ,Measure.add_apply] at h₁ h₂
    have H : (1:ℝ≥0∞)+(1:ℝ≥0∞)=2 := by norm_num
    rw [H] at h₁ h₂
    exact h₁.symm.trans h₂
  have hcb : c=b := (ENNReal.mul_left_inj (show (2:ℝ≥0∞) ≠ 0 by norm_num) (show (2:ℝ≥0∞) ≠ ⊤ by norm_num)).mp hceq
  rw [hc,hb,hcb]

end Transitive
end PrimeDegreePackets
end
end

end OAI
