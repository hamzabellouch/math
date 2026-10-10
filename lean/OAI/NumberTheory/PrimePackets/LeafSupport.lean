import Mathlib
import OAI.NumberTheory.PrimePackets.RootLeaves

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
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets

lemma real_mem_measureSupport_iff_rat (ν : Measure ℝ) (t : ℝ) :
    t ∈ ν.support ↔ ∀ a b : ℚ, t ∈ Ioo (a : ℝ) b → 0 < ν (Ioo (a : ℝ) b) := by
  constructor
  · intro ht a b hab
    exact (ν.mem_support_iff_forall t).mp ht _ (isOpen_Ioo.mem_nhds hab)
  · intro ht
    apply (ν.mem_support_iff_forall t).mpr
    intro U hU
    obtain ⟨l,u,htu,hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
    obtain ⟨a,hla,hat⟩ := exists_rat_btwn htu.1
    obtain ⟨b,htb,hbu⟩ := exists_rat_btwn htu.2
    exact (ht a b ⟨hat,htb⟩).trans_le (measure_mono (fun x hx => hlu ⟨hla.trans hx.1,hx.2.trans hbu⟩))

 

lemma measurableSet_kernel_support {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) : MeasurableSet {z : α × ℝ | z.2 ∈ (κ z.1).support} := by
  simp_rw [real_mem_measureSupport_iff_rat,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  exact (measurable_snd measurableSet_Ioo).imp
    (measurableSet_lt measurable_const ((κ.measurable_coe measurableSet_Ioo).comp measurable_fst))

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_mem_leafMeasure_support (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, z.2 ∈ (A.leafMeasure R μ z.1).support := by
  let κ := A.leafKernel R hAR μ hfree
  have hK : ∀ᵐ z ∂A.coordinateMeasure μ, z.2 ∈ (κ z.1).support := by
    have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
        t ∈ (κ s).support := by
      filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,A.ae_leafKernel_eq R hAR μ hfree] with s hs he
      have hle : A.conditionalKernel μ s ≤ κ s := by
        rw [he,←hs.2.2.1]
        exact Measure.restrict_le_self
      filter_upwards [(A.conditionalKernel μ s).support_mem_ae] with t ht
      exact (Measure.support_mono hle) ht
    have H' := Measure.ae_compProd_of_ae_ae (measurableSet_kernel_support κ) H
    simpa only [conditionalKernel,Measure.disintegrate] using H'
  have he : ∀ᵐ z ∂A.coordinateMeasure μ, κ z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafKernel_eq R hAR μ hfree)
  filter_upwards [hK,he] with z hz hez
  rwa [←hez]

 

theorem ae_leafMeasure_ball_pos (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ r : ℝ, 0 < r →
      0 < A.leafMeasure R μ z.1 (Metric.ball z.2 r) := by
  filter_upwards [A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz
  intro r hr
  exact ((A.leafMeasure R μ z.1).mem_support_iff_forall z.2).mp hz _ (Metric.ball_mem_nhds _ hr)

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets

 

lemma isSFiniteKernel_of_pointwise_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (hκ : ∀ a, κ a univ < ∞) : IsSFiniteKernel κ := by
  let U : ℕ → Set α := fun m => {a | κ a univ < m}
  let V := disjointed U
  have hU (m : ℕ) : MeasurableSet (U m) :=
    measurableSet_lt (κ.measurable_coe MeasurableSet.univ) measurable_const
  have hV (m : ℕ) : MeasurableSet (V m) := MeasurableSet.disjointed hU m
  let κs : ℕ → Kernel α β := fun m => Kernel.piecewise (hV m) κ 0
  refine ⟨κs,?_,?_⟩
  · intro m
    refine ⟨(m : ℝ≥0∞),ENNReal.natCast_lt_top m,?_⟩
    intro a
    change (if a ∈ V m then κ a else 0) univ ≤ (m : ℝ≥0∞)
    split_ifs with ha
    · exact (disjointed_subset U m ha).le
    · change 0 ≤ (m : ℝ≥0∞)
      exact bot_le
  · ext a T hT
    obtain ⟨m,hm⟩ := ENNReal.exists_nat_gt (hκ a).ne
    have ha : a ∈ ⋃ k, V k := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr ⟨m,hm⟩
    obtain ⟨k,hk⟩ := mem_iUnion.mp ha
    rw [Kernel.sum_apply' _ _ hT,tsum_eq_single k]
    · change κ a T = (if a ∈ V k then κ a else 0) T
      rw [ite_eq_left hk]
    · intro l hl
      have hl' : a ∉ V l := fun hal => (disjoint_disjointed U hl).le_bot ⟨hal,hk⟩
      change (if a ∈ V l then κ a else 0) T = 0
      rw [ite_eq_right hl']
      rfl

 

lemma isSFiniteKernel_of_finite_exhaustion {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (W : ℕ → Set β)
    (hW : ∀ m, MeasurableSet (W m)) (hcov : ⋃ m, W m = univ)
    (hfin : ∀ a m, κ a (W m) < ∞) : IsSFiniteKernel κ := by
  let V := disjointed W
  have hV (m : ℕ) : MeasurableSet (V m) := MeasurableSet.disjointed hW m
  let κs : ℕ → Kernel α β := fun m => κ.restrict (hV m)
  have (m : ℕ) : IsSFiniteKernel (κs m) := by
    apply isSFiniteKernel_of_pointwise_finite
    intro a
    change (κ a).restrict (V m) univ < ∞
    rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact (measure_mono (disjointed_subset W m)).trans_lt (hfin a m)
  have he : κ = Kernel.sum κs := by
    ext a T hT
    exact congrArg (fun ν : Measure β => ν T) (measure_eq_sum_disjointed (κ a) W hW hcov)
  rw [he]
  infer_instance

 
def finiteRealWindows {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ) : Set α :=
  {a | ∀ m : ℕ, κ a (Icc (-(m : ℝ)) m) < ∞}

lemma measurableSet_finiteRealWindows {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) : MeasurableSet (finiteRealWindows κ) := by
  change MeasurableSet {a | ∀ m : ℕ, κ a (Icc (-(m : ℝ)) m) < ∞}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun m => measurableSet_lt
    (κ.measurable_coe measurableSet_Icc) measurable_const

lemma locallyFinite_of_finite_real_windows (ν : Measure ℝ)
    (hν : ∀ m : ℕ, ν (Icc (-(m : ℝ)) m) < ∞) : IsLocallyFiniteMeasure ν := by
  constructor
  intro t
  obtain ⟨m,hm⟩ := exists_nat_gt |t|
  refine ⟨Ioo (-(m : ℝ)) m,isOpen_Ioo.mem_nhds ⟨?_,?_⟩,?_⟩
  · have := neg_abs_le t
    linarith
  · exact (le_abs_self t).trans_lt hm
  · exact (measure_mono Set.Ioo_subset_Icc_self).trans_lt (hν m)

 
def locallyFiniteRealVersion {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ) : Kernel α ℝ :=
  Kernel.piecewise (measurableSet_finiteRealWindows κ) κ 0

lemma locallyFiniteRealVersion_eq {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    (a : α) [IsLocallyFiniteMeasure (κ a)] : locallyFiniteRealVersion κ a = κ a := by
  apply ite_eq_left
  intro m
  exact isCompact_Icc.measure_lt_top

instance locallyFiniteRealVersion_locallyFinite {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) (a : α) : IsLocallyFiniteMeasure (locallyFiniteRealVersion κ a) := by
  change IsLocallyFiniteMeasure (if a ∈ finiteRealWindows κ then κ a else 0)
  split_ifs with ha
  · exact locallyFinite_of_finite_real_windows (κ a) ha
  · infer_instance

instance locallyFiniteRealVersion_sFinite {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) : IsSFiniteKernel (locallyFiniteRealVersion κ) := by
  apply isSFiniteKernel_of_finite_exhaustion _ (rootLeafWindow 0)
    (fun m => (rootLeafWindow_open 0 m).measurableSet) (rootLeafWindow_cover 0)
  intro a m
  exact (measure_mono Set.Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 
def regularLeafKernel (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (RootSlice i j k) ℝ := locallyFiniteRealVersion (A.leafKernel R hAR μ hfree)

instance regularLeafKernel_locallyFinite (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (s : RootSlice i j k) : IsLocallyFiniteMeasure (A.regularLeafKernel R hAR μ hfree s) :=
  locallyFiniteRealVersion_locallyFinite _ _

instance regularLeafKernel_sFinite (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    IsSFiniteKernel (A.regularLeafKernel R hAR μ hfree) := locallyFiniteRealVersion_sFinite _

lemma ae_regularLeafKernel_eq (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.regularLeafKernel R hAR μ hfree s = A.leafMeasure R μ s := by
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,A.ae_leafKernel_eq R hAR μ hfree] with s hs he
  have : IsLocallyFiniteMeasure (A.leafKernel R hAR μ hfree s) := he.symm ▸ hs.1
  exact (locallyFiniteRealVersion_eq _ s).trans he

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets

 
def centerRealMeasure (ν : Measure ℝ) (t : ℝ) : Measure ℝ :=
  ν.map (Homeomorph.subRight t)

lemma centerRealMeasure_ball (ν : Measure ℝ) (t r : ℝ) :
    centerRealMeasure ν t (Metric.ball 0 r) = ν (Metric.ball t r) := by
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable Metric.isOpen_ball.measurableSet]
  congr 1
  ext u
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_subRight,Real.dist_eq]
  rw [sub_zero]

instance centerRealMeasure_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (t : ℝ) :
    IsLocallyFiniteMeasure (centerRealMeasure ν t) := by
  apply locallyFinite_of_finite_real_windows
  intro m
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable measurableSet_Icc]
  exact ((Homeomorph.subRight t).isCompact_preimage.mpr isCompact_Icc).measure_lt_top

 

def basedRealMeasure (ν : Measure ℝ) (t : ℝ) : Measure ℝ :=
  anchorNormalize (centerRealMeasure ν t) (Metric.ball 0 1)

lemma basedRealMeasure_ball_one (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (t : ℝ)
    (ht : 0 < ν (Metric.ball t 1)) : basedRealMeasure ν t (Metric.ball 0 1) = 1 := by
  change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t (Metric.ball 0 1) = 1
  rw [centerRealMeasure_ball]
  exact ENNReal.inv_mul_cancel ht.ne' measure_ball_lt_top.ne

lemma basedRealMeasure_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (t : ℝ)
    (ht : 0 < ν (Metric.ball t 1)) : IsLocallyFiniteMeasure (basedRealMeasure ν t) := by
  apply locallyFinite_of_finite_real_windows
  intro m
  change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ *
    centerRealMeasure ν t (Icc (-(m : ℝ)) m) < ∞
  rw [centerRealMeasure_ball]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ht) isCompact_Icc.measure_lt_top

 

def centerRealKernel {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    [IsSFiniteKernel κ] : Kernel (α × ℝ) ℝ where
  toFun z := centerRealMeasure (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ κ)
      ((measurable_snd.sub measurable_fst.snd) hS)
    convert H using 1
    funext z
    exact Measure.map_apply (Homeomorph.subRight z.2).measurable hS

 

def basedRealKernel {α : Type*} [MeasurableSpace α] (κ : Kernel α ℝ)
    [IsSFiniteKernel κ] : Kernel (α × ℝ) ℝ where
  toFun z := basedRealMeasure (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    change Measurable (fun z => (centerRealKernel κ z (Metric.ball 0 1))⁻¹ * centerRealKernel κ z S)
    exact (centerRealKernel κ |>.measurable_coe Metric.isOpen_ball.measurableSet).inv.mul
      (centerRealKernel κ |>.measurable_coe hS)

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 
def basedLeaf (A : RootBox hij k) (R : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (z : RootSlice i j k × ℝ) : Measure ℝ := basedRealMeasure (A.leafMeasure R μ z.1) z.2

lemma aemeasurable_basedLeaf (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (A.basedLeaf R μ) (A.coordinateMeasure μ) := by
  have he : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.regularLeafKernel R hAR μ hfree z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  exact (basedRealKernel (A.regularLeafKernel R hAR μ hfree)).measurable.aemeasurable.congr
    (he.mono fun z hz => congrArg (fun ν => basedRealMeasure ν z.2) hz)

 

theorem ae_basedLeaf_spec (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      IsLocallyFiniteMeasure (A.basedLeaf R μ z) ∧
        A.basedLeaf R μ z (Metric.ball 0 1) = 1 := by
  have hlf : ∀ᵐ z ∂A.coordinateMeasure μ, IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [hlf,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hz
  exact ⟨basedRealMeasure_locallyFinite _ _ (hp 1 zero_lt_one),
    basedRealMeasure_ball_one _ _ (hp 1 zero_lt_one)⟩

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets

lemma anchorNormalize_smul {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (J : Set α) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) :
    anchorNormalize (c • ν) J = anchorNormalize ν J := by
  unfold anchorNormalize
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.mul_inv (Or.inl hc0) (Or.inl hcT),smul_smul]
  congr 1
  rw [mul_right_comm,ENNReal.inv_mul_cancel hc0 hcT,one_mul]

lemma anchorNormalize_restrict_comm {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {J W : Set α} (hJ : MeasurableSet J) (hJW : J ⊆ W) :
    anchorNormalize (ν.restrict W) J = (anchorNormalize ν J).restrict W := by
  unfold anchorNormalize
  rw [Measure.restrict_apply hJ,inter_eq_left.mpr hJW,Measure.restrict_smul]

lemma anchorNormalize_anchor_of_pos_finite {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (J : Set α) (hJ0 : ν J ≠ 0) (hJT : ν J ≠ ∞) :
    anchorNormalize ν J J = 1 := ENNReal.inv_mul_cancel hJ0 hJT

lemma anchorNormalize_twice {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (J W : Set α) (hW0 : ν W ≠ 0) (hWT : ν W ≠ ∞) :
    anchorNormalize (anchorNormalize ν W) J = anchorNormalize ν J :=
  anchorNormalize_smul ν J _ (ENNReal.inv_ne_zero.mpr hWT) (ENNReal.inv_ne_top.mpr hW0)

lemma centerRealMeasure_smul (ν : Measure ℝ) (c : ℝ≥0∞) (t : ℝ) :
    centerRealMeasure (c • ν) t = c • centerRealMeasure ν t :=
  Measure.map_smul c (Homeomorph.subRight t).measurable.aemeasurable

lemma basedRealMeasure_smul (ν : Measure ℝ) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) (t : ℝ) :
    basedRealMeasure (c • ν) t = basedRealMeasure ν t := by
  unfold basedRealMeasure
  rw [centerRealMeasure_smul,anchorNormalize_smul _ _ _ hc0 hcT]

lemma centerRealMeasure_center (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure (centerRealMeasure ν t) u = centerRealMeasure ν (t+u) := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight u).measurable (Homeomorph.subRight t).measurable]
  congr 1
  funext x
  change (x-t)-u=x-(t+u)
  ring

lemma basedRealMeasure_center (ν : Measure ℝ) (t u : ℝ) :
    basedRealMeasure (centerRealMeasure ν t) u = basedRealMeasure ν (t+u) := by
  unfold basedRealMeasure
  rw [centerRealMeasure_center]

 

lemma basedRealMeasure_rebase (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t u : ℝ) (ht : 0 < ν (Metric.ball t 1)) :
    basedRealMeasure (basedRealMeasure ν t) u = basedRealMeasure ν (t+u) := by
  change basedRealMeasure ((centerRealMeasure ν t (Metric.ball 0 1))⁻¹ • centerRealMeasure ν t) u = _
  rw [basedRealMeasure_smul]
  · exact basedRealMeasure_center ν t u
  · rw [centerRealMeasure_ball]
    exact ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne
  · rw [centerRealMeasure_ball]
    exact ENNReal.inv_ne_top.mpr ht.ne'

lemma centerRealMeasure_scaling (ν : Measure ℝ) (c t : ℝ) (hc : c ≠ 0) :
    centerRealMeasure (ν.map (Homeomorph.mulLeft₀ c hc)) (c*t) =
      (centerRealMeasure ν t).map (Homeomorph.mulLeft₀ c hc) := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight (c*t)).measurable (Homeomorph.mulLeft₀ c hc).measurable,
    Measure.map_map (Homeomorph.mulLeft₀ c hc).measurable (Homeomorph.subRight t).measurable]
  congr 1
  funext x
  change c*x-c*t=c*(x-t)
  ring

 

lemma basedRealMeasure_scaling (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (c t : ℝ) (hc : c ≠ 0) (ht : 0 < ν (Metric.ball t 1)) :
    basedRealMeasure (ν.map (Homeomorph.mulLeft₀ c hc)) (c*t) =
      anchorNormalize ((basedRealMeasure ν t).map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) := by
  unfold basedRealMeasure
  rw [centerRealMeasure_scaling]
  unfold anchorNormalize
  rw [Measure.map_smul _ (Homeomorph.mulLeft₀ c hc).measurable.aemeasurable]
  exact (anchorNormalize_smul _ _ _
    (ENNReal.inv_ne_zero.mpr (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne))
    (ENNReal.inv_ne_top.mpr (by rw [centerRealMeasure_ball]; exact ht.ne'))).symm

end PrimeDegreePackets
end
end

end OAI
