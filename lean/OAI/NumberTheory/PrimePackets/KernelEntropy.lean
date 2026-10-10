import Mathlib
import OAI.NumberTheory.PrimePackets.AtomMass
import OAI.NumberTheory.PrimePackets.EntropyMixtures

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
namespace PrimeDegreePackets

lemma kernel_cond_le {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y)
    (S : Set Z) (hS : τ S ≠ 0) :
    κ ∘ₘ ProbabilityTheory.cond τ S ≤ ENNReal.ofReal ((τ.real S)⁻¹) • (κ ∘ₘ τ) := by
  have H : ENNReal.ofReal ((τ.real S)⁻¹) = (τ S)⁻¹ := by
    rw [measureReal_def, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal]
    exact ENNReal.inv_ne_top.mpr hS
  rw [H, ProbabilityTheory.cond, Measure.comp_smul]
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  apply _root_.mul_le_mul_right
  rw [Measure.bind_apply hA κ.aemeasurable, Measure.bind_apply hA κ.aemeasurable]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

 

theorem zero_entropy_component_collection_null {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z (X (d+1))) [IsMarkovKernel κ]
    (hball : OrdinaryBallBound (d+1) (κ ∘ₘ τ))
    (hA : ∀ᵐ z ∂τ, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z)
    (S : Set Z)
    (hzero : ∀ᵐ z ∂τ.restrict S, measureEntropy (κ z)
      (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
        (regularDiagonalWeights_sum d) 1)) = 0) : τ S = 0 := by
  by_contra hS
  let σ := ProbabilityTheory.cond τ S
  have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hS
  let ν := κ ∘ₘ σ
  have hA' : ∀ᵐ z ∂σ, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z :=
    cond_absolutelyContinuous.ae_le hA
  have hν : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) ν = ν := by
    intro u
    exact (kernel_mixture_preserving σ κ (continuous_rightAction _).measurable
      (hA'.mono (fun z hz => ⟨(continuous_rightAction _).measurable,hz u⟩))).map_eq
  have hpos := positive_entropy_every_dominated_invariant (κ ∘ₘ τ) ν hball hν
    (kernel_cond_le τ κ S hS)
  have hz : ∀ᵐ z ∂σ, measureEntropy (κ z)
      (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
        (regularDiagonalWeights_sum d) 1)) = 0 := Measure.smul_absolutelyContinuous.ae_le hzero
  have hpres : ∀ᵐ z ∂σ, MeasurePreserving
      (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
        (regularDiagonalWeights_sum d) 1)) (κ z) (κ z) := by
    filter_upwards [hA'] with z hz
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hz _
  have H := measureEntropy_kernel_zero σ κ (continuous_rightAction _).measurable hpres hz
  exact (ne_of_gt hpos) H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurable_kernel_entropyRate {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α] (κ : Kernel Z Y) {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Measurable (fun z => observationEntropyRate (κ z) T P) := by
  unfold observationEntropyRate
  exact Measurable.sInf (Set.to_countable _) (fun N _ =>
    (measurable_kernel_entropy κ _ (orbitName_measurable_fiber hT hP N)).div_const _)

 

lemma observationEntropyRate_kernel_zero {Z Y α : Type*} [MeasurableSpace Z]
    [MeasurableSpace Y] [Fintype α]
    (τ : Measure Z) [IsProbabilityMeasure τ] (κ : Kernel Z Y) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T)
    (hκ : ∀ᵐ z ∂τ, MeasurePreserving T (κ z) (κ z))
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a})
    (hzero : ∀ᵐ z ∂τ, observationEntropyRate (κ z) T P = 0) :
    observationEntropyRate (κ ∘ₘ τ) T P = 0 := by
  apply le_antisymm _ (observationEntropyRate_nonneg _ hT P hP)
  let F : ℕ → Z → ℝ := fun N z => observationEntropy (κ z) (orbitName T P N)/(N:ℝ)
  have hlim : Tendsto (fun N => ∫ z, F N z ∂τ) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence
      (fun _ : Z => Real.log (Fintype.card α))
      (fun N => ((measurable_kernel_entropy κ _ (orbitName_measurable_fiber hT hP N)).div_const _).aestronglyMeasurable)
      (integrable_const _) (fun N => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
          (observationEntropy_nonneg (κ z) _ (orbitName_measurable_fiber hT hP N)) (Nat.cast_nonneg N))]
        exact normalized_orbit_entropy_le (κ z) hT P hP N)
      (f := fun _ : Z => (0:ℝ)) (by
        filter_upwards [hκ,hzero] with z hz hz0
        simpa only [hz0] using tendsto_observationEntropyRate (κ z) hz P hP)
    simpa only [integral_zero] using H
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have H := kernel_entropyRate_le_block τ κ hT hκ P hP hN
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  change observationEntropyRate (κ ∘ₘ τ) T P ≤ ∫ z, observationEntropy (κ z) (orbitName T P N)/(N:ℝ) ∂τ
  rw [integral_div]
  exact (le_div_iff₀ hNr).mpr H

 

theorem positive_entropy_components_ae {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z (X (d+1))) [IsMarkovKernel κ]
    (hball : OrdinaryBallBound (d+1) (κ ∘ₘ τ))
    (hA : ∀ᵐ z ∂τ, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z) :
    ∀ᵐ z ∂τ, 0 < measureEntropy (κ z)
      (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
        (regularDiagonalWeights_sum d) 1)) := by
  let T : X (d+1) → X (d+1) := fun x => rightAction x
    (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)
  have hT : Measurable T := (continuous_rightAction _).measurable
  let C : Set (Set Z) := {B | ∃ k : ℕ, ∃ P : X (d+1) → Fin k,
    (∀ a, MeasurableSet {y | P y = a}) ∧ B = {z | 0 < observationEntropyRate (κ z) T P}}
  have hCm (B : Set Z) (hB : B ∈ C) : MeasurableSet B := by
    obtain ⟨k,P,hP,rfl⟩ := hB
    exact measurableSet_lt measurable_const (measurable_kernel_entropyRate κ hT P hP)
  obtain ⟨D,hDC,hDcount,hDcover⟩ := Measure.exists_ae_subset_biUnion_countable τ hCm
  let U : Set Z := ⋃₀ D
  have hUm : MeasurableSet U := MeasurableSet.sUnion hDcount (fun B hB => hCm B (hDC hB))
  have hUpos (z : Z) (hz : z ∈ U) : 0 < measureEntropy (κ z) T := by
    obtain ⟨B,hBD,hzB⟩ := Set.mem_sUnion.mp hz
    obtain ⟨k,P,hP,rfl⟩ := hDC hBD
    exact (ENNReal.ofReal_pos.mpr hzB).trans_le
      (le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP le_rfl)))
  have hnull : τ Uᶜ = 0 := by
    by_contra hS
    let σ := ProbabilityTheory.cond τ Uᶜ
    have : IsProbabilityMeasure σ := cond_isProbabilityMeasure hS
    let ν := κ ∘ₘ σ
    have hA' : ∀ᵐ z ∂σ, ∀ u : LogCoordinates d,
        Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z :=
      cond_absolutelyContinuous.ae_le hA
    have hν : ∀ u : LogCoordinates d,
        Measure.map (fun x => rightAction x (diagonalFlow u)) ν = ν := by
      intro u
      exact (kernel_mixture_preserving σ κ (continuous_rightAction _).measurable
        (hA'.mono (fun z hz => ⟨(continuous_rightAction _).measurable,hz u⟩))).map_eq
    have hpos := positive_entropy_every_dominated_invariant (κ ∘ₘ τ) ν hball hν
      (kernel_cond_le τ κ Uᶜ hS)
    have hpres : ∀ᵐ z ∂σ, MeasurePreserving T (κ z) (κ z) := by
      filter_upwards [hA'] with z hz
      refine ⟨hT,?_⟩
      dsimp [T]
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hz _
    have hnotU : ∀ᵐ z ∂σ, z ∉ U := by
      exact Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem hUm.compl)
    have hzero : measureEntropy ν T = 0 := by
      apply le_antisymm _ bot_le
      apply iSup_le
      intro k
      apply iSup_le
      intro P
      apply iSup_le
      intro hP
      have hcover := hDcover {z | 0 < observationEntropyRate (κ z) T P} ⟨k,P,hP,rfl⟩
      have hz : ∀ᵐ z ∂σ, observationEntropyRate (κ z) T P = 0 := by
        filter_upwards [cond_absolutelyContinuous.ae_le hcover,hnotU] with z hz hn
        apply le_antisymm _ (observationEntropyRate_nonneg (κ z) hT P hP)
        exact le_of_not_gt (fun hp => hn (hz hp))
      rw [observationEntropyRate_kernel_zero σ κ hT hpres P hP hz,ENNReal.ofReal_zero]
      exact le_rfl
    exact (ne_of_gt hpos) hzero
  have hUae : ∀ᵐ z ∂τ, z ∈ U := by
    simpa only [Set.mem_compl_iff,not_not] using measure_eq_zero_iff_ae_notMem.mp hnull
  exact hUae.mono hUpos

end PrimeDegreePackets

open Set Filter
open scoped Topology
namespace PrimeDegreePackets

 

theorem fixedPoint_mem_closed_convex_orbit {H E : Type*} [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : H → E →ₗᵢ[ℝ] E) (hU : ∀ g h x, U g (U h x) = U (g*h) x)
    (x : E) : ∃ v : E, v ∈ closure (convexHull ℝ (Set.range (fun g => U g x))) ∧
      ∀ g, U g v = v := by
  let O := Set.range (fun g => U g x)
  let C := closure (convexHull ℝ O)
  have hconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hnon : C.Nonempty := ⟨U 1 x,subset_closure (subset_convexHull ℝ O ⟨1,rfl⟩)⟩
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hnon
    isClosed_closure.isComplete hconv (0:E)
  refine ⟨v,hv,?_⟩
  intro g
  have himage : U g '' C ⊆ C := by
    calc
      U g '' C ⊆ closure (U g '' convexHull ℝ O) :=
        image_closure_subset_closure_image (U g).continuous
      _ = closure (convexHull ℝ (U g '' O)) := by
        exact congrArg closure ((U g).toLinearMap.image_convexHull O)
      _ ⊆ C := closure_mono (convexHull_mono ?_)
    rintro _ ⟨_,⟨h,rfl⟩,rfl⟩
    exact ⟨g*h,(hU g h x).symm⟩
  have hg : U g v ∈ C := himage ⟨v,hv,rfl⟩
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin (U g v) hg
  have hn := norm_sub_sq_real (U g v) v
  have hh : inner ℝ v (U g v) = inner ℝ (U g v) v := real_inner_comm _ _
  simp only [zero_sub,inner_neg_left,inner_sub_right,real_inner_self_eq_norm_sq] at hinner
  rw [(U g).norm_map] at hn
  have he : ‖U g v-v‖^2 = 0 := by nlinarith [sq_nonneg ‖U g v-v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))

 

theorem exists_convex_orbit_approximants {H E : Type*} [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : H → E →ₗᵢ[ℝ] E) (hU : ∀ g h x, U g (U h x) = U (g*h) x)
    (x : E) : ∃ v : E, (∀ g, U g v = v) ∧
      ∀ ε : ℝ, 0 < ε → ∃ y ∈ convexHull ℝ (Set.range (fun g => U g x)), ‖y-v‖ < ε := by
  obtain ⟨v,hv,hfix⟩ := fixedPoint_mem_closed_convex_orbit U hU x
  refine ⟨v,hfix,?_⟩
  intro ε hε
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp hv ε hε
  exact ⟨y,hy,by simpa only [dist_eq_norm, norm_sub_rev] using hd⟩

end PrimeDegreePackets

open scoped Classical
namespace PrimeDegreePackets

 
@[instance_reducible]
def actionInvariantSigma (H Y : Type*) [Group H] [MulAction H Y] [MeasurableSpace Y] :
    MeasurableSpace Y := ⨅ g : H, MeasurableSpace.invariants (fun y : Y => g • y)

lemma actionInvariantSigma_le (H Y : Type*) [Group H] [MulAction H Y]
    [mY : MeasurableSpace Y] : actionInvariantSigma H Y ≤ mY :=
  (iInf_le _ (1:H)).trans (MeasurableSpace.invariants_le _)

lemma measurable_actionInvariantSigma {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] {f : Y → ℝ} (hf : Measurable f)
    (hinv : ∀ (g : H) (y : Y), f (g • y) = f y) : Measurable[actionInvariantSigma H Y] f := by
  intro s hs
  rw [actionInvariantSigma,MeasurableSpace.measurableSet_iInf]
  intro g
  refine ⟨hf hs,?_⟩
  ext y
  simp only [Set.mem_preimage,hinv]

 

theorem exists_pointwise_invariant_representative {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [MeasurableSpace Y] (μ : Measure Y)
    (hm : ∀ g : H, Measurable (fun y : Y => g • y))
    (f : Y → ℝ) (hf : Measurable f)
    (hinv : ∀ g : H, (fun y => f (g • y)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[actionInvariantSigma H Y] f₀ ∧ f₀ =ᵐ[μ] f ∧
      ∀ (g : H) (y : Y), f₀ (g • y) = f₀ y := by
  let A : Set Y := {y | ∀ g : H, f (g • y) = f y}
  have hA : MeasurableSet A := by
    simpa only [A,Set.ofPred_forall,Function.comp_apply] using
      MeasurableSet.iInter (fun g => measurableSet_eq_fun (hf.comp (hm g)) hf)
  have hconull : ∀ᵐ y ∂μ, y ∈ A := ae_all_iff.mpr hinv
  have hstable (g : H) (y : Y) : g • y ∈ A ↔ y ∈ A := by
    constructor
    · intro hy h
      have hfgy : f y = f (g • y) := by simpa only [inv_smul_smul] using hy g⁻¹
      have hh := hy (h*g⁻¹)
      simpa only [mul_smul,inv_smul_smul,hfgy] using hh
    · intro hy h
      simpa only [mul_smul,hy g] using hy (h*g)
  let f₀ := A.indicator f
  have hmeas : Measurable f₀ := hf.indicator hA
  have hfixed (g : H) (y : Y) : f₀ (g • y) = f₀ y := by
    by_cases hy : y ∈ A
    · simp only [f₀,Set.indicator_of_mem hy,Set.indicator_of_mem ((hstable g y).mpr hy)]
      exact hy g
    · simp only [f₀,Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (not_imp_not.mpr (hstable g y).mp hy)]
  refine ⟨f₀,measurable_actionInvariantSigma hmeas hfixed,?_,hfixed⟩
  filter_upwards [hconull] with y hy
  exact Set.indicator_of_mem hy f

end PrimeDegreePackets

open scoped Topology ENNReal Classical
namespace PrimeDegreePackets

 
def orbitConvexHull {H Y : Type*} [Group H] [MulAction H Y] (f : Y → ℝ) : Set (Y → ℝ) :=
  convexHull ℝ (Set.range fun g : H => fun y : Y => f (g • y))

lemma orbitConvexHull_measurable {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (hm : ∀ g : H, Measurable (fun y : Y => g • y))
    {f F : Y → ℝ} (hf : Measurable f) (hF : F ∈ orbitConvexHull (H := H) f) :
    Measurable F := by
  have hc : Convex ℝ {F : Y → ℝ | Measurable F} := by
    intro F hF G hG a b _ _ _
    exact (hF.const_smul a).add (hG.const_smul b)
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩
  exact hf.comp (hm g)

lemma orbitConvexHull_interval {H Y : Type*} [Group H] [MulAction H Y]
    {f F : Y → ℝ} {a b : ℝ} (hf : ∀ y, f y ∈ Set.Icc a b)
    (hF : F ∈ orbitConvexHull (H := H) f) : ∀ y, F y ∈ Set.Icc a b := by
  have hc : Convex ℝ {F : Y → ℝ | ∀ y, F y ∈ Set.Icc a b} := by
    intro F hF G hG c d hc hd hcd y
    exact (convex_Icc a b) (hF y) (hG y) hc hd hcd
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩ y
  exact hf (g • y)

 

lemma orbitConvexHull_integral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    Integrable F ν ∧ (∫ y, F y ∂ν) = ∫ y, f y ∂ν := by
  let : MeasurableConstSMul H Y := ⟨fun g => (hp g).measurable⟩
  have hc : Convex ℝ {F : Y → ℝ | Integrable F ν ∧ (∫ y, F y ∂ν) = ∫ y, f y ∂ν} := by
    intro F hF G hG a b _ _ hab
    refine ⟨(hF.1.smul a).add (hG.1.smul b),?_⟩
    change (∫ y, a * F y+b * G y ∂ν) = _
    rw [integral_add (hF.1.const_mul a) (hG.1.const_mul b),
      integral_const_mul,integral_const_mul,hF.2,hG.2]
    rw [← add_mul,hab,one_mul]
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩
  exact ⟨(hp g).integrable_comp_of_integrable hf,
    (hp g).integral_comp (MeasurableEquiv.smul g).measurableEmbedding f⟩

lemma orbitConvexHull_setIntegral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S = S)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    (∫ y in S, F y ∂ν) = ∫ y in S, f y ∂ν := by
  apply (orbitConvexHull_integral (ν.restrict S) (fun g => ?_) hf.integrableOn hF).2
  simpa only [hSfix g] using (hp g).restrict_preimage hS

end PrimeDegreePackets


namespace PrimeDegreePackets

 
lemma lp_convex_orbit_representative {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (μ : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ)
    {f : Y → ℝ} (hf : MemLp f 2 μ) {z : Lp ℝ 2 μ}
    (hz : z ∈ convexHull ℝ (Set.range fun g : H =>
      Lp.compMeasurePreservingₗᵢ ℝ (fun y : Y => g⁻¹ • y) (hp g⁻¹) (hf.toLp f))) :
    ∃ F ∈ orbitConvexHull (H := H) f, z =ᵐ[μ] F := by
  let C : Set (Lp ℝ 2 μ) := {z | ∃ F ∈ orbitConvexHull (H := H) f, z =ᵐ[μ] F}
  have hconv : Convex ℝ C := by
    intro z hz w hw a b ha hb hab
    obtain ⟨F,hF,hzF⟩ := hz
    obtain ⟨G,hG,hwG⟩ := hw
    refine ⟨a • F+b • G, (convex_convexHull ℝ _) hF hG ha hb hab,?_⟩
    filter_upwards [Lp.coeFn_add (a • z) (b • w),Lp.coeFn_smul a z,
      Lp.coeFn_smul b w,hzF,hwG] with y hy ha' hb' hz' hw'
    simp only [hy,ha',hb',Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz',hw']
  apply convexHull_min ?_ hconv hz
  rintro _ ⟨g,rfl⟩
  refine ⟨fun y => f (g⁻¹ • y),subset_convexHull ℝ _ ⟨g⁻¹,rfl⟩,?_⟩
  exact (Lp.coeFn_compMeasurePreserving (hf.toLp f) (hp g⁻¹)).trans
    ((hp g⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)

 

theorem exists_invariant_orbit_average_limit {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [MeasurableSpace Y] (μ : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ)
    {f : Y → ℝ} (hf : MemLp f 2 μ) :
    ∃ v : Y → ℝ, Measurable[actionInvariantSigma H Y] v ∧
      (∀ (g : H) (y : Y), v (g • y) = v y) ∧
      ∃ F : ℕ → Y → ℝ, (∀ k, F k ∈ orbitConvexHull (H := H) f) ∧
        ∀ᵐ y ∂μ, Tendsto (fun k => F k y) atTop (𝓝 (v y)) := by
  let U : H → (Lp ℝ 2 μ) →ₗᵢ[ℝ] (Lp ℝ 2 μ) := fun g =>
    Lp.compMeasurePreservingₗᵢ ℝ (fun y : Y => g⁻¹ • y) (hp g⁻¹)
  have hU (g h : H) (x : Lp ℝ 2 μ) : U g (U h x) = U (g*h) x := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ x) =
      Lp.compMeasurePreserving (fun y : Y => (g*h)⁻¹ • y) (hp (g*h)⁻¹) x
    rw [← Lp.compMeasurePreserving_comp_apply]
    simp only [Function.comp_def,_root_.mul_inv_rev,mul_smul]
  obtain ⟨v,hv,hfix⟩ := fixedPoint_mem_closed_convex_orbit U hU (hf.toLp f)
  have hvfix (g : H) : (fun y => v (g • y)) =ᵐ[μ] v := by
    have H := Lp.coeFn_compMeasurePreserving v (hp g)
    have he : Lp.compMeasurePreserving (fun y : Y => g • y) (hp g) v = v := by
      have he := hfix g⁻¹
      change Lp.compMeasurePreserving (fun y : Y => (g⁻¹)⁻¹ • y) _ v = v at he
      simpa only [inv_inv] using he
    simpa only [he,Function.comp_def] using H.symm
  obtain ⟨v₀,hv₀,hveq,hvfix₀⟩ := exists_pointwise_invariant_representative μ
    (fun g => (hp g).measurable) v (Lp.stronglyMeasurable v).measurable hvfix
  obtain ⟨z,hz,hzlim⟩ := mem_closure_iff_seq_limit.mp hv
  choose F hF hzF using fun k => lp_convex_orbit_representative μ hp hf (hz k)
  obtain ⟨ns,-,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hzlim).exists_seq_tendsto_ae
  refine ⟨v₀,hv₀,hvfix₀,F ∘ ns,fun k => hF (ns k),?_⟩
  filter_upwards [hns,hveq,ae_all_iff.mpr hzF] with y hy hvy hzy
  simpa only [Function.comp_apply,hzy,hvy] using hy

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma orbitConvexHull_aeSetIntegral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S =ᵐ[ν] S)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    (∫ y in S, F y ∂ν) = ∫ y in S, f y ∂ν := by
  apply (orbitConvexHull_integral (ν.restrict S) (fun g => ?_) hf.integrableOn hF).2
  have hg := (hp g).restrict_preimage hS
  simpa only [Measure.restrict_congr_set (hSfix g)] using hg

 

lemma invariant_set_independent_of_orbit_indicator_limit {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {B : Set Y} (hB : MeasurableSet B) {F : ℕ → Y → ℝ}
    (hF : ∀ k, F k ∈ orbitConvexHull (H := H) (B.indicator (fun _ => (1:ℝ))))
    {c : ℝ} (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => F k y) atTop (𝓝 c))
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S =ᵐ[ν] S) :
    ν.real (B ∩ S) = ν.real S * ν.real B := by
  have hbmeas : Measurable (B.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hB
  have hbint : Integrable (B.indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator hB
  have hfm (k : ℕ) : Measurable (F k) :=
    orbitConvexHull_measurable (fun g => (hp g).measurable) hbmeas (hF k)
  have hbnd (k : ℕ) (y : Y) : ‖F k y‖ ≤ 1 := by
    have hb : ∀ y : Y, B.indicator (fun _ => (1:ℝ)) y ∈ Icc (0:ℝ) 1 := by
      intro y
      by_cases hy : y ∈ B <;> simp [hy]
    have hx := orbitConvexHull_interval hb (hF k) y
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hc : ν.real B = c := by
    have H := tendsto_integral_of_dominated_convergence (fun _ : Y => (1:ℝ))
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ (hbnd k)) hlim
    have hi (k : ℕ) : (∫ y, F k y ∂ν) = ν.real B := by
      rw [(orbitConvexHull_integral ν hp hbint (hF k)).2,integral_indicator hB]
      simp [integral_const,Measure.real]
    simp only [hi,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at H
    exact tendsto_nhds_unique tendsto_const_nhds H
  have H := tendsto_integral_of_dominated_convergence (μ := ν.restrict S)
    (fun _ : Y => (1:ℝ))
    (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
    (fun k => ae_of_all _ (hbnd k)) (ae_restrict_of_ae hlim)
  have hi (k : ℕ) : (∫ y in S, F k y ∂ν) = ν.real (B ∩ S) := by
    rw [orbitConvexHull_aeSetIntegral ν hp hS hSfix hbint (hF k),integral_indicator hB]
    simp [integral_const,Measure.real,Measure.restrict_apply hB]
  simp only [hi,integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at H
  rw [← hc] at H
  exact tendsto_nhds_unique tendsto_const_nhds H

 

theorem ergodicSMul_of_orbit_indicator_limits {H Y : Type*} [Group H] [MulAction H Y]
    [mY : MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    (C : Set (Set Y)) (hgen : mY = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (havg : ∀ B ∈ C, ∃ c : ℝ, ∃ F : ℕ → Y → ℝ,
      (∀ k, F k ∈ orbitConvexHull (H := H) (B.indicator (fun _ => (1:ℝ)))) ∧
        ∀ᵐ y ∂ν, Tendsto (fun k => F k y) atTop (𝓝 c)) :
    ErgodicSMul H Y ν := by
  refine { measure_preimage_smul := fun g _ hs => (hp g).measure_preimage hs.nullMeasurableSet
           aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  intro S hS hSfix
  have hmeas (B : Set Y) (hB : B ∈ C) : MeasurableSet B := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hB
  have hind (B : Set Y) (hB : B ∈ C) : ν.real (B ∩ S) = ν.real S * ν.real B := by
    obtain ⟨c,F,hF,hlim⟩ := havg B hB
    exact invariant_set_independent_of_orbit_indicator_limit ν hp (hmeas B hB)
      hF hlim hS hSfix
  have he : ν.restrict S = (ν S) • ν := by
    apply ext_of_generate_finite C hgen hpi
    · intro B hB
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).mp
      · simpa only [Measure.real,Measure.restrict_apply (hmeas B hB),
          Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul] using hind B hB
      · simp only [Measure.smul_apply,smul_eq_mul]
        exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
    · simp
  have hreal := congrArg (fun η : Measure Y => η.real S) he
  simp only [Measure.real,Measure.restrict_apply hS,inter_self,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul] at hreal
  have hz : (ν S).toReal * ((ν S).toReal - 1) = 0 := by nlinarith [hreal]
  rw [eventuallyEmptyOrUniv_iff]
  rcases mul_eq_zero.mp hz with hz | hz
  · right
    apply measure_eq_zero_iff_ae_notMem.mp
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)
  · left
    have hmass : ν S = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
      simpa only [ENNReal.toReal_one] using sub_eq_zero.mp hz
    have hcompl : ν Sᶜ = 0 := by rw [measure_compl hS (measure_ne_top _ _),hmass,measure_univ,tsub_self]
    exact (measure_eq_zero_iff_ae_notMem.mp hcompl).mono fun y hy => not_not.mp hy

end PrimeDegreePackets
end
end

end OAI
