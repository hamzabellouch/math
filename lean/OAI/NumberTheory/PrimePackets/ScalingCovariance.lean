import Mathlib
import OAI.NumberTheory.PrimePackets.AmbientLeaves

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
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
namespace PrimeDegreePackets

lemma normalized_realScaling_total_inv (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0)
    (hb : anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1)
      (Metric.ball 0 1) = 1) :
    (anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) univ)⁻¹ =
      ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1) * (ν univ)⁻¹ := by
  let B := ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1)
  have he : B⁻¹ * B = 1 := by
    simpa only [anchorNormalize,Measure.smul_apply,smul_eq_mul,
      Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable
        Metric.isOpen_ball.measurableSet] using hb
  have hB0 : B ≠ 0 := by intro h; simp [h] at he
  have hBT : B ≠ ∞ := by intro h; simp [h] at he
  change ((ν.map (Homeomorph.mulLeft₀ c hc) (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc) univ)⁻¹ = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable
    Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable MeasurableSet.univ,
    preimage_univ]
  rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hBT))
    (Or.inl (ENNReal.inv_ne_top.mpr hB0)),inv_inv]

 

theorem ae_total_inv_eq_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (ν : α → Measure ℝ) (hν : AEMeasurable ν μ)
    (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (c : ℝ) (hc : 0 < c)
    (hcov : ∀ᵐ x ∂μ, ν (T x) =
      anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, (ν x univ)⁻¹ = (ν (T x) univ)⁻¹ := by
  have hm : AEMeasurable (fun x => (ν x univ)⁻¹) μ :=
    ((Measure.measurable_coe MeasurableSet.univ).comp_aemeasurable hν).inv
  have hle : ∀ᵐ x ∂μ, (ν x univ)⁻¹ ≤ 1 := by
    filter_upwards [hball] with x hx
    apply ENNReal.inv_le_one.mpr
    rw [←hx]
    exact measure_mono (subset_univ _)
  have hballT : ∀ᵐ x ∂μ, ν (T x) (Metric.ball 0 1) = 1 := by
    apply ae_of_ae_map (μ := μ) (p := fun y => ν y (Metric.ball 0 1) = 1)
      hT.measurable.aemeasurable
    rwa [hT.map_eq]
  have he : ∀ᵐ x ∂μ, (ν (T x) univ)⁻¹ =
      ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) * (ν x univ)⁻¹ := by
    filter_upwards [hcov,hballT] with x hx hb
    rw [hx] at hb ⊢
    exact normalized_realScaling_total_inv _ _ _ hb
  rcases le_total 1 c with h | h
  · apply ae_eq_of_measurePreserving_ennreal_ge μ hT hm hle
    filter_upwards [hball,he] with x hx he
    rw [he]
    have hb : ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) ≤ 1 := by
      rw [←hx]
      exact measure_mono (realScaling_preimage_unitBall_subset c h)
    simpa using mul_le_mul' hb (le_refl ((ν x univ)⁻¹))
  · apply ae_eq_of_measurePreserving_ennreal_le μ hT hm hle
    filter_upwards [hball,he] with x hx he
    rw [he]
    have hb : 1 ≤ ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) := by
      rw [←hx]
      exact measure_mono (realScaling_unitBall_subset_preimage c hc h)
    simpa using mul_le_mul' hb (le_refl ((ν x univ)⁻¹))

 

theorem ae_dirac_of_finite_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : α → Measure ℝ)
    (hν : AEMeasurable ν μ) (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (hscale : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α,
      MeasurePreserving T μ μ ∧ ∀ᵐ x ∂μ, ν (T x) =
        anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x univ ≠ ∞ → ν x = Measure.dirac 0 := by
  have H (c : ℝ) (hc : 0 < c) :
      ∀ᵐ x ∂μ, ν x univ ≠ ∞ → ν x (Metric.ball 0 (1/c)) = 1 := by
    obtain ⟨T,hT,hcov⟩ := hscale c hc
    have he := ae_total_inv_eq_of_scaling_covariance μ hT ν hν hball c hc hcov
    have hballT : ∀ᵐ x ∂μ, ν (T x) (Metric.ball 0 1) = 1 := by
      apply ae_of_ae_map (μ := μ) (p := fun y => ν y (Metric.ball 0 1) = 1)
        hT.measurable.aemeasurable
      rwa [hT.map_eq]
    filter_upwards [hball,hcov,he,hballT] with x hx hc' he' hb hfin
    have h0 : ν x univ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (by
      rw [←hx]; exact measure_mono (subset_univ _)))
    rw [hc'] at hb he'
    rw [normalized_realScaling_total_inv _ _ _ hb] at he'
    have H := (ENNReal.mul_eq_right (ENNReal.inv_ne_zero.mpr hfin)
      (ENNReal.inv_ne_top.mpr h0)).mp he'.symm
    rwa [realScaling_preimage_ball c 1 hc] at H
  have HS := ae_all_iff.mpr (fun m : ℕ => H (m+1) (by positivity))
  have HL := ae_all_iff.mpr (fun m : ℕ => H ((m+1:ℝ)⁻¹) (by positivity))
  filter_upwards [HS,HL] with x hs hl hfin
  apply realMeasure_eq_dirac_of_ball_masses (ν x)
  · intro m
    simpa only [one_div] using hs m hfin
  · intro m
    simpa only [one_div,inv_inv] using hl m hfin

end PrimeDegreePackets


namespace PrimeDegreePackets

theorem ae_intrinsicRootLeaf_finite_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x univ ≠ ∞ →
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply ae_dirac_of_finite_scaling_covariance μ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
  intro c hc
  let ell := coordinateContractionWeights d j
  have hell : ∑ k, ell k = 0 := coordinateContractionWeights_sum d j
  let t := Real.log c / (d+1:ℝ)
  let a := diagonalOneParameter ell hell t
  have hinv : μ.map (fun x => rightAction x a) = μ := by
    rw [show a = diagonalFlow (fun k : Fin d => ell k.castSucc*t) from
      diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  refine ⟨(fun x => rightAction x a),⟨(continuous_rightAction a).measurable,hinv⟩,?_⟩
  have hrate : ell j-ell i = (d+1:ℝ) := by
    simp [ell,coordinateContractionWeights,hij]
  have he : Real.exp ((ell j-ell i)*t) = c := by
    rw [hrate]
    dsimp [t]
    rw [mul_comm,div_mul_cancel₀ _ (by positivity),Real.exp_log hc]
  have hs : rootTimeScaling ell i j t = Homeomorph.mulLeft₀ c hc.ne' := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,he]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell t μ hfree hinv
  simpa only [hs] using H

 

theorem ae_intrinsicRootLeaf_trivial_or_infinite_atomless (d : ℕ)
    {i j : Fin (d+1)} (hij : i ≠ j) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0 ∨
      (intrinsicRootLeaf hij μ x univ = ∞ ∧ NullSingletonClass (intrinsicRootLeaf hij μ x)) := by
  filter_upwards [ae_intrinsicRootLeaf_finite_dirac d hij μ hA,
    ae_intrinsicRootLeaf_nullSingleton_or_dirac d hij μ hA] with x hf hn
  by_cases h : intrinsicRootLeaf hij μ x = Measure.dirac 0
  · exact Or.inl h
  · exact Or.inr ⟨not_ne_iff.mp (mt hf h),hn.resolve_right h⟩

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_atom_diagonal (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (u : LogCoordinates d) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} =
      intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u)) {0} := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let ell : Fin (d+1) → ℝ := Fin.snoc u (-∑ k, u k)
  have hell : ∑ k, ell k = 0 := by simp [ell,Fin.sum_univ_castSucc]
  have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext k
    simp [ell]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell 1 μ hfree (by rw [ha]; exact hA u)
  have hs : rootTimeScaling ell i j 1 =
      Homeomorph.mulLeft₀ (Real.exp (ell j-ell i)) (Real.exp_ne_zero _) := by
    apply Homeomorph.ext
    intro t
    simp [rootTimeScaling]
  rw [ha,hs] at H
  exact ae_atom_eq_of_scaling_covariance μ
    ⟨(continuous_rightAction _).measurable,hA u⟩ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
    _ (Real.exp_pos _) H

 

theorem intrinsicRootLeaf_ergodic_alternative (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    (∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x)) ∨
      (∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  let S : Set (X (d+1)) := {x | intrinsicRootLeaf hij μ x {0} = 0}
  have hm : NullMeasurableSet S μ := by
    exact nullMeasurableSet_eq_fun
      ((Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable
        (aemeasurable_intrinsicRootLeaf hij μ hfree)) aemeasurable_const
  have he : EventuallyEmptyOrUniv S (ae μ) :=
    aeconst_of_forall_preimage_smul_ae_eq (Multiplicative (LogCoordinates d)) hm (by
      intro u
      filter_upwards [ae_intrinsicRootLeaf_atom_diagonal d hij μ hA u.toAdd] with x hx
      change (intrinsicRootLeaf hij μ (rightAction x (diagonalFlow u.toAdd)) {0} = 0) =
        (intrinsicRootLeaf hij μ x {0} = 0)
      rw [hx])
  rcases eventuallyEmptyOrUniv_iff.mp he with hz | hn
  · left
    filter_upwards [hz,ae_intrinsicRootLeaf_nullSingleton_or_dirac d hij μ hA] with x hx h
    rcases h with h | h
    · exact h
    · change intrinsicRootLeaf hij μ x {0} = 0 at hx
      rw [h] at hx
      simp at hx
  · right
    filter_upwards [hn,ae_intrinsicRootLeaf_atom_dirac d hij μ hA] with x hx h
    exact h hx

end PrimeDegreePackets


namespace PrimeDegreePackets

def rootCanonicalWeights (d : ℕ) (j : Fin (d+1)) (k : Fin (d+1)) : ℝ :=
  coordinateContractionWeights d j k / (d+1:ℝ)

lemma rootCanonicalWeights_sum (d : ℕ) (j : Fin (d+1)) :
    ∑ k, rootCanonicalWeights d j k = 0 := by
  simp only [rootCanonicalWeights,←Finset.sum_div,coordinateContractionWeights_sum,zero_div]

lemma rootCanonicalWeights_difference (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j) :
    rootCanonicalWeights d j j - rootCanonicalWeights d j i = 1 := by
  simp only [rootCanonicalWeights,←sub_div]
  have h : coordinateContractionWeights d j j - coordinateContractionWeights d j i = (d+1:ℝ) := by
    simp [coordinateContractionWeights,hij]
  rw [h,div_self (by positivity)]

def rootCanonicalFlow (d : ℕ) (j : Fin (d+1)) (t : ℝ) : G (d+1) :=
  diagonalOneParameter (rootCanonicalWeights d j) (rootCanonicalWeights_sum d j) t

lemma rootCanonicalFlow_preserving (d : ℕ) (j : Fin (d+1)) (t : ℝ)
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    MeasurePreserving (fun x => rightAction x (rootCanonicalFlow d j t)) μ μ := by
  refine ⟨(continuous_rightAction _).measurable,?_⟩
  rw [rootCanonicalFlow,diagonalOneParameter_eq_diagonalFlow]
  exact hA _

 
theorem ae_intrinsicRootLeaf_canonical (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t)) =
      anchorNormalize ((intrinsicRootLeaf hij μ x).map
        (Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t))) (Metric.ball 0 1) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have H := ae_intrinsicRootLeaf_diagonal hij (rootCanonicalWeights d j)
    (rootCanonicalWeights_sum d j) t μ hfree (rootCanonicalFlow_preserving d j t μ hA).map_eq
  have he : rootTimeScaling (rootCanonicalWeights d j) i j t =
      Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t) := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,rootCanonicalWeights_difference d hij,one_mul]
  simpa only [rootCanonicalFlow,he] using H

end PrimeDegreePackets


namespace PrimeDegreePackets

def rootInformation {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (t : ℝ) (x : X n) : ℝ :=
  -Real.log ((intrinsicRootLeaf hij μ x) (Metric.ball 0 (Real.exp (-t)))).toReal

lemma aemeasurable_rootInformation (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    AEMeasurable (rootInformation hij μ t) μ := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  exact ((Measure.measurable_coe (Metric.isOpen_ball (x := (0:ℝ))
    (ε := Real.exp (-t))).measurableSet).comp_aemeasurable
    (aemeasurable_intrinsicRootLeaf hij μ hfree)).ennreal_toReal.log.neg

lemma ae_rootInformation_nonneg (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂μ, 0 ≤ rootInformation hij μ t x := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
  have hle : intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t))) ≤ 1 := by
    rw [←hx.2]
    exact measure_mono (Metric.ball_subset_ball
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)))
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg
    (by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hle))

lemma normalized_realScaling_ball (ν : Measure ℝ) (c r : ℝ) (hc : 0 < c) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)
      (Metric.ball 0 r) = (ν (Metric.ball 0 (1/c)))⁻¹ * ν (Metric.ball 0 (r/c)) := by
  change (ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc.ne') (Metric.ball 0 r) = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc.ne').measurable
      Metric.isOpen_ball.measurableSet,
    realScaling_preimage_ball c 1 hc,realScaling_preimage_ball c r hc]

 
theorem ae_intrinsicRootLeaf_ball_cocycle (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (s t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-(s+t)))) =
      intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t))) *
      intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
        (Metric.ball 0 (Real.exp (-s))) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_canonical d hij μ hA t,
    ae_intrinsicRootLeaf_spec hij μ hfree,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x he hs hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  rw [he,normalized_realScaling_ball _ _ _ (Real.exp_pos _)]
  have h1 : 1/Real.exp t = Real.exp (-t) := by simp [Real.exp_neg,one_div]
  have h2 : Real.exp (-s)/Real.exp t = Real.exp (-(s+t)) := by
    rw [←Real.exp_sub]
    congr 1
    ring
  rw [h1,h2,←mul_assoc,ENNReal.mul_inv_cancel
    (hp _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne,one_mul]

 

theorem ae_rootInformation_cocycle (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (s t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation hij μ (s+t) x = rootInformation hij μ t x +
      rootInformation hij μ s (rightAction x (rootCanonicalFlow d j t)) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hs := ae_intrinsicRootLeaf_spec hij μ hfree
  have hp := ae_intrinsicRootLeaf_ball_pos hij μ hfree
  have hT := rootCanonicalFlow_preserving d j t μ hA
  have hST : ∀ᵐ x ∂μ, IsLocallyFiniteMeasure
      (intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))) := by
    have H : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootCanonicalFlow d j t)),
        IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ y) := by
      rw [hT.map_eq]
      exact hs.mono fun _ h => h.1
    exact ae_of_ae_map hT.measurable.aemeasurable H
  have hPT : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 <
      intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t)) (Metric.ball 0 r) := by
    have H : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootCanonicalFlow d j t)),
        ∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ y (Metric.ball 0 r) := by
      rw [hT.map_eq]
      exact hp
    exact ae_of_ae_map hT.measurable.aemeasurable H
  filter_upwards [ae_intrinsicRootLeaf_ball_cocycle d hij μ hA s t,hs,hp,hST,hPT]
    with x he hs hp hst hpt
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  let : IsLocallyFiniteMeasure
      (intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))) := hst
  have h0 : (intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t)))).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hp _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne).ne'
  have h0T : (intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
      (Metric.ball 0 (Real.exp (-s)))).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hpt _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne).ne'
  dsimp only [rootInformation]
  rw [he,ENNReal.toReal_mul,Real.log_mul h0 h0T]
  ring

end PrimeDegreePackets


namespace PrimeDegreePackets

def rootInformationMean {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (rootInformation hij μ t x) ∂μ

lemma rootInformationMean_add (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    rootInformationMean hij μ (s+t) = rootInformationMean hij μ s + rootInformationMean hij μ t := by
  have hT := rootCanonicalFlow_preserving d j t μ hA
  have hps : ∀ᵐ x ∂μ, 0 ≤ rootInformation hij μ s (rightAction x (rootCanonicalFlow d j t)) := by
    have H : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootCanonicalFlow d j t)),
        0 ≤ rootInformation hij μ s y := by
      rw [hT.map_eq]
      exact ae_rootInformation_nonneg d hij μ hA hs
    exact ae_of_ae_map hT.measurable.aemeasurable H
  have he : (fun x => ENNReal.ofReal (rootInformation hij μ (s+t) x)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (rootInformation hij μ t x) +
        ENNReal.ofReal (rootInformation hij μ s (rightAction x (rootCanonicalFlow d j t)))) := by
    filter_upwards [ae_rootInformation_cocycle d hij μ hA s t,
      ae_rootInformation_nonneg d hij μ hA ht,hps] with x he hpt hps
    rw [he,ENNReal.ofReal_add hpt hps]
  have hms := (aemeasurable_rootInformation d hij μ hA s).ennreal_ofReal
  have hmt := (aemeasurable_rootInformation d hij μ hA t).ennreal_ofReal
  have hmap : ∫⁻ x, ENNReal.ofReal (rootInformation hij μ s
      (rightAction x (rootCanonicalFlow d j t))) ∂μ = rootInformationMean hij μ s := by
    have H : AEMeasurable (fun x => ENNReal.ofReal (rootInformation hij μ s x))
        (μ.map (fun x => rightAction x (rootCanonicalFlow d j t))) := hT.map_eq.symm ▸ hms
    rw [←lintegral_map' H hT.measurable.aemeasurable,hT.map_eq]
    rfl
  rw [rootInformationMean,lintegral_congr_ae he,lintegral_add_left' hmt,hmap,add_comm]
  rfl

lemma rootInformationMean_zero_time (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    rootInformationMean hij μ 0 = 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
  simp [rootInformation,hx.2]

lemma rootInformationMean_nat (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (m : ℕ) :
    rootInformationMean hij μ m = (m:ℝ≥0∞) * rootInformationMean hij μ 1 := by
  induction m with
  | zero => simpa using rootInformationMean_zero_time d hij μ hA
  | succ m ih =>
    rw [Nat.cast_add,Nat.cast_one,rootInformationMean_add d hij μ hA (by positivity) zero_le_one,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

 

lemma ae_rootLeaf_ball_eq_one_of_mean_zero (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    {t : ℝ} (ht : 0 ≤ t) (hz : rootInformationMean hij μ t = 0) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t))) = 1 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have H := (lintegral_eq_zero_iff' (aemeasurable_rootInformation d hij μ hA t).ennreal_ofReal).mp hz
  filter_upwards [H,ae_rootInformation_nonneg d hij μ hA ht,
    ae_intrinsicRootLeaf_spec hij μ hfree,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hz hn hs hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  have he : rootInformation hij μ t x = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hn
  have hlog : Real.log (intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t)))).toReal = 0 := by
    exact neg_eq_zero.mp he
  exact (ENNReal.toReal_eq_one_iff _).mp
    (Real.eq_one_of_pos_of_log_eq_zero
      (ENNReal.toReal_pos (hp _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne) hlog)

 

theorem rootInformationMean_eq_zero_iff_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    rootInformationMean hij μ 1 = 0 ↔
      ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  constructor
  · intro hz
    have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
      (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
    have H : ∀ᵐ x ∂μ, ∀ m : ℕ,
        intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-(m:ℝ)))) = 1 := by
      apply ae_all_iff.mpr
      intro m
      apply ae_rootLeaf_ball_eq_one_of_mean_zero d hij μ hA (by positivity)
      rw [rootInformationMean_nat d hij μ hA,hz,mul_zero]
    filter_upwards [H,ae_intrinsicRootLeaf_spec hij μ hfree,
      ae_intrinsicRootLeaf_atom_dirac d hij μ hA] with x hx hs hd
    apply hd
    have hsmall (m : ℕ) : intrinsicRootLeaf hij μ x (Metric.ball 0 ((m+1:ℝ)⁻¹)) = 1 := by
      apply le_antisymm
      · rw [←hs.2]
        exact measure_mono (Metric.ball_subset_ball (inv_le_one₀ (by positivity) |>.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) m])))
      · rw [←hx m]
        apply measure_mono (Metric.ball_subset_ball ?_)
        rw [Real.exp_neg]
        exact inv_anti₀ (by positivity) (Real.add_one_le_exp _)
    have hanti : Antitone (fun m : ℕ => Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) := by
      intro a b hab
      apply Metric.ball_subset_ball
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    have h0 : intrinsicRootLeaf hij μ x {0} = 1 := by
      rw [←real_iInter_ball_inv_nat,hanti.measure_iInter
        (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet)
        ⟨0,by rw [hsmall]; exact ENNReal.one_ne_top⟩]
      simp only [hsmall,iInf_const]
    rw [h0]
    exact one_ne_zero
  · intro hd
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hd] with x hx
    simp [rootInformation,hx,Measure.dirac_apply_of_mem (Metric.mem_ball_self (Real.exp_pos _))]

end PrimeDegreePackets
end
end

end OAI
