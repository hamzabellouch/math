import Mathlib
import OAI.NumberTheory.PrimePackets.ThetaTails

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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

lemma logScale_selfAdjoint (u : d → ℝ) :
    (logScale u).toContinuousLinearMap.adjoint = (logScale u).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,ContinuousLinearEquiv.coe_coe,logScale_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_assoc,mul_left_comm,mul_comm]

lemma adjointEquiv_logScaledLattice (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) :
    adjointEquiv (logScaledLattice B u).symm =
      logScaledLattice (adjointEquiv B.symm) (-u) := by
  have HE : (logScaledLattice B u).symm.toContinuousLinearMap =
      B.symm.toContinuousLinearMap.comp (logScale u).symm.toContinuousLinearMap := by
    ext x
    rfl
  apply ContinuousLinearEquiv.ext
  funext x
  change ((logScaledLattice B u).symm.toContinuousLinearMap.adjoint) x = _
  rw [HE,ContinuousLinearMap.adjoint_comp,logScale_symm,logScale_selfAdjoint]
  rfl

lemma logScale_det (u : d → ℝ) :
    LinearMap.det (logScale u).toLinearMap = Real.exp (∑ i, u i) := by
  classical
  let b := (EuclideanSpace.basisFun d ℝ).toBasis
  have HE : (logScale u).toLinearMap = Matrix.toLin b b (Matrix.diagonal (fun i => Real.exp (u i))) := by
    ext x i
    rw [Matrix.toLin_apply]
    simp [b,EuclideanSpace.basisFun_apply,Matrix.mulVec,Matrix.diagonal_apply,Pi.single_apply,dotProduct]
  rw [HE,LinearMap.det_toLin,Matrix.det_diagonal,Real.exp_sum]

lemma logScaledLattice_det (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) :
    LinearMap.det (logScaledLattice B u).toLinearMap =
      Real.exp (∑ i, u i) * LinearMap.det B.toLinearMap := by
  change LinearMap.det ((logScale u).toLinearMap.comp B.toLinearMap) = _
  rw [LinearMap.det_comp,logScale_det]

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_sum {d : ℕ} (u : LogCoordinates d) :
    ∑ i, restoredLogCoordinates u i = 0 := by
  simp [restoredLogCoordinates,Fin.sum_univ_castSucc]

lemma restoredLogCoordinates_neg {d : ℕ} (u : LogCoordinates d) :
    restoredLogCoordinates (-u) = -restoredLogCoordinates u := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [restoredLogCoordinates]

 

theorem arithmeticFlowTheta_inversion {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (u : LogCoordinates d) (t : ℝ) (ht : 0 < t) :
    normalizedTheta (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) t = ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) *
      (t:ℂ)^(-((d+1:ℕ):ℂ)/2) *
      normalizedTheta (logScaledLattice
        (fullLatticeEuclideanBasis (traceDualFullLattice M hn) σ hn)
        (restoredLogCoordinates (-u))) t⁻¹ := by
  rw [normalizedTheta_inversion _ t ht,logScaledLattice_det,restoredLogCoordinates_sum,
    Real.exp_zero,one_mul,fullLatticeEuclideanBasis_det,adjointEquiv_logScaledLattice,
    ←traceDualFullLattice_euclideanBasis M σ hn,←restoredLogCoordinates_neg]
  simp only [Fintype.card_fin,neg_div]

 

theorem arithmeticFlowThetaXi_reflection {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (u : LogCoordinates d) (s : ℂ) :
    thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) s = ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) *
      thetaMellinXi (logScaledLattice
        (fullLatticeEuclideanBasis (traceDualFullLattice M hn) σ hn)
        (restoredLogCoordinates (-u))) (((d+1:ℕ):ℂ)/2-s) := by
  rw [thetaMellinXi_functional_equation,logScaledLattice_det,restoredLogCoordinates_sum,
    Real.exp_zero,one_mul,fullLatticeEuclideanBasis_det,adjointEquiv_logScaledLattice,
    ←traceDualFullLattice_euclideanBasis M σ hn,←restoredLogCoordinates_neg]
  simp only [Fintype.card_fin]

 

theorem arithmeticFlowThetaXi_average_reflection {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (S : Set (LogCoordinates d)) (s : ℂ) :
    (∫ u in S, thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) s) = ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) *
      ∫ u in S, thetaMellinXi (logScaledLattice
        (fullLatticeEuclideanBasis (traceDualFullLattice M hn) σ hn)
        (restoredLogCoordinates (-u))) (((d+1:ℕ):ℂ)/2-s) := by
  simp_rw [arithmeticFlowThetaXi_reflection M σ hn]
  exact integral_const_mul _ _

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

theorem averagedThetaMellinXi_differentiable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hdual : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2))
    (hD : StronglyMeasurable (fun p : α × ℝ =>
      normalizedThetaTail (adjointEquiv (B p.1).symm) p.2))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    Differentiable ℂ (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let P := mellin (averagedNormalizedThetaTail μ B)
  let Q := mellin (averagedNormalizedThetaTail μ (fun x => adjointEquiv (B x).symm))
  have HP : Differentiable ℂ P := averagedNormalizedThetaTail_mellin_differentiable μ B R hR hbound hB
  have HQ : Differentiable ℂ Q := averagedNormalizedThetaTail_mellin_differentiable μ _ T hT hdual hD
  have HE : (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) =
      fun s => s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
    funext s
    have hP := normalizedThetaTail_mellin_integrable μ B R hR hbound hB s
    have hQ := normalizedThetaTail_mellin_integrable μ _ T hT hdual hD (a-s)
    have hQc : Integrable (fun x => c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hQ.const_mul c
    have hPQ : Integrable (fun x => mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) μ := hP.add hQc
    have hPQc : Integrable (fun x => s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
        c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s))) μ := hPQ.const_mul _
    have HPv := averagedNormalizedThetaTail_mellin_eq_integral μ B R hR hbound hB s
    have HQv := averagedNormalizedThetaTail_mellin_eq_integral μ _ T hT hdual hD (a-s)
    calc
      (∫ x, thetaMellinXi (B x) s ∂μ) = ∫ x,
          s*(s-a)*(mellin (normalizedThetaTail (B x)) s +
            c*mellin (normalizedThetaTail (adjointEquiv (B x).symm)) (a-s)) +
          (c*s-(s-a)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by simp only [thetaMellinXi,hc x]; dsimp [a]; ring)
      _ = s*(s-a)*(P s+c*Q (a-s)) + (μ.real Set.univ:ℂ)*(c*s-(s-a)) := by
        rw [integral_add hPQc (integrable_const (c*s-(s-a))),
          integral_const_mul,integral_add hP hQc,integral_const_mul,
          integral_const,←HPv,←HQv]
        simp only [P,Q,Complex.real_smul]
  rw [HE]
  fun_prop

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_abs_bound_on_compact {d : ℕ} {S : Set (LogCoordinates d)}
    (hS : IsCompact S) : ∃ R : ℝ, ∀ u ∈ S, ∀ i, |restoredLogCoordinates u i| ≤ R := by
  let f : LogCoordinates d → ℝ := fun u => ∑ i, |restoredLogCoordinates u i|
  have hf : Continuous f := continuous_finsetSum _ (fun i _ =>
    (restoredLogCoordinates_continuous i).abs)
  obtain ⟨R,hR⟩ := hS.bddAbove_image hf.continuousOn
  refine ⟨R,fun u hu i => le_trans ?_ (hR (Set.mem_image_of_mem f hu))⟩
  change |restoredLogCoordinates u i| ≤ ∑ j, |restoredLogCoordinates u j|
  exact Finset.single_le_sum (fun j _ => abs_nonneg (restoredLogCoordinates u j)) (Finset.mem_univ i)

 

theorem arithmeticFlowThetaXi_boundedAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    Differentiable ℂ (fun s => ∫ u in S,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) := by
  let μ : Measure S := Measure.comap ((↑) : S → LogCoordinates d) volume
  have hμ : IsFiniteMeasure μ := ⟨by
    dsimp only [μ]
    rw [comap_subtype_coe_apply hS,Set.image_univ,Subtype.range_coe]
    exact hbd.measure_lt_top⟩
  let B := fullLatticeEuclideanBasis M σ hn
  let u : S → Fin (d+1) → ℝ := fun x => restoredLogCoordinates x.1
  let F := fun x : S => logScaledLattice B (u x)
  have hu : ∀ i, Measurable (fun x => u x i) := fun i =>
    ((restoredLogCoordinates_continuous i).comp continuous_subtype_val).measurable
  obtain ⟨U,hU⟩ := restoredLogCoordinates_abs_bound_on_compact hbd.isCompact_closure
  let R := ‖B.symm.toContinuousLinearMap‖*Real.exp U
  let T := ‖(adjointEquiv B.symm).symm.toContinuousLinearMap‖*Real.exp U
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hT : 0 ≤ T := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have HB : ∀ x, ‖(F x).symm.toContinuousLinearMap‖ ≤ R := by
    intro x
    exact logScaledLattice_inverse_bound B (fun i =>
      (neg_le_abs _).trans (hU x.1 (subset_closure x.2) i))
  have HD : ∀ x, ‖(adjointEquiv (F x).symm).symm.toContinuousLinearMap‖ ≤ T := by
    intro x
    rw [show F x = logScaledLattice B (u x) from rfl,adjointEquiv_logScaledLattice]
    apply logScaledLattice_inverse_bound
    intro i
    simp only [Pi.neg_apply,neg_neg]
    exact (le_abs_self _).trans (hU x.1 (subset_closure x.2) i)
  have HM : StronglyMeasurable (fun p : S × ℝ => normalizedThetaTail (F p.1) p.2) :=
    normalizedThetaTail_joint_stronglyMeasurable (B := F)
      (fun z => logScaledLattice_measurable_apply B u hu (euclideanInteger z))
  have HN : StronglyMeasurable (fun p : S × ℝ =>
      normalizedThetaTail (adjointEquiv (F p.1).symm) p.2) := by
    have HE : (fun x => adjointEquiv (F x).symm) =
        fun x => logScaledLattice (adjointEquiv B.symm) (-u x) := by
      funext x
      exact adjointEquiv_logScaledLattice B (u x)
    simp_rw [show ∀ x, adjointEquiv (F x).symm =
      logScaledLattice (adjointEquiv B.symm) (-u x) from congrFun HE]
    exact normalizedThetaTail_joint_stronglyMeasurable
      (B := fun x => logScaledLattice (adjointEquiv B.symm) (-u x))
      (fun z => logScaledLattice_measurable_apply _ _ (fun i => (hu i).neg) (euclideanInteger z))
  have HC : ∀ x, ((|(LinearMap.det (F x).toLinearMap)⁻¹|:ℝ):ℂ) =
      ((|(embeddingMatrix M σ).det⁻¹|:ℝ):ℂ) := by
    intro x
    dsimp only [F,u]
    rw [logScaledLattice_det,restoredLogCoordinates_sum,Real.exp_zero,one_mul,
      show LinearMap.det B.toLinearMap = (embeddingMatrix M σ).det from
        fullLatticeEuclideanBasis_det M σ hn]
  have H := averagedThetaMellinXi_differentiable μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s := by
    funext s
    exact integral_subtype_comap hS (fun u => thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s)
  rw [HE] at H
  exact H

end PrimeDegreePackets

open MeasureTheory Module WithLp
namespace PrimeDegreePackets
open ThetaConstruction

 

theorem arithmeticFlowThetaXi_unitAverage_entire {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    Differentiable ℂ (fun s => ∫ u in orderedThetaLogDomain σ,
      thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s) :=
  arithmeticFlowThetaXi_boundedAverage_entire M σ hn
    (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)

 

theorem arithmeticFlowThetaXi_average_eq_epstein {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (S : Set (LogCoordinates d)) {s : ℂ} (hs : ((d+1:ℕ):ℝ)/2 < s.re) :
    (∫ u in S, thetaMellinXi (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
      (restoredLogCoordinates u)) s) =
      (s*(s-((d+1:ℕ):ℂ)/2)*Complex.Gamma s) *
      ∫ u in S, latticeEpsteinSeries (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
        (restoredLogCoordinates u)) s := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have h0 : s ≠ 0 := by intro H; simp [H] at hs0
  have ha : s ≠ ((d+1:ℕ):ℂ)/2 := by
    intro H
    have HE : s.re = ((d+1:ℕ):ℝ)/2 := by simp [H]
    linarith
  calc
    _ = ∫ u in S, (s*(s-((d+1:ℕ):ℂ)/2)*Complex.Gamma s)*
        latticeEpsteinSeries (logScaledLattice (fullLatticeEuclideanBasis M σ hn)
          (restoredLogCoordinates u)) s := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only
      rw [thetaMellinXi_eq _ h0 (by simpa only [Fintype.card_fin] using ha),
        thetaMellinContinuation_eq_epstein _ (by simpa only [Fintype.card_fin] using hs)]
      simp only [Fintype.card_fin,mul_assoc]
    _ = _ := integral_const_mul _ _

end PrimeDegreePackets

open scoped BigOperators NumberField nonZeroDivisors ENNReal
namespace PrimeDegreePackets
open ThetaConstruction

 
def arithmeticFlowGaussian {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (t : ℝ) (u : LogCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-Real.pi*t*∑ i, (logFlowWeights u i*σ i a)^2))

lemma arithmeticFlowGaussian_measurable {d : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings (d+1) K) (a : K) (t : ℝ) :
    Measurable (arithmeticFlowGaussian σ a t) := by
  unfold arithmeticFlowGaussian
  apply Measurable.ennreal_ofReal
  apply Continuous.measurable
  apply Continuous.rexp
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp continuous_logFlowWeights).mul_const _).pow 2

lemma arithmeticFlowGaussian_unit_translate {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (a : K) (z : (𝓞 K)ˣ) (t : ℝ) (u : LogCoordinates d) :
    arithmeticFlowGaussian σ ((z:K)*a) t u =
      arithmeticFlowGaussian σ a t (orderedUnitLog σ (Additive.ofMul z)+u) := by
  unfold arithmeticFlowGaussian
  simp only [map_mul,logFlowWeights_add,logFlowWeights_orderedUnitLog]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply,mul_pow,sq_abs]
  ring

 

theorem lintegral_arithmeticFlowGaussian_units {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (Module.finrank ℚ K))
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (a : K) (t : ℝ) :
    (∫⁻ u in S, ∑' z : (𝓞 K)ˣ, arithmeticFlowGaussian σ ((z:K)*a) t u) =
      2*∫⁻ u, arithmeticFlowGaussian σ a t u := by
  simp_rw [arithmeticFlowGaussian_unit_translate]
  let «φ» := orderedUnitLogOnto σ
  let : Finite «φ».ker := Nat.finite_of_card_ne_zero (by rw [orderedUnitLogOnto_ker_card σ hodd]; decide)
  have H := lintegral_tsum_addHom_fundamentalDomain (orderedLogSubgroup σ ⊤) «φ»
    (orderedUnitLogOnto_surjective σ) hS (arithmeticFlowGaussian σ a t)
    (arithmeticFlowGaussian_measurable σ a t)
  rw [orderedUnitLogOnto_ker_card σ hodd] at H
  exact H

 

theorem lintegral_arithmeticFlowGaussian_ideal {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (Module.finrank ℚ K))
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) :
    (∫⁻ u in S, ∑' a : nonzeroIdealElements I, arithmeticFlowGaussian σ a.1.1 t u) =
      2*∑' J : integralIdealClassFiber I,
        ∫⁻ u, arithmeticFlowGaussian σ (idealElementRepresentative I J).1.1 t u := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := NumberField.RingOfIntegers.coe_injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    infer_instance
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have HE (u : LogCoordinates d) :
      (∑' a : nonzeroIdealElements I, arithmeticFlowGaussian σ a.1.1 t u) =
      ∑' J : integralIdealClassFiber I, ∑' z : (𝓞 K)ˣ,
        arithmeticFlowGaussian σ ((z:K)*(idealElementRepresentative I J).1.1) t u := by
    simpa only [one_mul] using tsum_relativeElementIdeal I (fun _ => 1)
      (fun a => arithmeticFlowGaussian σ a t u)
  simp_rw [HE]
  rw [lintegral_tsum (fun J => (Measurable.tsum (fun z : (𝓞 K)ˣ =>
    arithmeticFlowGaussian_measurable σ ((z:K)*(idealElementRepresentative I J).1.1) t)).aemeasurable)]
  simp_rw [lintegral_arithmeticFlowGaussian_units σ hodd hS]
  exact ENNReal.tsum_mul_left

end PrimeDegreePackets


namespace PrimeDegreePackets
open ThetaConstruction

 

def fractionalIdealNonzeroIntegerEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    NonzeroIntegerVector (Fin n) ≃ nonzeroIdealElements I := by
  let M := fractionalIdealFullLattice hn I
  let e : NonzeroIntegerVector (Fin n) ≃ {a : M.carrier // a ≠ 0} :=
    M.basis.equivFun.symm.toEquiv.subtypeEquiv (by
      intro z
      change z ≠ 0 ↔ M.basis.equivFun.symm z ≠ 0
      constructor
      · intro hz h
        apply hz
        apply M.basis.equivFun.symm.injective
        simpa only [_root_.map_zero] using h
      · intro hz h
        apply hz
        rw [h, _root_.map_zero])
  let f : {a : M.carrier // a ≠ 0} ≃ nonzeroIdealElements I :=
    { toFun := fun a => ⟨Units.mk0 (a.1:K) (by
        intro H
        exact a.2 (Subtype.ext H)),a.1.property⟩
      invFun := fun a => ⟨⟨(a.1:K),a.2⟩,by
        intro H
        exact a.1.ne_zero (congrArg Subtype.val H)⟩
      left_inv := fun a => by apply Subtype.ext; rfl
      right_inv := fun a => by apply Subtype.ext; apply Units.ext; rfl }
  exact e.trans f

lemma normalizedTheta_fractionalIdeal_gaussian_sum {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : LogCoordinates d) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal ((normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates u)) t - 1).re) =
      ∑' a : nonzeroIdealElements I, arithmeticFlowGaussian σ a.1.1 t u := by
  let M := fractionalIdealFullLattice hn I
  let B := logScaledLattice (fullLatticeEuclideanBasis M σ hn) (restoredLogCoordinates u)
  let e := fractionalIdealNonzeroIntegerEquiv hn I
  have HE (z : NonzeroIntegerVector (Fin (d+1))) :
      arithmeticFlowGaussian σ (e z).1.1 t u =
        ENNReal.ofReal (Real.exp (-latticeEnergy B z*t)) := by
    change arithmeticFlowGaussian σ (M.basis.equivFun.symm z.1 : K) t u = _
    unfold arithmeticFlowGaussian latticeEnergy
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [show ∀ i, B (euclideanInteger z.1) i =
      logFlowWeights u i*σ i (M.basis.equivFun.symm z.1 : K) from
        arithmeticFlowTheta_vector M σ hn u z.1]
    congr 2
    ring
  change ENNReal.ofReal ((normalizedTheta B t-1).re) = _
  rw [normalizedTheta,←thetaRemainder_eq B (mul_pos Real.pi_pos ht),
    thetaRemainder_eq_real_sum B ht,Complex.ofReal_re,
    ENNReal.ofReal_tsum_of_nonneg (fun z => (Real.exp_pos _).le) (realGaussian_summable B ht)]
  calc
    _ = ∑' z, arithmeticFlowGaussian σ (e z).1.1 t u := tsum_congr (fun z => (HE z).symm)
    _ = _ := e.tsum_eq (fun a : nonzeroIdealElements I => arithmeticFlowGaussian σ a.1.1 t u)

 

theorem fractionalIdealTheta_unit_unfolding {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (Module.finrank ℚ K)) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {S : Set (LogCoordinates d)} (hS : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) S volume)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ u in S, ENNReal.ofReal ((normalizedTheta
      (logScaledLattice (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
        (restoredLogCoordinates u)) t - 1).re)) =
      2*∑' J : integralIdealClassFiber I,
        ∫⁻ u, arithmeticFlowGaussian σ (idealElementRepresentative I J).1.1 t u := by
  simp_rw [normalizedTheta_fractionalIdeal_gaussian_sum σ hn I _ ht]
  exact lintegral_arithmeticFlowGaussian_ideal σ hodd hS I t

end PrimeDegreePackets
end
end

end OAI
