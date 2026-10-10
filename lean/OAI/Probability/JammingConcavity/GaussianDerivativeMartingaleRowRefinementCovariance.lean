import Mathlib
import OAI.Probability.JammingConcavity.GaussianDerivativeMartingale

namespace OAI

/-! Gaussian Derivative Martingale Row Refinement Covariance. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma rowSignedPairMean_integrable {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (j : ℕ) (hj : j ≤ ms.length) (x : ℝ)
    (μ : Measure (FamilyCascadeTree ℝ ms.length)) [IsFiniteMeasure μ] :
    Integrable (fun ω => ∫ ℓ, rowSignedPairObservable ms u j x ω ℓ
      ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)) μ := by
  let A : ℝ := 1/(2*(L+1))
  let B : ℝ := 1/2
  have hAp : 0 < A := by dsimp [A]; positivity [hu.L_nonneg]
  have hA : |A| * L ≤ B := by
    dsimp [A,B]
    rw [abs_of_pos (by positivity [hu.L_nonneg]),one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity [hu.L_nonneg] : 0 < 2*(L+1))).mpr
    linarith
  have hB : B+|A| * L ≤ 1 := by dsimp [B] at *; linarith
  have hnA : |-A| * L ≤ B := by simpa using hA
  have hnB : B+|-A| * L ≤ 1 := by simpa using hB
  have hzA : |(0:ℝ)| * L ≤ B := by norm_num [B]
  have hzB : B+|(0:ℝ)| * L ≤ 1 := by norm_num [B]
  have hp := rowAffineIidMean_integrable hu.diff.continuous.measurable hu.slope hA hB ms j hj x μ
  have hn := rowAffineIidMean_integrable hu.diff.continuous.measurable hu.slope hnA hnB ms j hj x μ
  have hz := rowAffineIidMean_integrable hu.diff.continuous.measurable hu.slope hzA hzB ms j hj x μ
  have hi := ((hp.add hn).sub (hz.const_mul 2)).const_mul (2*A^2)⁻¹
  apply hi.congr
  apply Eventually.of_forall
  intro ω
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [← rowSignedPairMean_polarization hu.L_nonneg hu.slope hA hB]
  rw [← mul_assoc,inv_mul_cancel₀ (show 2*A^2 ≠ 0 by positivity),one_mul]

lemma rowFiniteRankObservable_eq_sum (ms : List ℝ) (u : ℝ → ℝ) (B : ℕ → ℝ)
    (x : ℝ) (ω : FamilyCascadeTree ℝ ms.length) (ℓ : Fin 2 → CascadePath ms.length) :
    B (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1)) *
      (deriv u (familyPathMark ms.length x ω (ℓ 0))*deriv u (familyPathMark ms.length x ω (ℓ 1))) =
    ∑ j ∈ Finset.range (ms.length+1), B j * rowSignedPairObservable ms u j x ω ℓ := by
  rw [Finset.sum_eq_single (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1))]
  · simp [rowSignedPairObservable]
  · intro j hj hne
    simp [rowSignedPairObservable,Ne.symm hne]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_of_le (cascadeSharedEdges_le _ _ _)))).elim

lemma rowFiniteRankTest_expectation {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (hord : ms.Pairwise (· < ·)) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (B : ℕ → ℝ) (x : ℝ) :
    (∫ ω, (∫ ℓ : Fin 2 → CascadePath ms.length,
        B (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1)) *
          (deriv u (familyPathMark ms.length x ω (ℓ 0))*deriv u (familyPathMark ms.length x ω (ℓ 1)))
        ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω))
      ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
    ∫ s in (0:ℝ)..1, B (rpcStepLevel ms s)*rowDerivativeDepthMoment (rowGaussianBlocks ms d) u (rpcStepLevel ms s) x := by
  have hν (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  let := familyCascadeLaw_probability ms.length (rowGaussianLaw d) hν
  have he (ω : FamilyCascadeTree ℝ ms.length) :
      (∫ ℓ : Fin 2 → CascadePath ms.length, B (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1)) *
          (deriv u (familyPathMark ms.length x ω (ℓ 0))*deriv u (familyPathMark ms.length x ω (ℓ 1)))
        ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)) =
      ∑ j ∈ Finset.range (ms.length+1), B j*(∫ ℓ, rowSignedPairObservable ms u j x ω ℓ
        ∂Measure.pi (fun _ : Fin 2 => familySampleLeafLaw ms u x ω)) := by
    simp_rw [rowFiniteRankObservable_eq_sum]
    rw [integral_finsetSum _ (fun j hj => (rowSignedPairObservable_integrable hu.L_nonneg hu.slope ms j x ω).const_mul (B j))]
    simp_rw [integral_const_mul]
  simp_rw [he]
  rw [integral_finsetSum _ (fun j hj => (rowSignedPairMean_integrable hu ms j
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x _).const_mul (B j))]
  simp_rw [integral_const_mul]
  rw [integral_rpcStepTest_weights ms hord (fun m hm => (hms m hm).2) 0
    zero_lt_one (fun m hm => (hms m hm).1) (fun j => B j*rowDerivativeDepthMoment (rowGaussianBlocks ms d) u j x)]
  simp only [sub_zero,one_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rowSignedPair_expectation hu ms hord hms d j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x]
  unfold rowPairWeight
  ring

theorem rowFiniteRankTest : RowFiniteRankTestStatement := by
  intro u L H hu hL hH hb ms hord hms d Δ B x
  have hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),
    hu'.differentiable (by norm_num),hL,hH,fun y => (hb y).1,fun y => (hb y).2⟩
  have hv := rowBoundedOperator_terminal ht (by norm_num : (0:ℝ) ≤ 1) le_rfl (Δ:ℝ)
  exact rowFiniteRankTest_expectation hv ms hord hms d B x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma familyPathWeight_forget {E : Type} (ms : List ℝ)
    (ω : FamilyCascadeTree E ms.length) (ℓ : CascadePath ms.length) :
    cascadePathWeight ms (forgetFamilyMarks ms.length ω) ℓ = familyPathWeight ms ω ℓ := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change (if ℓ.1.2 < (ω ℓ.1.1).1 then
      ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m))*
        cascadePathWeight ms (forgetFamilyMarks ms.length ((ω ℓ.1.1).2 ℓ.1.2).2.2) ℓ.2 else 0) = _
    rw [ih]
    rfl

lemma familyBaseLeaf_lintegral (ms : List ℝ) (u : ℝ → ℝ) (x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length)
    (hω : 0 < familyUnmarkedTotal ms ω ∧ familyUnmarkedTotal ms ω < ∞) :
    (∫⁻ ℓ, ENNReal.ofReal (Real.exp (u (familyPathMark ms.length x ω ℓ)))
      ∂cascadeLeafLaw ms (forgetFamilyMarks ms.length ω)) =
      familyLeafTotal ms u x ω / familyUnmarkedTotal ms ω := by
  rw [lintegral_countable']
  simp_rw [cascadeLeafLaw_singleton_good ms _ hω, familyPathWeight_forget]
  simp only [div_eq_mul_inv]
  simp_rw [← mul_assoc, mul_comm (ENNReal.ofReal _) (familyPathWeight ms ω _)]
  rw [ENNReal.tsum_mul_right]
  change (∑' ℓ, familyLeafMass ms u x ω ℓ) * (familyUnmarkedTotal ms ω)⁻¹ = _
  rw [tsum_familyLeafMass]

lemma familyBaseLeaf_Z (ms : List ℝ) (u : ℝ → ℝ) (x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length)
    (hω : 0 < familyUnmarkedTotal ms ω ∧ familyUnmarkedTotal ms ω < ∞) :
    (∫ ℓ, Real.exp (u (familyPathMark ms.length x ω ℓ))
      ∂cascadeLeafLaw ms (forgetFamilyMarks ms.length ω)) =
      (familyLeafTotal ms u x ω / familyUnmarkedTotal ms ω).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (measurable_of_countable _).aestronglyMeasurable, familyBaseLeaf_lintegral ms u x ω hω]

lemma familySampleLeafLaw_eq_tilted (ms : List ℝ) (u : ℝ → ℝ) (x : ℝ)
    (ω : FamilyCascadeTree ℝ ms.length)
    (hω : 0 < familyUnmarkedTotal ms ω ∧ familyUnmarkedTotal ms ω < ∞)
    (hT : 0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞) :
    familySampleLeafLaw ms u x ω =
      (cascadeLeafLaw ms (forgetFamilyMarks ms.length ω)).tilted
        (fun ℓ => u (familyPathMark ms.length x ω ℓ)) := by
  let T := familyLeafTotal ms u x ω
  let S := familyUnmarkedTotal ms ω
  have hTS0 : T/S ≠ 0 := (ENNReal.div_pos hT.1.ne' hω.2.ne).ne'
  have hTSI : T/S ≠ ∞ := ENNReal.div_ne_top hT.2.ne hω.1.ne'
  apply Measure.ext_of_singleton
  intro ℓ
  rw [familySampleLeafLaw_singleton ms u x ω hT,tilted_apply' _ _ (measurableSet_singleton _),
    lintegral_singleton, familyBaseLeaf_Z ms u x ω hω,
    cascadeLeafLaw_singleton_good ms _ hω, familyPathWeight_forget]
  change familyPathWeight ms ω ℓ * ENNReal.ofReal (Real.exp _) / T =
    ENNReal.ofReal (Real.exp _ / (T/S).toReal)*(familyPathWeight ms ω ℓ/S)
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hTS0 hTSI), ENNReal.ofReal_toReal hTSI]
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.inv_div (Or.inl hω.2.ne) (Or.inl hω.1.ne')]
  simp only [div_eq_mul_inv]
  calc
    _ = ENNReal.ofReal (Real.exp _) * (familyPathWeight ms ω ℓ * T⁻¹) := by ring
    _ = ENNReal.ofReal (Real.exp _) * (familyPathWeight ms ω ℓ * T⁻¹) * (S*S⁻¹) := by
      rw [ENNReal.mul_inv_cancel hω.1.ne' hω.2.ne,mul_one]
    _ = _ := by ring

lemma replica_normalized_eq_tilted {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (G : Kernel Ω S) [IsMarkovKernel G] (V : Ω × S → ℝ) {r : ℕ}
    (B : Ω × (Fin r → S) → ℝ) (ω : Ω) :
    replicaNum G V B ω / (replicaZ G V ω)^r =
      ∫ xs, B (ω,xs) ∂Measure.pi (fun _ : Fin r => (G ω).tilted (fun x => V (ω,x))) := by
  rw [← gibbsMean_replicas_eq]
  unfold gibbsMean
  rw [gibbsZ_replicas]
  simp only [replicaPotential,Real.exp_sum,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma replica_pair_abs_le {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (G : Kernel Ω S) [IsMarkovKernel G] (V : Ω × S → ℝ)
    (B : Ω × (Fin 2 → S) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hB : Measurable B) (hb : ∀ z, |B z| ≤ K) (ω : Ω) :
    |replicaNum G V B ω / (replicaZ G V ω)^2| ≤ K := by
  by_cases hi : Integrable (fun x => Real.exp (V (ω,x))) (G ω)
  · let := isProbabilityMeasure_tilted hi
    rw [replica_normalized_eq_tilted]
    have hf : Integrable (fun xs => B (ω,xs))
        (Measure.pi (fun _ : Fin 2 => (G ω).tilted (fun x => V (ω,x)))) :=
      (integrable_const K).mono' (hB.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall (fun xs => by simpa only [Real.norm_eq_abs] using hb (ω,xs)))
    calc
      _ ≤ ∫ xs, |B (ω,xs)| ∂Measure.pi (fun _ : Fin 2 => (G ω).tilted (fun x => V (ω,x))) := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Fin 2 → S, K ∂Measure.pi (fun _ : Fin 2 => (G ω).tilted (fun x => V (ω,x))) :=
        integral_mono hf.norm (integrable_const _) (fun xs => hb (ω,xs))
      _ = K := by simp
  · simp [replicaZ,integral_undef hi,hK]

def familyCoordinateKernel (ms : List ℝ) :
    Kernel (ℝ × FamilyCascadeTree ℝ ms.length) (CascadePath ms.length) :=
  ⟨fun z => cascadeLeafLaw ms (forgetFamilyMarks ms.length z.2),
    (measurable_cascadeLeafLaw ms).comp ((measurable_forgetFamilyMarks ms.length).comp measurable_snd)⟩
instance (ms : List ℝ) : IsMarkovKernel (familyCoordinateKernel ms) :=
  ⟨fun z => cascadeLeafLaw_probability ms (forgetFamilyMarks ms.length z.2)⟩
def familyCoordinatePotential (ms : List ℝ) (u : ℝ → ℝ)
    (z : (ℝ × FamilyCascadeTree ℝ ms.length) × CascadePath ms.length) : ℝ :=
  u (familyPathMark ms.length z.1.1 z.1.2 z.2)
def familyCoordinatePair (ms : List ℝ) (u : ℝ → ℝ) (B : ℕ → ℝ)
    (z : (ℝ × FamilyCascadeTree ℝ ms.length) × (Fin 2 → CascadePath ms.length)) : ℝ :=
  B (cascadeSharedEdges ms.length (z.2 0) (z.2 1)) *
    (deriv u (familyPathMark ms.length z.1.1 z.1.2 (z.2 0)) *
     deriv u (familyPathMark ms.length z.1.1 z.1.2 (z.2 1)))

lemma measurable_familyCoordinatePotential (ms : List ℝ) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (familyCoordinatePotential ms u) := by
  apply measurable_from_prod_countable_left
  intro ℓ
  exact hu.comp (measurable_familyPathMark ms.length ℓ)
lemma measurable_familyCoordinatePair (ms : List ℝ) {u : ℝ → ℝ} (hu : Measurable (deriv u)) (B : ℕ → ℝ) :
    Measurable (familyCoordinatePair ms u B) := by
  apply measurable_from_prod_countable_left
  intro ℓ
  exact ((hu.comp (measurable_familyPathMark ms.length (ℓ 0))).mul
    (hu.comp (measurable_familyPathMark ms.length (ℓ 1)))).const_mul (B (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1)))
lemma measurable_rowCoordinatePotential (ms : List ℝ) {u : ℝ → ℝ} (hu : Measurable u) :
    Measurable (rowCoordinatePotential ms u) := by
  apply measurable_from_prod_countable_left
  intro ℓ
  exact hu.comp ((measurable_rootPathField_pair ms.length).comp (measurable_const.prodMk measurable_snd))
lemma measurable_rowCoordinatePair (ms : List ℝ) {u : ℝ → ℝ} (hu : Measurable (deriv u)) (B : ℕ → ℝ) :
    Measurable (rowCoordinatePair ms u B) := by
  apply measurable_from_prod_countable_left
  intro ℓ
  exact ((hu.comp ((measurable_rootPathField_pair ms.length).comp
      ((measurable_const (a := ℓ 0)).prodMk measurable_snd))).mul
    (hu.comp ((measurable_rootPathField_pair ms.length).comp
      ((measurable_const (a := ℓ 1)).prodMk measurable_snd)))).const_mul (B (cascadeSharedEdges ms.length (ℓ 0) (ℓ 1)))

lemma familyCoordinatePair_bound {u : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hu : ∀ y, |deriv u y| ≤ L) (ms : List ℝ) (B : ℕ → ℝ) (z) :
    |familyCoordinatePair ms u B z| ≤ (∑ j ∈ Finset.range (ms.length+1), |B j|)*L^2 := by
  unfold familyCoordinatePair
  rw [abs_mul,abs_mul]
  apply mul_le_mul
  · exact Finset.single_le_sum (fun j _ => abs_nonneg (B j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (cascadeSharedEdges_le _ _ _)))
  · nlinarith [hu (familyPathMark ms.length z.1.1 z.1.2 (z.2 0)),
      hu (familyPathMark ms.length z.1.1 z.1.2 (z.2 1)),
      abs_nonneg (deriv u (familyPathMark ms.length z.1.1 z.1.2 (z.2 0))),
      abs_nonneg (deriv u (familyPathMark ms.length z.1.1 z.1.2 (z.2 1)))]
  · positivity
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma familyCoordinate_pair_expectation {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (hord : ms.Pairwise (· < ·)) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (B : ℕ → ℝ) (x : ℝ) :
    (∫ ω, replicaNum (familyCoordinateKernel ms) (familyCoordinatePotential ms u)
        (familyCoordinatePair ms u B) (x,ω) /
      (replicaZ (familyCoordinateKernel ms) (familyCoordinatePotential ms u) (x,ω))^2
      ∂familyCascadeLaw ms.length (rowGaussianLaw d)) =
    ∫ s in (0:ℝ)..1, B (rpcStepLevel ms s)*rowDerivativeDepthMoment (rowGaussianBlocks ms d) u (rpcStepLevel ms s) x := by
  have hν (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  have hU := (familyUnmarkedTotal_properties ms hord hms (rowGaussianLaw d) hν).1
  have hT := scaledLaw_positive _ (familyLeafTotal_identDistrib ms hord hms (rowGaussianLaw d) hν
    hu.diff.continuous.measurable (rowGaussian_recursion hu ms hms d).2 x) hU
  rw [← rowFiniteRankTest_expectation hu ms hord hms d B x]
  apply integral_congr_ae
  filter_upwards [hU,hT] with ω hU hT
  rw [replica_normalized_eq_tilted]
  have ht := familySampleLeafLaw_eq_tilted ms u x ω hU hT
  simp only [familyCoordinateKernel,Kernel.coe_mk,familyCoordinatePotential,← ht]
  rfl

lemma rowDirectingPair_expectation {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (hord : ms.Pairwise (· < ·)) (hms : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (B : ℕ → ℝ) :
    (∫ ω, replicaNum (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms u)
        (rowCoordinatePair ms u B) ω /
      (replicaZ (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms u) ω)^2
      ∂rowReplicaEnvironmentLaw ms d p₀) =
    ∫ x, (∫ s in (0:ℝ)..1, B (rpcStepLevel ms s)*rowDerivativeDepthMoment (rowGaussianBlocks ms d) u (rpcStepLevel ms s) x)
      ∂gaussianReal 0 p₀ := by
  let f := fun z : ℝ × FamilyCascadeTree ℝ ms.length =>
    replicaNum (familyCoordinateKernel ms) (familyCoordinatePotential ms u) (familyCoordinatePair ms u B) z /
      (replicaZ (familyCoordinateKernel ms) (familyCoordinatePotential ms u) z)^2
  let g := fun ω : RowReplicaEnvironment ms.length =>
    replicaNum (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms u) (rowCoordinatePair ms u B) ω /
      (replicaZ (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms u) ω)^2
  have hf : Measurable f := (measurable_replicaNum _ (measurable_familyCoordinatePotential ms hu.diff.continuous.measurable)
    (measurable_familyCoordinatePair ms hu.diff_deriv.continuous.measurable B)).div
      ((measurable_replicaZ _ (measurable_familyCoordinatePotential ms hu.diff.continuous.measurable)).pow_const 2)
  have hg : Measurable g := (measurable_replicaNum _ (measurable_rowCoordinatePotential ms hu.diff.continuous.measurable)
    (measurable_rowCoordinatePair ms hu.diff_deriv.continuous.measurable B)).div
      ((measurable_replicaZ _ (measurable_rowCoordinatePotential ms hu.diff.continuous.measurable)).pow_const 2)
  have (k : ℕ) : IsProbabilityMeasure (rowGaussianLaw d k) := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 (d k)))
  let := familyCascadeLaw_probability ms.length (rowGaussianLaw d) (fun _ => inferInstance)
  have he := integral_cascade_coordinates ms (gaussianReal 0 p₀) (rowGaussianLaw d) hf hg (by
    intro ω x y
    simp only [f,g,replicaNum,replicaZ,familyCoordinateKernel,Kernel.coe_mk,
      familyCoordinatePotential,familyCoordinatePair,rowCoordinateLeafKernel,rowCoordinatePotential,rowCoordinatePair,
      forgetFamilyMarks_zip,rootPathField_eq])
  have hlaw : (fun i : Option (CascadeMarkIndex ms.length) => i.elim (gaussianReal 0 p₀)
        (fun j => rowGaussianLaw d (cascadeMarkDepth ms.length j))) =
      (fun i => gaussianReal 0 (rootCoordinateVariance ms.length d p₀ i)) := by
    funext i
    cases i <;> rfl
  rw [hlaw] at he
  change (∫ ω, g ω ∂rowReplicaEnvironmentLaw ms d p₀) = _
  unfold rowReplicaEnvironmentLaw
  rw [← he]
  have hfi : Integrable f ((gaussianReal 0 p₀).prod (familyCascadeLaw ms.length (rowGaussianLaw d))) := by
    let K := (∑ j ∈ Finset.range (ms.length+1), |B j|)*L^2
    have hK : 0 ≤ K := mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (sq_nonneg _)
    apply (integrable_const K).mono' hf.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs]
    exact replica_pair_abs_le _ _ _ hK (measurable_familyCoordinatePair ms hu.diff_deriv.continuous.measurable B)
      (familyCoordinatePair_bound hu.L_nonneg hu.slope ms B) z
  rw [integral_prod _ hfi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => familyCoordinate_pair_expectation hu ms hord hms d B x)

theorem rowDirectingPair : RowDirectingPairStatement := by
  intro u L H hu hL hH hb ms hord hms d p₀ Δ B
  have hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),
    hu'.differentiable (by norm_num),hL,hH,fun y => (hb y).1,fun y => (hb y).2⟩
  have hv := rowBoundedOperator_terminal ht (by norm_num : (0:ℝ) ≤ 1) le_rfl (Δ:ℝ)
  exact rowDirectingPair_expectation hv ms hord hms d p₀ B
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma residual_weight_integrable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (Δ : ℝ≥0) (x : ℝ) : Integrable (fun z => Real.exp (u (x+z))) (gaussianReal 0 Δ) := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  rw [rowGaussian_integrable Δ (by fun_prop)]
  simpa only [one_mul] using rowTiltStep_weight_integrable hu.diff.continuous.measurable
    (rowBounded_exp_growth hu 1).1 (Δ:ℝ) x

lemma residual_weight_integral {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (Δ : ℝ≥0) (x : ℝ) :
    (∫ z, Real.exp (u (x+z)) ∂gaussianReal 0 Δ) = Real.exp (gaussianRowOperator 1 (Δ:ℝ) u x) := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  have hp := integral_exp_pos (residual_weight_integrable hu Δ x)
  rw [rowGaussian_integral Δ (by fun_prop)] at hp ⊢
  simp only [gaussianRowOperator,one_div,one_mul,ite_false,one_ne_zero,inv_one,gaussianHeat]
  rw [Real.exp_log hp]

lemma residual_score_integrable {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (Δ : ℝ≥0) (x : ℝ) :
    Integrable (fun z => deriv u (x+z)*Real.exp (u (x+z))) (gaussianReal 0 Δ) := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  apply ((residual_weight_integrable hu Δ x).const_mul L).mono' (by fun_prop)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hu.slope _) (Real.exp_pos _).le

lemma residual_score_integral {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (Δ : ℝ≥0) (x : ℝ) :
    (∫ z, deriv u (x+z)*Real.exp (u (x+z)) ∂gaussianReal 0 Δ) =
      deriv (gaussianRowOperator 1 (Δ:ℝ) u) x * Real.exp (gaussianRowOperator 1 (Δ:ℝ) u x) := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  have hd := ((rowBoundedOperator_derivatives hu 1 (Δ:ℝ)).1 x).deriv
  rw [hd,← residual_weight_integral hu Δ x]
  rw [rowGaussian_integral Δ (by fun_prop),rowGaussian_integral Δ (by fun_prop)]
  have hp := integral_exp_pos (rowTiltStep_weight_integrable hu.diff.continuous.measurable
    (rowBounded_exp_growth hu 1).1 (Δ:ℝ) x)
  simp only [one_mul] at hp
  simp only [rowTiltStep,one_mul]
  rw [div_mul_cancel₀ _ hp.ne']

lemma residual_exp_integrable_iff {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (Δ : ℝ≥0) :
    Integrable (fun z : S × ℝ => Real.exp (u (f z.1+z.2))) (μ.prod (gaussianReal 0 Δ)) ↔
      Integrable (fun x => Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x))) μ := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  have hm : Measurable (fun z : S × ℝ => Real.exp (u (f z.1+z.2))) :=
    Real.measurable_exp.comp (hum.comp ((hf.comp measurable_fst).add measurable_snd))
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  have he (x : S) : (∫ z, ‖Real.exp (u (f x+z))‖ ∂gaussianReal 0 Δ) =
      Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x)) := by
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact residual_weight_integral hu Δ (f x)
  simp only [he]
  exact and_iff_right (Eventually.of_forall (fun x => residual_weight_integrable hu Δ (f x)))

lemma residual_partition_eq {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (Δ : ℝ≥0) :
    (∫ z : S × ℝ, Real.exp (u (f z.1+z.2)) ∂μ.prod (gaussianReal 0 Δ)) =
      ∫ x, Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x)) ∂μ := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  by_cases hi : Integrable (fun x => Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x))) μ
  · rw [integral_prod _ ((residual_exp_integrable_iff μ f hf hu Δ).mpr hi)]
    exact integral_congr_ae (Eventually.of_forall (fun x => residual_weight_integral hu Δ (f x)))
  · rw [integral_undef hi,integral_undef ((residual_exp_integrable_iff μ f hf hu Δ).not.mpr hi)]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace MicroscopicJamming

lemma residual_pair_score_integral {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (Δ : ℝ≥0)
    (B : (Fin 2 → S) → ℝ) (hB : Measurable B) {K : ℝ} (hb : ∀ xs, |B xs| ≤ K)
    (hi : Integrable (fun x => Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x))) μ) :
    (∫ xs, B (fun i => (xs i).1) * ∏ i : Fin 2,
        (deriv u (f (xs i).1+(xs i).2) * Real.exp (u (f (xs i).1+(xs i).2)))
      ∂Measure.pi (fun _ : Fin 2 => μ.prod (gaussianReal 0 Δ))) =
    ∫ xs, B xs * ∏ i : Fin 2, (deriv (gaussianRowOperator 1 (Δ:ℝ) u) (f (xs i)) *
      Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f (xs i)))) ∂Measure.pi (fun _ : Fin 2 => μ) := by
  have hum : Measurable u := hu.diff.continuous.measurable
  have hud : Measurable (deriv u) := hu.diff_deriv.continuous.measurable
  let score := fun z : S × ℝ => deriv u (f z.1+z.2)*Real.exp (u (f z.1+z.2))
  have hs : Measurable score := by unfold score; fun_prop
  have hsi : Integrable score (μ.prod (gaussianReal 0 Δ)) := by
    apply (((residual_exp_integrable_iff μ f hf hu Δ).mpr hi).const_mul L).mono' hs.aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    simp only [score,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hu.slope _) (Real.exp_pos _).le
  let F := fun xs : Fin 2 → S × ℝ => B (fun i => (xs i).1) * ∏ i, score (xs i)
  have hF : Measurable F := by unfold F; fun_prop
  have hFi : Integrable F (Measure.pi (fun _ : Fin 2 => μ.prod (gaussianReal 0 Δ))) :=
    (Integrable.fintype_prod (fun _ : Fin 2 => hsi)).bdd_mul
      (hB.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun xs => by simpa only [Real.norm_eq_abs] using hb (fun i => (xs i).1)))
  let pair := fun z : (Fin 2 → S) × (Fin 2 → ℝ) => fun i => (z.1 i,z.2 i)
  have hp : Measurable pair := by unfold pair; fun_prop
  have he := pi_prod_pair_map (fun _ : Fin 2 => μ) (fun _ : Fin 2 => gaussianReal 0 Δ)
  change (∫ xs, F xs ∂Measure.pi (fun _ : Fin 2 => μ.prod (gaussianReal 0 Δ))) = _
  rw [← he,integral_map hp.aemeasurable hF.aestronglyMeasurable]
  have hIi : Integrable (fun z => F (pair z))
      ((Measure.pi (fun _ : Fin 2 => μ)).prod (Measure.pi (fun _ : Fin 2 => gaussianReal 0 Δ))) := by
    apply (integrable_map_measure hF.aestronglyMeasurable hp.aemeasurable).mp
    rwa [he]
  rw [integral_prod _ hIi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro xs
  change (∫ zs, B xs * ∏ i : Fin 2, (deriv u (f (xs i)+zs i)*Real.exp (u (f (xs i)+zs i)))
    ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 Δ)) = _
  rw [integral_const_mul,integral_fintype_prod_eq_prod (fun i : Fin 2 =>
    fun z : ℝ => deriv u (f (xs i)+z)*Real.exp (u (f (xs i)+z)))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact residual_score_integral hu Δ (f (xs i))

lemma residual_pair_normalized {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ) (hf : Measurable f)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H) (Δ : ℝ≥0)
    (B : (Fin 2 → S) → ℝ) (hB : Measurable B) {K : ℝ} (hb : ∀ xs, |B xs| ≤ K) :
    (∫ xs, (B (fun i => (xs i).1) *
        (deriv u (f (xs 0).1+(xs 0).2)*deriv u (f (xs 1).1+(xs 1).2))) *
        ∏ i : Fin 2, Real.exp (u (f (xs i).1+(xs i).2))
      ∂Measure.pi (fun _ : Fin 2 => μ.prod (gaussianReal 0 Δ))) /
      (∫ z : S × ℝ, Real.exp (u (f z.1+z.2)) ∂μ.prod (gaussianReal 0 Δ))^2 =
    (∫ xs, (B xs * (deriv (gaussianRowOperator 1 (Δ:ℝ) u) (f (xs 0)) *
        deriv (gaussianRowOperator 1 (Δ:ℝ) u) (f (xs 1)))) *
        ∏ i : Fin 2, Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f (xs i)))
      ∂Measure.pi (fun _ : Fin 2 => μ)) /
      (∫ x, Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x)) ∂μ)^2 := by
  rw [residual_partition_eq μ f hf hu Δ]
  by_cases hi : Integrable (fun x => Real.exp (gaussianRowOperator 1 (Δ:ℝ) u (f x))) μ
  · congr 1
    convert residual_pair_score_integral μ f hf hu Δ B hB hb hi using 1 <;>
      congr 1 <;> funext xs <;> simp only [Fin.prod_univ_two] <;> ring
  · simp [integral_undef hi]

lemma rowResidualPair_pointwise {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (ms : List ℝ) (Δ : ℝ≥0) (B : ℕ → ℝ) (ω : RowReplicaEnvironment ms.length) :
    replicaNum (rowReplicaKernel ms Δ) (rowFullPotential ms u) (rowFullPair ms u B) ω /
      (replicaZ (rowReplicaKernel ms Δ) (rowFullPotential ms u) ω)^2 =
    replicaNum (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms (gaussianRowOperator 1 Δ u))
        (rowCoordinatePair ms (gaussianRowOperator 1 Δ u) B) ω /
      (replicaZ (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms (gaussianRowOperator 1 Δ u)) ω)^2 := by
  let := cascadeLeafLaw_probability ms ω.1
  apply residual_pair_normalized (cascadeLeafLaw ms ω.1) (rootPathField ms.length ω.2)
    (measurable_of_countable _) hu Δ
    (fun xs => B (cascadeSharedEdges ms.length (xs 0) (xs 1))) (measurable_of_countable _)
  intro xs
  exact Finset.single_le_sum (fun i _ => abs_nonneg (B i))
    (show cascadeSharedEdges ms.length (xs 0) (xs 1) ∈ Finset.range (ms.length+1) from
      Finset.mem_range.mpr (Nat.lt_succ_of_le (cascadeSharedEdges_le _ _ _)))

theorem rowResidualPair : RowResidualPairStatement := by
  intro u L H hu hL hH hb ms hord hms d p₀ Δ B
  have hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),
    hu'.differentiable (by norm_num),hL,hH,fun y => (hb y).1,fun y => (hb y).2⟩
  calc
    _ = ∫ ω, replicaNum (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms (gaussianRowOperator 1 Δ u))
        (rowCoordinatePair ms (gaussianRowOperator 1 Δ u) B) ω /
      (replicaZ (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms (gaussianRowOperator 1 Δ u)) ω)^2
      ∂rowReplicaEnvironmentLaw ms d p₀ :=
      integral_congr_ae (Eventually.of_forall (rowResidualPair_pointwise ht ms Δ B))
    _ = _ := rowDirectingPair u L H hu hL hH hb ms hord hms d p₀ Δ B
end MicroscopicJamming

 
open scoped MatrixOrder
 
open scoped NNReal

namespace MicroscopicJamming
 

def RowRefinementCovarianceStatement : Prop :=
  ∀ ms ns : List ℝ, ms.Pairwise (· < ·) → ns.Pairwise (· < ·) →
    (∀ m ∈ ms, 0 < m ∧ m < 1) → (∀ m ∈ ns, 0 < m ∧ m < 1) →
  ∀ (d e : ℕ → ℝ≥0) (p₀ : ℝ≥0),
    (rowGaussianBlocks ms d).filter (fun r => r.2 != 0) =
      (rowGaussianBlocks ns e).filter (fun r => r.2 != 0) →
    (∀ s, (rowCascadeProfile ms d p₀).val s = (rowCascadeProfile ns e p₀).val s) ∧
    ∀ (r : ℕ) (Q : ℝ),
      rowFullRankCovariance r Q (rowCascadeProfile ms d p₀) =
        rowFullRankCovariance r Q (rowCascadeProfile ns e p₀)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal

namespace MicroscopicJamming
lemma rowCascadeProfile_sum (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (s : ℝ) :
    (rowCascadeProfile ms d p₀).val s = (p₀:ℝ) +
      ((rowGaussianBlocks ms d).map (fun r => if r.1 ≤ s then r.2 else 0)).sum := by
  suffices hs : (∑ a : Fin ms.length,
      if a.val+1 ≤ rpcStepLevel ms s then (d a:ℝ) else 0) =
      ((rowGaussianBlocks ms d).map (fun r => if r.1 ≤ s then r.2 else 0)).sum by
    exact congrArg ((p₀:ℝ)+·) hs
  induction ms generalizing d with
  | nil => simp [rpcStepLevel,rowGaussianBlocks]
  | cons m ms ih =>
    have ht := (List.pairwise_cons.mp hms).2
    by_cases hm : m ≤ s
    · have he : rpcStepLevel (m::ms) s = rpcStepLevel ms s + 1 := by
        simp [rpcStepLevel,hm]
      simp only [List.length_cons,Fin.sum_univ_succ,Fin.val_zero,zero_add,
        Fin.val_succ,he,rowGaussianBlocks,List.map_cons,List.sum_cons,ite_eq_left hm]
      simp only [Nat.succ_le_succ_iff,Nat.zero_le,ite_true]
      rw [ih ht (fun j => d (j+1))]
    · have hz : rpcStepLevel ms s = 0 := by
        have he : ms.filter (fun a => decide (a ≤ s)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro a ha
          have hn : ¬ a ≤ s := not_le.mpr ((lt_of_not_ge hm).trans
            ((List.pairwise_cons.mp hms).1 a ha))
          simp [hn]
        simp [rpcStepLevel,he]
      have he : rpcStepLevel (m::ms) s = 0 := by
        simpa [rpcStepLevel,List.filter_cons,hm] using hz
      have hij := ih ht (fun j => d (j+1))
      simp only [hz] at hij
      simp [he,rowGaussianBlocks,hm,←hij]

lemma rowIncrementSum_filter (rs : List (ℝ × ℝ)) (s : ℝ) :
    ((rs.filter (fun r => r.2 != 0)).map (fun r => if r.1 ≤ s then r.2 else 0)).sum =
      (rs.map (fun r => if r.1 ≤ s then r.2 else 0)).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases hz : r.2=0
    · simp [hz,ih]
    · simp [hz,ih]

theorem rowRefinementCovariance : RowRefinementCovarianceStatement := by
  intro ms ns hms hns hm hn d e p₀ he
  have hp (s : ℝ) : (rowCascadeProfile ms d p₀).val s =
      (rowCascadeProfile ns e p₀).val s := by
    rw [rowCascadeProfile_sum ms hms,rowCascadeProfile_sum ns hns,
      ←rowIncrementSum_filter (rowGaussianBlocks ms d) s,
      ←rowIncrementSum_filter (rowGaussianBlocks ns e) s,he]
  refine ⟨hp,?_⟩
  intro r Q
  funext U i j
  simp only [rowFullRankCovariance,rowClosedProfile,hp]
end MicroscopicJamming

end

end OAI
