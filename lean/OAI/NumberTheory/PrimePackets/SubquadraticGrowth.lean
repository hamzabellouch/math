import Mathlib
import OAI.NumberTheory.PrimePackets.ThetaReflection

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
namespace PrimeDegreePackets.AnalyticGrowth

lemma tendsto_affine_div_sq (a b : ℝ) :
    Tendsto (fun R : ℝ => (a*R+b)/R^2) atTop (𝓝 0) := by
  have H1 : Tendsto (fun R : ℝ => a/R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have H2 : Tendsto (fun R : ℝ => b/R^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  apply (show Tendsto (fun R : ℝ => a/R+b/R^2) atTop (𝓝 0) by simpa using H1.add H2).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  field_simp

lemma hasSubquadraticGrowth_id : HasSubquadraticGrowth (fun z => z) := by
  apply HasSubquadraticGrowth.of_bound (by simpa using tendsto_affine_div_sq 1 0)
  apply Filter.Eventually.of_forall
  intro R z hz
  exact hz.trans (by linarith [Real.add_one_le_exp R])

lemma hasSubquadraticGrowth_exp_affine (a b : ℂ) :
    HasSubquadraticGrowth (fun z => Complex.exp (a*z+b)) := by
  apply HasSubquadraticGrowth.of_bound (tendsto_affine_div_sq ‖a‖ ‖b‖)
  apply Filter.Eventually.of_forall
  intro R z hz
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖a*z+b‖ := Complex.re_le_norm _
    _ ≤ ‖a*z‖+‖b‖ := norm_add_le _ _
    _ ≤ ‖a‖*R+‖b‖ := by rw [norm_mul]; gcongr

lemma hasSubquadraticGrowth_const_cpow {a : ℝ} (ha : 0 < a) :
    HasSubquadraticGrowth (fun z : ℂ => (a:ℂ)^z) := by
  simpa only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), add_zero]
    using hasSubquadraticGrowth_exp_affine (Complex.log (a:ℂ)) 0

lemma HasSubquadraticGrowth.congr {f g : ℂ → ℂ} (hf : HasSubquadraticGrowth f)
    (h : ∀ z, f z = g z) : HasSubquadraticGrowth g := by
  have : f = g := funext h
  rwa [← this]

lemma HasSubquadraticGrowth.pow {f : ℂ → ℂ} (hf : HasSubquadraticGrowth f) (n : ℕ) :
    HasSubquadraticGrowth (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using hasSubquadraticGrowth_const 1
  | succ n IH => simpa only [pow_succ] using IH.mul hf

end PrimeDegreePackets.AnalyticGrowth

open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
namespace PrimeDegreePackets.ThetaConstruction
open AnalyticGrowth
variable {d : Type*} [Fintype d]

lemma averagedNormalizedThetaTail_mellin_hasSubquadraticGrowth
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R) :
    HasSubquadraticGrowth (mellin (averagedNormalizedThetaTail μ B)) := by
  obtain ⟨a,C,ha,hC,_,hdecay⟩ := averagedNormalizedThetaTail_bounds μ B R hR hbound
  exact mellin_hasSubquadraticGrowth ha hC
    (fun t ht => averagedNormalizedThetaTail_eq_zero μ B ht) hdecay

theorem averagedThetaMellinXi_hasSubquadraticGrowth
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖(B x).symm.toContinuousLinearMap‖ ≤ R)
    (hdual : ∀ x, ‖(adjointEquiv (B x).symm).symm.toContinuousLinearMap‖ ≤ T)
    (hB : StronglyMeasurable (fun p : α × ℝ => normalizedThetaTail (B p.1) p.2))
    (hD : StronglyMeasurable (fun p : α × ℝ =>
      normalizedThetaTail (adjointEquiv (B p.1).symm) p.2))
    (c : ℂ) (hc : ∀ x, ((|(LinearMap.det (B x).toLinearMap)⁻¹|:ℝ):ℂ) = c) :
    HasSubquadraticGrowth (fun s => ∫ x, thetaMellinXi (B x) s ∂μ) := by
  let a : ℂ := (Fintype.card d:ℂ)/2
  let P := mellin (averagedNormalizedThetaTail μ B)
  let Q := mellin (averagedNormalizedThetaTail μ (fun x => adjointEquiv (B x).symm))
  have HP : HasSubquadraticGrowth P := averagedNormalizedThetaTail_mellin_hasSubquadraticGrowth μ B R hR hbound
  have HQ : HasSubquadraticGrowth Q := averagedNormalizedThetaTail_mellin_hasSubquadraticGrowth μ _ T hT hdual
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
  have Hq : HasSubquadraticGrowth (fun s => Q (a-s)) :=
    (HQ.comp_affine (-1) a).congr (fun s => by congr 1; ring)
  have Hid := hasSubquadraticGrowth_id
  have Hsa := Hid.sub (hasSubquadraticGrowth_const a)
  exact ((Hid.mul Hsa).mul (HP.add ((hasSubquadraticGrowth_const c).mul Hq))).add
    ((hasSubquadraticGrowth_const (μ.real Set.univ:ℂ)).mul
      (((hasSubquadraticGrowth_const c).mul Hid).sub Hsa))

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction AnalyticGrowth

theorem arithmeticFlowThetaXi_boundedAverage_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    {S : Set (LogCoordinates d)} (hS : MeasurableSet S) (hbd : Bornology.IsBounded S) :
    HasSubquadraticGrowth (fun s => ∫ u in S,
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
  have H := averagedThetaMellinXi_hasSubquadraticGrowth μ F R T hR hT HB HD HM HN _ HC
  have HE : (fun s => ∫ x, thetaMellinXi (F x) s ∂μ) =
      fun s => ∫ u in S, thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s := by
    funext s
    exact integral_subtype_comap hS (fun u => thetaMellinXi (logScaledLattice B (restoredLogCoordinates u)) s)
  rw [HE] at H
  exact H

end PrimeDegreePackets


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction AnalyticGrowth

lemma idealThetaXi_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    HasSubquadraticGrowth (idealThetaXi σ hn I) := by
  have H := arithmeticFlowThetaXi_boundedAverage_hasSubquadraticGrowth
    (fractionalIdealFullLattice hn I) σ hn
    (S := orderedThetaLogDomain σ) (ZSpan.fundamentalDomain_measurableSet _) (ZSpan.fundamentalDomain_isBounded _)
  exact (H.comp_affine (((d+1 : ℕ) : ℂ)/2) 0).congr (fun s => by
    unfold idealThetaXi
    congr 1
    ring_nf)

lemma classThetaXi_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    HasSubquadraticGrowth (classThetaXi σ hn) := by
  classical
  unfold classThetaXi
  apply HasSubquadraticGrowth.finset_sum
  intro c _
  exact (hasSubquadraticGrowth_const_cpow (fractionalIdeal_absNorm_pos _)).mul
    (idealThetaXi_hasSubquadraticGrowth σ hn _)

 

theorem completedThetaXi_hasSubquadraticGrowth {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    HasSubquadraticGrowth (completedThetaXi σ hn) := by
  unfold completedThetaXi
  have H := hasSubquadraticGrowth_exp_affine
    ((Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) 0
  have HE : HasSubquadraticGrowth (fun s : ℂ =>
      Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2)) :=
    H.congr (fun s => by congr 1; ring)
  exact ((hasSubquadraticGrowth_const _).mul HE).mul
    (classThetaXi_hasSubquadraticGrowth σ hn)

end PrimeDegreePackets.HeckeMellin

open Complex Set Filter Module
namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

 

theorem dedekindXi_hasSum_realZeroPole {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {s : ℝ} (hs : 1 < s) :
    HasSum (realZeroPole (completedThetaXi σ hn) s)
      (1/s + 1/(s-1) + Real.log |(NumberField.discr K : ℝ)|/2 +
        deriv (realDedekindZeta K) s / realDedekindZeta K s +
          archimedeanZetaTerm (finrank ℚ K) s) := by
  have H := hasSum_realZeroPole (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero σ hn hodd)
    (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation σ hn hodd z).symm)
    (fun z hz => (dedekindXiZeros_re_mem_Icc σ hn hodd hz).2) hs
  rwa [completedThetaXi_logDeriv σ hn hodd (by simpa using hs),
    totallyRealCompletedXi_logDeriv_re K hs] at H

 

lemma dedekindXi_realZeroPole_nonneg {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {s : ℝ} (hs : 1 < s) (ρ : ℂ) :
    0 ≤ realZeroPole (completedThetaXi σ hn) s ρ :=
  realZeroPole_nonneg (completedThetaXi_entire σ hn) (dedekindXiZeros_ne_zero σ hn hodd)
    (fun _ hz => (dedekindXiZeros_re_mem_Icc σ hn hodd hz).2) hs ρ

end PrimeDegreePackets.HeckeMellin

open Complex
namespace PrimeDegreePackets.AnalyticGrowth

lemma near_one_kernel_lower {a b : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 5/4)
    (hb : |b| ≤ 1/4) : (10/13:ℝ) ≤ a/(a^2+b^2) := by
  have hb' := abs_le.mp hb
  have hbs : b^2 ≤ 1/16 := by nlinarith
  have hd : 0 < a^2+b^2 := by nlinarith [sq_nonneg b]
  apply (le_div_iff₀ hd).mpr
  have Hp : 0 ≤ (5/4-a)*(10*a-1/2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma real_inverse_pole_scaled {L h : ℝ} (hL : L ≠ 0) (ρ : ℂ) :
    (1/(((1+h:ℝ):ℂ)-ρ)).re =
      L*((L*(1-ρ.re)+L*h)/((L*(1-ρ.re)+L*h)^2+(L*ρ.im)^2)) := by
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re,
    Complex.normSq_apply, Complex.sub_im, Complex.ofReal_im, zero_sub]
  have HE : L*(1-ρ.re)+L*h = L*(1+h-ρ.re) := by ring
  rw [HE]
  simp only [mul_pow, neg_mul_neg]
  rw [← mul_add, ← mul_div_assoc, ← mul_assoc, ← pow_two]
  rw [show L*L = L^2 by ring]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hL)]
  congr 1; ring

 

lemma near_one_complex_pole_lower {L : ℝ} (hL : 0 < L) {ρ : ℂ}
    (hβ : ρ.re ≤ 1) (hβ' : 1-1/(4*L) ≤ ρ.re) (hγ : |ρ.im| ≤ 1/(4*L)) :
    (10/13)*L ≤ (1/(((1+1/L:ℝ):ℂ)-ρ)).re := by
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  have hX' : L*(1-ρ.re) ≤ 1/4 := by
    have H := mul_le_mul_of_nonneg_left (show 1-ρ.re ≤ 1/(4*L) by linarith) hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have hY : |L*ρ.im| ≤ 1/4 := by
    rw [abs_mul, abs_of_pos hL]
    have H := mul_le_mul_of_nonneg_left hγ hL.le
    have HE : L*(1/(4*L)) = (1/4:ℝ) := by field_simp
    rwa [HE] at H
  have H := near_one_kernel_lower (a := L*(1-ρ.re)+1) (by linarith) (by linarith) hY
  rw [real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left H hL.le

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Filter
namespace PrimeDegreePackets.AnalyticGrowth

 

def InNearOneBox (L : ℝ) (ρ : ℂ) : Prop :=
  1-1/(4*L) ≤ ρ.re ∧ |ρ.im| ≤ 1/(4*L)

lemma nearOneBox_multiplicity_sum_le_one {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    (t : Finset ℂ) (ht : ∀ ρ ∈ t, f ρ = 0 ∧ InNearOneBox L ρ) :
    ∑ ρ ∈ t, zeroMultiplicity f ρ ≤ 1 := by
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hL; linarith
  have HS := hasSum_realZeroPole hf h0 hg hfe hstrip hs
  have Hlower : (10/13)*L*(∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ)) ≤
      ∑ ρ ∈ t, realZeroPole f (1+1/L) ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have H := near_one_complex_pole_lower hL (hstrip ρ (ht ρ hρ).1)
      (ht ρ hρ).2.1 (ht ρ hρ).2.2
    simpa only [realZeroPole, mul_comm] using mul_le_mul_of_nonneg_left H
      (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  have Hupper := (HS.summable.sum_le_tsum t
    (fun ρ _ => realZeroPole_nonneg hf h0 hstrip hs ρ)).trans_eq HS.tsum_eq
  have Htotal := Hlower.trans (Hupper.trans hbound)
  by_contra h
  have Htwo : (2:ℤ) ≤ ∑ ρ ∈ t, zeroMultiplicity f ρ := by omega
  have Htwo' : (2:ℝ) ≤ ∑ ρ ∈ t, (zeroMultiplicity f ρ : ℝ) := by exact_mod_cast Htwo
  have HH := mul_le_mul_of_nonneg_left Htwo' (show 0 ≤ (10/13)*L by positivity)
  nlinarith

 

theorem nearOneBox_real_simple_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (hg : HasSubquadraticGrowth f)
    (hfe : ∀ z, f (1-z) = f z) (hconj : ∀ z, f (conj z) = conj (f z))
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L A : ℝ} (hL : 0 < L) (hA : 26*A < L)
    (hbound : (logDeriv f (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+A)
    {ρ : ℂ} (hρ : f ρ = 0) (hbox : InNearOneBox L ρ) :
    zeroMultiplicity f ρ = 1 ∧ ρ.im = 0 ∧
      ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
  classical
  have HP {τ : ℂ} (hτ : f τ = 0) : 1 ≤ zeroMultiplicity f τ := by
    have H := zeroMultiplicity_nonneg hf τ
    have H' := (zeroMultiplicity_ne_zero_iff hf h0 τ).mpr hτ
    omega
  have Huniq : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ := by
    intro τ hτ hτbox
    by_contra hne
    have H := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
      {τ,ρ} (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ⟨hτ,hτbox⟩
        · exact ⟨hρ,hbox⟩)
    simp only [Finset.sum_pair hne] at H
    have Hτ := HP hτ
    have Hρ := HP hρ
    omega
  have Hsimple := nearOneBox_multiplicity_sum_le_one hf h0 hg hfe hstrip hL hA hbound
    {ρ} (by intro z hz; have H := Finset.mem_singleton.mp hz; subst z; exact ⟨hρ,hbox⟩)
  have HS : zeroMultiplicity f ρ = 1 := by
    simp only [Finset.sum_singleton] at Hsimple
    exact le_antisymm Hsimple (HP hρ)
  have Hc := Huniq (conj ρ) (by rw [hconj, hρ]; simp) (by
    simpa only [InNearOneBox, Complex.conj_re, Complex.conj_im, abs_neg] using hbox)
  have HI := congrArg Complex.im Hc
  simp only [Complex.conj_im] at HI
  exact ⟨HS, by linarith, Huniq⟩

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology NumberField ComplexConjugate
namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

lemma completedThetaXi_logDeriv_base_le {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {B L : ℝ}
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL1 : 1 ≤ L)
    (hB : ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm (d+1) s| ≤ B) :
    (logDeriv (completedThetaXi σ hn) (((1+1/L:ℝ)):ℂ)).re ≤ (3/2)*L+B+1 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hs : 1 < 1+1/L := by have H := one_div_pos.mpr hLp; linarith
  have hsu : 1+1/L ≤ 2 := by
    have H := (div_le_one hLp).mpr hL1
    linarith
  rw [completedThetaXi_logDeriv σ hn hodd (by simpa using hs),
    totallyRealCompletedXi_logDeriv_re K hs, hn, ← hL]
  have HG := (abs_le.mp (hB (1+1/L) ⟨hs.le,hsu⟩)).2
  have HD : deriv (realDedekindZeta K) (1+1/L) / realDedekindZeta K (1+1/L) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (realDedekindZeta_deriv_nonpos K hs)
      (realDedekindZeta_pos K hs).le
  have Hr : 1/(1+1/L) ≤ 1 := (div_le_one (by linarith)).mpr hs.le
  have HE : 1/(1+1/L-1) = L := by field_simp; ring
  rw [HE]
  linarith

 

theorem dedekind_near_one_zero_real_simple_unique (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      ∀ (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
        (_hodd : Odd (finrank ℚ K)),
      C < Real.log |(NumberField.discr K : ℝ)| →
      ∀ ρ, ρ ∈ dedekindXiZeros σ hn →
        InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ →
        zeroMultiplicity (completedThetaXi σ hn) ρ = 1 ∧ ρ.im = 0 ∧
          ∀ τ, τ ∈ dedekindXiZeros σ hn →
            InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) τ → τ = ρ := by
  obtain ⟨B,hB,harch⟩ := archimedeanZetaTerm_bounded (d+1)
  refine ⟨max 1 (26*(B+1)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro K _ _ _ σ hn hodd hL ρ hρ hρbox
  have hL1 : 1 < Real.log |(NumberField.discr K : ℝ)| :=
    lt_of_le_of_lt (le_max_left _ _) hL
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := by linarith
  have Hbase := completedThetaXi_logDeriv_base_le σ hn hodd rfl hL1.le harch
  apply nearOneBox_real_simple_unique (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero σ hn hodd) (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation σ hn hodd z).symm)
    (completedThetaXi_conj σ hn hodd)
    (fun z hz => (dedekindXiZeros_re_mem_Icc σ hn hodd hz).2)
    hLp (lt_of_le_of_lt (le_max_right _ _) hL) _ hρ hρbox
  simpa only [add_assoc] using Hbase

end PrimeDegreePackets.HeckeMellin
end
end

end OAI
