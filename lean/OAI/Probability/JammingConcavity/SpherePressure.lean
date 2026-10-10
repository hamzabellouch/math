import Mathlib
import OAI.Probability.JammingConcavity.DeletionMeasurePreservingSelectRows

namespace OAI

/-! Sphere Pressure. -/

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
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def unitSphereLaw (n : ℕ) : Measure (Metric.sphere (0 : SpinSpace n) 1) :=
  let σ := (volume : Measure (SpinSpace n)).toSphere
  (σ Set.univ)⁻¹ • σ

instance unitSphereLaw_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (unitSphereLaw n) := by
  have : NeZero ((volume : Measure (SpinSpace n)).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  infer_instance

lemma unitSphereLaw_cap {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (y : Metric.sphere (0 : SpinSpace n) 1) :
    (δ/4)^n ≤ (unitSphereLaw n).real (Metric.ball y δ) := by
  let : NeZero n := ⟨by omega⟩
  let σ := (volume : Measure (SpinSpace n)).toSphere
  have hball : 0 < (volume : Measure (SpinSpace n)).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos _ _ zero_lt_one)) measure_ball_lt_top.ne
  have htot : σ.real Set.univ = (n:ℝ)*(volume : Measure (SpinSpace n)).real (Metric.ball 0 1) := by
    simp [σ, SpinSpace]
  have htotpos : 0 < σ.real Set.univ := by rw [htot]; positivity
  have hraw := Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    (volume : Measure (SpinSpace n)) hδ y
  have hc : (Measure.toSphereBallBound n δ : ℝ) = (n:ℝ)*(δ/4)^n := by
    simp [Measure.toSphereBallBound, hn.ne', hδ, min_eq_left hδ2, Real.toNNReal_of_nonneg hδ.le]
  simp only [finrank_euclideanSpace_fin, SpinSpace] at hraw
  rw [hc] at hraw
  change (δ/4)^n ≤ ((σ Set.univ)⁻¹ • σ).real (Metric.ball y δ)
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
  change (δ/4)^n ≤ (σ.real Set.univ)⁻¹ * σ.real (Metric.ball y δ)
  rw [← div_eq_inv_mul, le_div_iff₀ htotpos, htot]
  nlinarith only [hraw]

lemma surfaceLaw_as_map (n : ℕ) : surfaceLaw n =
    (unitSphereLaw n).map (fun y : Metric.sphere (0 : SpinSpace n) 1 =>
      Real.sqrt n • (y : SpinSpace n)) := rfl

lemma partition_rescale {α β : ℝ} {n : ℕ} (hn : 0 < n) (A : PatternMatrix α n) :
    (∫ x, Real.exp (-β*energy A x) ∂surfaceLaw n) =
      ∫ y : Metric.sphere (0 : SpinSpace n) 1,
        Real.exp (-β*unitEnergy A (y : SpinSpace n)) ∂unitSphereLaw n := by
  rw [surfaceLaw_as_map, integral_map (by fun_prop) (by unfold energy field potential; fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [energy_rescale hn]

 
def unitResidual {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => max (-1 - (matrixOperator A y) j) 0)

lemma unitEnergy_eq_half_norm_sq {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : unitEnergy A y = (1/2:ℝ)*‖unitResidual A y‖^2 := by
  simp only [unitEnergy, potential, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  rfl

lemma unitResidual_contract {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) :
    ‖unitResidual A y - unitResidual A z‖ ≤ ‖matrixOperator A‖ * ‖y-z‖ := by
  have hv : ‖unitResidual A y - unitResidual A z‖ ≤ ‖matrixOperator A (y-z)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    have h := abs_max_sub_max_le_abs (-1-(matrixOperator A y) j)
      (-1-(matrixOperator A z) j) 0
    have he : -1-(matrixOperator A y) j - (-1-(matrixOperator A z) j) =
        -((matrixOperator A y) j - (matrixOperator A z) j) := by ring
    rw [he, abs_neg] at h
    have hs := sq_le_sq₀ (abs_nonneg _) (abs_nonneg _) |>.mpr h
    simpa [unitResidual, sq_abs] using hs
  exact hv.trans ((matrixOperator A).le_opNorm (y-z))

lemma unitResidual_sq_le {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) :
    ‖unitResidual A y‖^2 ≤ 2*(m:ℝ)+2*‖matrixOperator A‖^2 := by
  have hs : ‖unitResidual A y‖^2 ≤ 2*(m:ℝ)+2*‖matrixOperator A y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ j : Fin m, (2+2*((matrixOperator A y) j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        change (max (-1-(matrixOperator A y) j) 0)^2 ≤ _
        rcases le_total (-1-(matrixOperator A y) j) 0 with h | h
        · rw [max_eq_right h]; nlinarith [sq_nonneg ((matrixOperator A y) j)]
        · rw [max_eq_left h]; nlinarith [sq_nonneg ((matrixOperator A y) j-1)]
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]; ring
  have hop := (matrixOperator A).le_opNorm y
  rw [hy, mul_one] at hop
  have hsop := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hop
  linarith

lemma unitEnergy_sphere_lipschitz {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {y z : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    |unitEnergy A y - unitEnergy A z| ≤
      ((m:ℝ)+2*‖matrixOperator A‖^2)*‖y-z‖ := by
  let H := Real.sqrt (2*(m:ℝ)+2*‖matrixOperator A‖^2)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H^2 = 2*(m:ℝ)+2*‖matrixOperator A‖^2 := Real.sq_sqrt (by positivity)
  have ha : ‖unitResidual A y‖ ≤ H := by
    apply (sq_le_sq₀ (norm_nonneg _) hH).mp
    rw [hHsq]
    exact unitResidual_sq_le A hy
  have hb : ‖unitResidual A z‖ ≤ H := by
    apply (sq_le_sq₀ (norm_nonneg _) hH).mp
    rw [hHsq]
    exact unitResidual_sq_le A hz
  have hc : H*‖matrixOperator A‖ ≤ (m:ℝ)+2*‖matrixOperator A‖^2 := by
    nlinarith [sq_nonneg (H-‖matrixOperator A‖), sq_nonneg ‖matrixOperator A‖]
  have hd := (abs_norm_sub_norm_le (unitResidual A y) (unitResidual A z)).trans
    (unitResidual_contract A y z)
  rw [unitEnergy_eq_half_norm_sq, unitEnergy_eq_half_norm_sq]
  calc
    _ = (‖unitResidual A y‖+‖unitResidual A z‖)/2 *
        |‖unitResidual A y‖-‖unitResidual A z‖| := by
      rw [← abs_of_nonneg (show 0 ≤ (‖unitResidual A y‖+‖unitResidual A z‖)/2 by positivity),
        ← abs_mul]
      congr 1; ring
    _ ≤ H * (‖matrixOperator A‖*‖y-z‖) :=
      mul_le_mul (by linarith) hd (abs_nonneg _) hH
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

def spherePartition {m n : ℕ} (A : Fin m → Fin n → ℝ) (β : ℝ) : ℝ :=
  ∫ y : Metric.sphere (0 : SpinSpace n) 1,
    Real.exp (-β*unitEnergy A (y : SpinSpace n)) ∂unitSphereLaw n

lemma continuous_sphere_integrand {m n : ℕ} (β : ℝ) :
    Continuous (fun p : (Fin m → Fin n → ℝ) × Metric.sphere (0 : SpinSpace n) 1 =>
      Real.exp (-β*unitEnergy p.1 (p.2 : SpinSpace n))) := by
  exact (continuous_const.mul (continuous_unitEnergy.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).rexp

lemma integrable_sphere_integrand {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Integrable (fun y : Metric.sphere (0 : SpinSpace n) 1 =>
      Real.exp (-β*unitEnergy A (y : SpinSpace n))) (unitSphereLaw n) := by
  let : NeZero n := ⟨by omega⟩
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_sphere_integrand β).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  filter_upwards [] with y
  change ‖Real.exp (-β*unitEnergy A (y : SpinSpace n))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [unitEnergy_nonneg A (y : SpinSpace n)])

lemma spherePartition_bounds {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-β*((m:ℝ)+‖matrixOperator A‖^2)) ≤ spherePartition A β ∧
      spherePartition A β ≤ Real.exp (-β*unitGround A) := by
  let : NeZero n := ⟨by omega⟩
  have hi := integrable_sphere_integrand hn A hβ
  constructor
  · calc
      _ = ∫ _ : Metric.sphere (0 : SpinSpace n) 1,
          Real.exp (-β*((m:ℝ)+‖matrixOperator A‖^2)) ∂unitSphereLaw n := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) hi
        intro y
        apply Real.exp_le_exp.mpr
        have hy : ‖(y : SpinSpace n)‖ = 1 := by simp
        have he := unitResidual_sq_le A hy
        rw [unitEnergy_eq_half_norm_sq]
        nlinarith [mul_nonneg hβ (sub_nonneg.mpr he)]
  · calc
      _ ≤ ∫ _ : Metric.sphere (0 : SpinSpace n) 1,
          Real.exp (-β*unitGround A) ∂unitSphereLaw n := by
        apply integral_mono hi (integrable_const _)
        intro y
        apply Real.exp_le_exp.mpr
        have hg := unitGround_le hn A (y := (y : SpinSpace n)) (by simp)
        nlinarith [mul_nonneg hβ (sub_nonneg.mpr hg)]
      _ = _ := by simp

lemma spherePartition_pos {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {β : ℝ} (hβ : 0 ≤ β) : 0 < spherePartition A β :=
  (Real.exp_pos _).trans_le (spherePartition_bounds hn A hβ).1

lemma spherePartition_cap_lower {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    (δ/4)^n * Real.exp (-β*(unitGround A + ((m:ℝ)+2*‖matrixOperator A‖^2)*δ)) ≤
      spherePartition A β := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨y, hy, heq, _⟩ := unitGround_attained hn A
  let y' : Metric.sphere (0 : SpinSpace n) 1 := ⟨y, by simpa using hy⟩
  let c := Real.exp (-β*(unitGround A + ((m:ℝ)+2*‖matrixOperator A‖^2)*δ))
  have hi := integrable_sphere_integrand hn A hβ
  calc
    _ ≤ (unitSphereLaw n).real (Metric.ball y' δ)*c :=
      mul_le_mul_of_nonneg_right (unitSphereLaw_cap hn hδ hδ2 y') (Real.exp_nonneg _)
    _ = ∫ _ in Metric.ball y' δ, c ∂unitSphereLaw n := by simp
    _ ≤ ∫ z in Metric.ball y' δ,
        Real.exp (-β*unitEnergy A (z : SpinSpace n)) ∂unitSphereLaw n := by
      apply setIntegral_mono_on (integrable_const _) hi.integrableOn measurableSet_ball
      intro z hz
      apply Real.exp_le_exp.mpr
      have hz' : ‖(z : SpinSpace n)‖ = 1 := by simp
      have hLip := (le_abs_self (unitEnergy A (z : SpinSpace n)-unitEnergy A y)).trans
        (unitEnergy_sphere_lipschitz A hz' hy)
      have hd : ‖(z : SpinSpace n)-y‖ ≤ δ := by
        have hzd : dist (z : SpinSpace n) y < δ := hz
        exact (by simpa [dist_eq_norm] using hzd.le)
      have hK : 0 ≤ (m:ℝ)+2*‖matrixOperator A‖^2 := by positivity
      have hE : unitEnergy A (z : SpinSpace n) ≤ unitGround A+((m:ℝ)+2*‖matrixOperator A‖^2)*δ := by
        rw [heq]
        have hh := mul_le_mul_of_nonneg_left hd hK
        linarith
      nlinarith [mul_nonneg hβ (sub_nonneg.mpr hE)]
    _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall fun _ => Real.exp_nonneg _)

lemma log_spherePartition_bounds {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    -β*unitGround A - β*((m:ℝ)+2*‖matrixOperator A‖^2)*δ - (n:ℝ)*Real.log (4/δ) ≤
        Real.log (spherePartition A β) ∧
      Real.log (spherePartition A β) ≤ -β*unitGround A := by
  have hp := spherePartition_pos hn A hβ
  constructor
  · have hc := spherePartition_cap_lower hn A hβ hδ hδ2
    have hpos : 0 < (δ/4)^n * Real.exp (-β*(unitGround A+((m:ℝ)+2*‖matrixOperator A‖^2)*δ)) := by positivity
    have hl := Real.log_le_log hpos hc
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hl
    have he : Real.log (δ/4) = -Real.log (4/δ) := by
      rw [Real.log_div hδ.ne' (by norm_num), Real.log_div (by norm_num) hδ.ne']
      ring
    rw [he] at hl
    nlinarith
  · have hl := Real.log_le_log hp (spherePartition_bounds hn A hβ).2
    rwa [Real.log_exp] at hl

end MicroscopicJamming

 

 

open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

abbrev UnitSpin (N : ℕ) := Metric.sphere (0 : SpinSpace N) 1
abbrev PerturbationIndex (N : ℕ) := Σ p : Fin N, (Fin (p.val+1) → Fin N)
def perturbationLaw (N : ℕ) : Measure (PerturbationIndex N → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

def coefficientLaw : Measure ℝ := volume.restrict (Set.Icc 1 2)
instance coefficientLaw_probability : IsProbabilityMeasure coefficientLaw := by
  constructor
  norm_num [coefficientLaw]
def coefficientProductLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ => coefficientLaw

def tensorField {N p : ℕ} (g : (Fin p → Fin N) → ℝ) (y : UnitSpin N) : ℝ :=
  ∑ i, g i * ∏ j, (y : SpinSpace N) (i j)
def perturbation {N : ℕ} (ρ : ℝ) (c : ℕ → ℝ) (g : PerturbationIndex N → ℝ)
    (y : UnitSpin N) : ℝ :=
  (N:ℝ)^ρ * ∑ p : Fin N, (2:ℝ)^(-(p.val+1:ℝ)) * c (p.val+1) *
    tensorField (fun i => g ⟨p,i⟩) y

def perturbedWeight {α : ℝ} {N : ℕ} (β ρ : ℝ) (c : ℕ → ℝ)
    (A : PatternMatrix α N) (g : PerturbationIndex N → ℝ) (y : UnitSpin N) : ℝ :=
  Real.exp (-β*unitEnergy A (y : SpinSpace N) + perturbation ρ c g y)
def perturbedPartition {α : ℝ} {N : ℕ} (β ρ : ℝ) (c : ℕ → ℝ)
    (A : PatternMatrix α N) (g : PerturbationIndex N → ℝ) : ℝ :=
  ∫ y, perturbedWeight β ρ c A g y ∂unitSphereLaw N

 
def perturbedAverage (α β ρ : ℝ) (N : ℕ) (c : ℕ → ℝ) (k : ℕ)
    (F : (Fin k → UnitSpin N) → ℝ) : ℝ :=
  ∫ A : PatternMatrix α N, ∫ g : PerturbationIndex N → ℝ,
    (∫ y : Fin k → UnitSpin N, F y * ∏ r, perturbedWeight β ρ c A g (y r)
      ∂Measure.pi (fun _ => unitSphereLaw N)) / (perturbedPartition β ρ c A g)^k
    ∂perturbationLaw N
  ∂Measure.pi (fun _ => Measure.pi fun _ => gaussianReal 0 1)

def unitOverlap {N : ℕ} (x y : UnitSpin N) : ℝ :=
  ∑ i, (x : SpinSpace N) i * (y : SpinSpace N) i
def replicaGram {N k : ℕ} (y : Fin k → UnitSpin N) : Fin k → Fin k → ℝ :=
  fun i j => unitOverlap (y i) (y j)

 
def perturbationGGError (α β ρ : ℝ) (N p k : ℕ) (c : ℕ → ℝ)
    (f : (Fin (k+2) → Fin (k+2) → ℝ) → ℝ) : ℝ :=
  perturbedAverage α β ρ N c (k+3) (fun y =>
    f (replicaGram (fun i : Fin (k+2) => y i.castSucc)) *
      unitOverlap (y 0) (y (Fin.last (k+2))) ^ p) -
  (1/(k+2:ℝ)) * perturbedAverage α β ρ N c (k+2) (fun y => f (replicaGram y)) *
    perturbedAverage α β ρ N c 2 (fun y => unitOverlap (y 0) (y 1)^p) -
  (1/(k+2:ℝ)) * ∑ l : Fin (k+1),
    perturbedAverage α β ρ N c (k+2) (fun y =>
      f (replicaGram y) * unitOverlap (y 0) (y l.succ)^p)

 

def ModelGGStatement : Prop :=
  ∀ (α β ρ : ℝ), 0 < α → 0 < β → 1/4 < ρ → ρ < 1/2 →
    ∀ (p k : ℕ), 1 ≤ p →
      ∀ f : (Fin (k+2) → Fin (k+2) → ℝ) → ℝ,
        Measurable f → (∀ R, |f R| ≤ 1) →
        Tendsto (fun N => ∫ c, |perturbationGGError α β ρ N p k c f|
          ∂coefficientProductLaw) atTop (nhds 0)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace MicroscopicJamming

abbrev ModelOverlapArray := ℕ → ℕ → ℝ

def perturbedSpinLaw {α : ℝ} {N : ℕ} (β ρ : ℝ) (c : ℕ → ℝ)
    (z : PatternMatrix α N × (PerturbationIndex N → ℝ)) : Measure (UnitSpin N) :=
  (unitSphereLaw N).tilted (fun y =>
    -β*unitEnergy z.1 (y : SpinSpace N)+perturbation ρ c z.2 y)

def infiniteReplicaGram {N : ℕ} (y : ℕ → UnitSpin N) : ModelOverlapArray :=
  fun i j => unitOverlap (y i) (y j)

def perturbedArrayLaw (α β ρ : ℝ) (N : ℕ) (c : ℕ → ℝ) : Measure ModelOverlapArray :=
  ((Measure.pi (fun _ : Fin (rowCount α N) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1)).prod (perturbationLaw N)).bind
    (fun z => (Measure.infinitePi (fun _ : ℕ => perturbedSpinLaw β ρ c z)).map
      infiniteReplicaGram)

 

def ModelGGIdentities (μ : Measure ModelOverlapArray) : Prop :=
  ∀ (n : ℕ) (f : (Fin (n+1) → Fin (n+1) → ℝ) → ℝ), Measurable f →
    (∃ C : ℝ, ∀ r, |f r| ≤ C) →
    ∀ ψ : ℝ → ℝ, Measurable ψ → (∃ C : ℝ, ∀ t, |ψ t| ≤ C) →
    ((n:ℝ)+1) * (∫ R, f (fun i j => R i j) * ψ (R 0 (n+1)) ∂μ) =
      (∫ R, f (fun i j => R i j) ∂μ) * (∫ R, ψ (R 0 1) ∂μ) +
      ∑ j : Fin n, ∫ R, f (fun i j => R i j) * ψ (R 0 (j.val+1)) ∂μ

def ModelArrayLimitStatement : Prop :=
  ∀ (α β ρ : ℝ), 0 < α → 0 < β → 1/4 < ρ → ρ < 1/2 →
    ∀ σ : ℕ → ℕ, StrictMono σ →
    ∀ᵐ c ∂coefficientProductLaw,
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ μ : Measure ModelOverlapArray,
        IsProbabilityMeasure μ ∧
        (∀ f : ModelOverlapArray →ᵇ ℝ,
          Tendsto (fun n => ∫ R, f R ∂perturbedArrayLaw α β ρ (σ (τ n)) c)
            atTop (nhds (∫ R, f R ∂μ))) ∧
        ModelGGIdentities μ ∧
        (∀ᵐ R ∂μ, (∀ i, R i i = 1) ∧ (∀ i j, R i j = R j i) ∧
          (∀ i j, |R i j| ≤ 1) ∧
          (∀ n (a : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, a i*a j*R i j)) ∧
        (∀ p : Equiv.Perm ℕ, μ.map (fun R i j => R (p i) (p j)) = μ)
end MicroscopicJamming

 
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace MicroscopicJamming

 

def ArrayUltrametricityStatement : Prop :=
  ∀ μ : Measure ModelOverlapArray, IsProbabilityMeasure μ →
    ModelGGIdentities μ →
    (∀ᵐ R ∂μ, (∀ i, R i i = 1) ∧ (∀ i j, R i j = R j i) ∧
      (∀ i j, |R i j| ≤ 1) ∧
      (∀ n (a : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, a i*a j*R i j)) →
    (∀ p : Equiv.Perm ℕ, μ.map (fun R i j => R (p i) (p j)) = μ) →
    ∀ᵐ R ∂μ, ∀ i j k, min (R i j) (R i k) ≤ R j k
end MicroscopicJamming

 
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace MicroscopicJamming

abbrev FiniteOverlapMatrix (n : ℕ) := Fin n → Fin n → ℝ

def finiteArrayView (n : ℕ) (R : ModelOverlapArray) : FiniteOverlapMatrix n := fun i j => R i j

lemma measurable_finiteArrayView (n : ℕ) : Measurable (finiteArrayView n) := by
  unfold finiteArrayView
  fun_prop

lemma indicator_one_abs {X : Type*} (s : Set X) (x : X) :
    |s.indicator (fun _ => (1:ℝ)) x| ≤ 1 := by
  by_cases hx : x ∈ s <;> simp [hx]

lemma indicator_one_product {X : Type*} (s t : Set X) (x : X) :
    s.indicator (fun _ => (1:ℝ)) x*t.indicator (fun _ => (1:ℝ)) x =
      (s∩t).indicator (fun _ => (1:ℝ)) x := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [hs,ht]

lemma indicator_one_preimage {X Y : Type*} (s : Set Y) (f : X → Y) (x : X) :
    s.indicator (fun _ => (1:ℝ)) (f x)=(f ⁻¹' s).indicator (fun _ => (1:ℝ)) x := by
  by_cases h : f x ∈ s <;> simp [h]

 

lemma gg_avoid_one {μ : Measure ModelOverlapArray} [IsProbabilityMeasure μ]
    (hgg : ModelGGIdentities μ) (m : ℕ)
    (E : Set (FiniteOverlapMatrix (m+1))) (hE : MeasurableSet E) (c : ℝ)
    (hc : ∀ r ∈ E, ∀ j : Fin m, r 0 ⟨j.val+1,by omega⟩ ≤ c) :
    ((m:ℝ)+1)*μ.real ((finiteArrayView (m+1) ⁻¹' E)∩{R | R 0 (m+1) ≤ c}) =
      (μ.real {R | R 0 1 ≤ c}+(m:ℝ))*μ.real (finiteArrayView (m+1) ⁻¹' E) := by
  let f : FiniteOverlapMatrix (m+1) → ℝ := E.indicator (fun _ => 1)
  let ψ : ℝ → ℝ := (Set.Iic c).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hψ : Measurable ψ := measurable_const.indicator measurableSet_Iic
  have h := hgg m f hf ⟨1,indicator_one_abs E⟩ ψ hψ ⟨1,indicator_one_abs (Set.Iic c)⟩
  have he : MeasurableSet (finiteArrayView (m+1) ⁻¹' E) := hE.preimage (measurable_finiteArrayView _)
  have hv (v : ℕ) : MeasurableSet {R : ModelOverlapArray | R 0 v ≤ c} := by
    apply measurableSet_le <;> fun_prop
  have hfi : (∫ R, f (finiteArrayView (m+1) R) ∂μ)=μ.real (finiteArrayView (m+1) ⁻¹' E) := by
    simp_rw [show f=(E.indicator (fun _ => (1:ℝ))) from rfl,indicator_one_preimage]
    exact integral_indicator_one he
  have hψi : (∫ R, ψ (R 0 1) ∂μ)=μ.real {R | R 0 1 ≤ c} := by
    change (∫ R, (Set.Iic c).indicator (fun _ => (1:ℝ)) (R 0 1) ∂μ)=_
    simp_rw [indicator_one_preimage]
    exact integral_indicator_one (hv 1)
  have hprod (v : ℕ) :
      (∫ R, f (finiteArrayView (m+1) R)*ψ (R 0 v) ∂μ)=
        μ.real ((finiteArrayView (m+1) ⁻¹' E)∩{R | R 0 v ≤ c}) := by
    calc
      _ = ∫ R, ((finiteArrayView (m+1) ⁻¹' E)∩{R | R 0 v ≤ c}).indicator (fun _ => (1:ℝ)) R ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with R
        by_cases hR : finiteArrayView (m+1) R ∈ E <;> by_cases hcR : R 0 v ≤ c <;> simp [f,ψ,hR,hcR]
      _ = _ := integral_indicator_one (he.inter (hv v))
  have hold (j : Fin m) :
      (∫ R, f (finiteArrayView (m+1) R)*ψ (R 0 (j.val+1)) ∂μ)=
        μ.real (finiteArrayView (m+1) ⁻¹' E) := by
    rw [hprod]
    congr 1
    apply inter_eq_left.mpr
    intro R hR
    exact hc _ hR j
  change ((m:ℝ)+1)*(∫ R, f (finiteArrayView (m+1) R)*ψ (R 0 (m+1)) ∂μ)=
    (∫ R, f (finiteArrayView (m+1) R) ∂μ)*(∫ R, ψ (R 0 1) ∂μ)+
      ∑ j : Fin m, (∫ R, f (finiteArrayView (m+1) R)*ψ (R 0 (j.val+1)) ∂μ) at h
  rw [hprod,hfi,hψi] at h
  simp_rw [hold] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  nlinarith [h]
end MicroscopicJamming

 
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace MicroscopicJamming

def arrayFlatten (R : ModelOverlapArray) : (ℕ × ℕ) → ℝ := fun i => R i.1 i.2
lemma measurable_arrayFlatten : Measurable arrayFlatten := by unfold arrayFlatten; fun_prop

def arrayUnflatten (r : (ℕ × ℕ) → ℝ) : ModelOverlapArray := fun i j => r (i,j)
lemma measurable_arrayUnflatten : Measurable arrayUnflatten := by unfold arrayUnflatten; fun_prop

lemma array_law_ext {μ ν : Measure ModelOverlapArray} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n : ℕ, μ.map (finiteArrayView (n+1))=ν.map (finiteArrayView (n+1))) : μ=ν := by
  classical
  let P : (I : Finset (ℕ × ℕ)) → Measure (I → ℝ) :=
    fun I => (μ.map arrayFlatten).map I.restrict
  have : IsProbabilityMeasure (μ.map arrayFlatten) := inferInstance
  have (I : Finset (ℕ × ℕ)) : IsProbabilityMeasure (P I) :=
    inferInstanceAs (IsProbabilityMeasure ((μ.map arrayFlatten).map I.restrict))
  have hm : IsProjectiveLimit (μ.map arrayFlatten) P := fun _ => rfl
  have hn : IsProjectiveLimit (ν.map arrayFlatten) P := by
    intro I
    let n : ℕ := I.sup fun i => max i.1 i.2
    have hb (i : I) : i.val.1<n+1 ∧ i.val.2<n+1 := by
      have hh : max i.val.1 i.val.2 ≤ n := Finset.le_sup (f:=fun i : ℕ × ℕ => max i.1 i.2) i.property
      have h1 := (le_max_left i.val.1 i.val.2).trans hh
      have h2 := (le_max_right i.val.1 i.val.2).trans hh
      omega
    let T : FiniteOverlapMatrix (n+1) → (I → ℝ) :=
      fun r i => r ⟨i.val.1,(hb i).1⟩ ⟨i.val.2,(hb i).2⟩
    have hT : Measurable T := by unfold T; fun_prop
    have hformula (ξ : Measure ModelOverlapArray) :
        (ξ.map arrayFlatten).map I.restrict=(ξ.map (finiteArrayView (n+1))).map T := by
      rw [Measure.map_map I.measurable_restrict measurable_arrayFlatten,
        Measure.map_map hT (measurable_finiteArrayView _)]
      rfl
    change (ν.map arrayFlatten).map I.restrict=(μ.map arrayFlatten).map I.restrict
    rw [hformula ν,hformula μ,h n]
  have hh := hm.unique hn
  have hback (ξ : Measure ModelOverlapArray) :
      (ξ.map arrayFlatten).map arrayUnflatten=ξ := by
    rw [Measure.map_map measurable_arrayUnflatten measurable_arrayFlatten]
    change ξ.map id=ξ
    exact Measure.map_id
  rw [←hback μ,←hback ν,hh]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace MicroscopicJamming

def finiteRankCovariance (n : ℕ) (q : ℕ → ℝ) (Q : ℝ)
    (B : Fin (n+1) → Fin (n+1) → ℕ) : Fin (n+1) → Fin (n+1) → ℝ :=
  fun i j => if i=j then Q else q (B i j)

lemma measurable_finiteRankCovariance (n : ℕ) (q : ℕ → ℝ) (Q : ℝ) :
    Measurable (finiteRankCovariance n q Q) := measurable_of_countable _

lemma realizedRankLaw_finiteCovariance (n : ℕ) (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) :
    (realizedRankLaw.map (rankCovarianceArray ms q Q)).map (finiteArrayView (n+1))=
      ((rankSeedLaw.map (rankGrowing n)).map (rankFiniteSteps ms)).map (finiteRankCovariance n q Q) := by
  rw [realizedRankLaw,
    Measure.map_map (measurable_rankCovarianceArray _ _ _) continuous_realizedRank.measurable,
    Measure.map_map (measurable_finiteArrayView _) ((measurable_rankCovarianceArray _ _ _).comp continuous_realizedRank.measurable),
    Measure.map_map (measurable_rankFiniteSteps _ _) (continuous_rankGrowing n).measurable,
    Measure.map_map (measurable_finiteRankCovariance _ _ _) ((measurable_rankFiniteSteps _ _).comp (continuous_rankGrowing n).measurable)]
  congr 1
  funext z i j
  simp only [Function.comp_def,finiteArrayView,rankCovarianceArray,finiteRankCovariance,
    rankFiniteSteps,realizedRank_stage,Fin.val_inj]

lemma cascadeReplicaLaw_finiteCovariance (n : ℕ) (ms : List ℝ) (q : ℕ → ℝ) (Q : ℝ) :
    ((cascadeReplicaLaw ms).map (cascadeCovarianceArray ms q Q)).map (finiteArrayView (n+1))=
      ((cascadeReplicaLaw ms).map (cascadeFiniteEdges (n:=n) ms)).map (finiteRankCovariance n q Q) := by
  rw [Measure.map_map (measurable_finiteArrayView _) (measurable_cascadeCovarianceArray _ _ _),
    Measure.map_map (measurable_finiteRankCovariance _ _ _) (measurable_cascadeFiniteEdges _ _)]
  congr 1
  funext z i j
  simp only [Function.comp_def,finiteArrayView,cascadeCovarianceArray,finiteRankCovariance,
    cascadeFiniteEdges,Fin.val_inj]

 

theorem realizedRankLaw_rpc : HasRPCFiniteRankLaws realizedRankLaw := by
  intro ms hms h01 q Q hq0 hq hQ
  let := cascadeReplicaLaw_probability ms
  let : IsProbabilityMeasure (realizedRankLaw.map (rankCovarianceArray ms q Q)) := inferInstance
  let : IsProbabilityMeasure ((cascadeReplicaLaw ms).map (cascadeCovarianceArray ms q Q)) :=
    inferInstance
  apply array_law_ext
  intro n
  rw [realizedRankLaw_finiteCovariance,cascadeReplicaLaw_finiteCovariance,
    rankGrowing_finiteSteps_law n ms hms h01]

end MicroscopicJamming

 
 

open MeasureTheory Set
open scoped BigOperators

namespace MicroscopicJamming

def RPCRankPositiveStatement : Prop :=
  ∀ n (R : Fin n → Fin n → ℝ), FiniteRank R →
  ∀ (q : ℝ → ℝ) (Q : ℝ), Monotone q → 0 ≤ q 0 → q 1 ≤ Q →
  ∀ a : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, a i*a j*(if i=j then Q else q (R i j))
end MicroscopicJamming

 
open MeasureTheory Set
open scoped BigOperators

namespace MicroscopicJamming
attribute [local instance] Classical.propDecidable

lemma block_indicator_psd {ι : Type*} [Fintype ι] (s : Setoid ι) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i*a j*(if s.r i j then (1:ℝ) else 0) := by
  classical
  let : Fintype (Quotient s) := Fintype.ofFinite _
  let q : ι → Quotient s := Quotient.mk s
  have he (i j : ι) : a i*a j*(if s.r i j then (1:ℝ) else 0) =
      ∑ c : Quotient s, (if q i=c then a i else 0)*(if q j=c then a j else 0) := by
    rw [Finset.sum_eq_single (q i)]
    · simp only [ite_true]
      have hq : q j=q i ↔ s.r i j := by
        rw [eq_comm]
        exact Quotient.eq
      simp only [hq]
      split_ifs <;> ring
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  simp_rw [he]
  have hsum : (∑ i, ∑ j, ∑ c : Quotient s,
      (if q i=c then a i else 0)*(if q j=c then a j else 0)) =
      ∑ c : Quotient s, (∑ i, if q i=c then a i else 0)^2 := by
    calc
      _ = ∑ i, ∑ c : Quotient s, ∑ j,
          (if q i=c then a i else 0)*(if q j=c then a j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ c : Quotient s, ∑ i, ∑ j,
          (if q i=c then a i else 0)*(if q j=c then a j else 0) := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        rw [sq,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
  rw [hsum]
  exact Finset.sum_nonneg fun c _ => sq_nonneg _

lemma integrable_rank_threshold (Q c : ℝ) :
    Integrable (fun t : ℝ => if t ≤ c then (1:ℝ) else 0) (volume.restrict (Set.Icc (0:ℝ) Q)) := by
  have hi := (integrable_const (1:ℝ) (μ := volume.restrict (Set.Icc (0:ℝ) Q))).indicator (s := Set.Iic c) measurableSet_Iic
  exact hi

lemma integral_rank_threshold {Q c : ℝ} (hc0 : 0 ≤ c) (hcQ : c ≤ Q) :
    (∫ t : ℝ in Set.Icc (0:ℝ) Q, if t ≤ c then (1:ℝ) else 0) = c := by
  change (∫ t : ℝ, (Set.Iic c).indicator (fun _ => (1:ℝ)) t ∂volume.restrict (Set.Icc (0:ℝ) Q)) = c
  rw [integral_indicator_const (1:ℝ) measurableSet_Iic]
  simp only [Measure.real, smul_eq_mul, mul_one]
  rw [Measure.restrict_apply measurableSet_Iic]
  have hs : Set.Iic c ∩ Set.Icc (0:ℝ) Q = Set.Icc 0 c := by
    ext t
    simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc]
    constructor
    · rintro ⟨htc,ht0,_⟩; exact ⟨ht0,htc⟩
    · rintro ⟨ht0,htc⟩; exact ⟨htc,ht0,htc.trans hcQ⟩
  rw [hs,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hc0]

lemma finite_ultrametric_psd {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) (Q : ℝ)
    (hd : ∀ i, A i i=Q) (hs : ∀ i j, A i j=A j i)
    (hb : ∀ i j, 0 ≤ A i j ∧ A i j ≤ Q)
    (hu : ∀ i j k, min (A i j) (A j k) ≤ A i k) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i*a j*A i j := by
  classical
  let μ := volume.restrict (Set.Icc (0:ℝ) Q)
  have hi (i j : ι) : Integrable (fun t : ℝ => a i*a j*(if t ≤ A i j then (1:ℝ) else 0)) μ :=
    (integrable_rank_threshold Q (A i j)).const_mul _
  have ht (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) Q) :
      0 ≤ ∑ i, ∑ j, a i*a j*(if t ≤ A i j then (1:ℝ) else 0) := by
    let s : Setoid ι :=
      { r := fun i j => t ≤ A i j
        iseqv := ⟨fun i => by rw [hd]; exact ht.2,
          fun hij => by rwa [hs],
          fun hij hjk => (le_min hij hjk).trans (hu _ _ _)⟩ }
    exact block_indicator_psd s a
  have hn : 0 ≤ ∫ t, ∑ i, ∑ j, a i*a j*(if t ≤ A i j then (1:ℝ) else 0) ∂μ :=
    integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Icc).mono ht)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))] at hn
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul] at hn
  dsimp only [μ] at hn
  simp_rw [integral_rank_threshold (hb _ _).1 (hb _ _).2] at hn
  exact hn
end MicroscopicJamming

 
open MeasureTheory Set
open scoped BigOperators

namespace MicroscopicJamming

 theorem rpcRankPositive : RPCRankPositiveStatement := by
  classical
  intro n R hR q Q hq hq0 hqQ a
  let A : Fin n → Fin n → ℝ := fun i j => if i=j then Q else q (R i j)
  have hQ0 : 0 ≤ Q := hq0.trans ((hq zero_le_one).trans hqQ)
  have hA (i j : Fin n) : 0 ≤ A i j ∧ A i j ≤ Q := by
    unfold A
    split_ifs
    · exact ⟨hQ0,le_rfl⟩
    · exact ⟨hq0.trans (hq (hR.2.2.1 i j).1),(hq (hR.2.2.1 i j).2).trans hqQ⟩
  have hd (i : Fin n) : A i i=Q := by simp [A]
  have hs (i j : Fin n) : A i j=A j i := by simp [A,eq_comm,hR.2.1]
  have hu (i j k : Fin n) : min (A i j) (A j k) ≤ A i k := by
    by_cases hij : i=j
    · subst j; exact min_le_right _ _
    by_cases hjk : j=k
    · subst k; exact min_le_left _ _
    by_cases hik : i=k
    · subst k; rw [hd]; exact (min_le_left _ _).trans (hA _ _).2
    simp only [A,ite_eq_right hij,ite_eq_right hjk,ite_eq_right hik]
    rw [← hq.map_min]
    exact hq (hR.2.2.2 i j k)
  exact finite_ultrametric_psd A Q hd hs hA hu a
end MicroscopicJamming

end

end OAI
