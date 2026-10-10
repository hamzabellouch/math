import Mathlib
import OAI.Probability.ParisiFinite.ThermalDeviation

namespace OAI

/-! Mixed Replica Identity. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {K : Type*} [Fintype K] [DecidableEq K]

 

theorem mixed_replica_identity {n r : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ) :
    (∫ z, ∑ σ, replicaWeight (field (mixedCoeff n d β x) z) σ*
      (field (mixedNoise n d k) z (σ i)*f σ)
      ∂gaussianLaw (MixedIndex n d)) =
      x k*(∫ z, replicaMean (field (mixedCoeff n d β x) z)
        (fun σ => f σ*∑ l, (overlap (σ i) (σ l))^(d k))
        ∂gaussianLaw (MixedIndex n d)) -
      (r:ℝ)*x k*(∫ z, replicaMean (field (mixedCoeff n d β x) z)
        (fun τ : Fin (r+1) → Configuration n =>
          f (fun l => τ l.castSucc)*(overlap (τ i.castSucc) (τ (Fin.last r)))^(d k))
        ∂gaussianLaw (MixedIndex n d)) := by
  have h := integral_field_replica_energy_covariance
    (mixedCoeff n d β x) (mixedNoise n d k) i f
  simp_rw [mixedNoise_crossCov hn] at h
  simp only [replicaMean, ← Finset.mul_sum] at h ⊢
  have he₁ (σ : Fin r → Configuration n) (z) :
      replicaWeight (field (mixedCoeff n d β x) z) σ*
        (f σ*(x k*∑ l, overlap (σ i) (σ l)^(d k))) =
      x k*(replicaWeight (field (mixedCoeff n d β x) z) σ*
        (f σ*∑ l, overlap (σ i) (σ l)^(d k))) := by ring
  have he₂ (τ : Fin (r+1) → Configuration n) (z) :
      replicaWeight (field (mixedCoeff n d β x) z) τ*
        (f (fun l => τ l.castSucc)*(x k*overlap (τ i.castSucc) (τ (Fin.last r))^(d k))) =
      x k*(replicaWeight (field (mixedCoeff n d β x) z) τ*
        (f (fun l => τ l.castSucc)*overlap (τ i.castSucc) (τ (Fin.last r))^(d k))) := by ring
  simp_rw [he₁, he₂, ← Finset.mul_sum, integral_const_mul] at h
  convert h using 1
  ring

lemma mixed_energyMean {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K) :
    energyMean (mixedCoeff n d β x) (mixedNoise n d k) =
      x k*(1-averagedReplica (mixedCoeff n d β x)
        (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^(d k))) := by
  have h := mixed_replica_identity hn d β x k (0 : Fin 1) (fun _ => 1)
  norm_num only [Nat.cast_one, Fin.castSucc_zero] at h
  change energyObservation (mixedCoeff n d β x) (mixedNoise n d k) (0 : Fin 1) (fun _ => 1) =
    x k*averagedReplica (mixedCoeff n d β x)
      (fun σ : Fin 1 → Configuration n => 1*∑ l, (overlap (σ 0) (σ l))^(d k))-
    (1:ℝ)*x k*averagedReplica (mixedCoeff n d β x)
      (fun τ : Fin 2 → Configuration n => 1*(overlap (τ 0) (τ 1))^(d k)) at h
  simp only [energyObservation_one, one_mul, Fin.sum_univ_one, overlap_self hn, one_pow,
    averagedReplica_const] at h
  linarith

 

def mixedGGDefect {n r : ℕ} (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K) (i : Fin r)
    (f : (Fin r → Configuration n) → ℝ) : ℝ :=
  (r:ℝ)*averagedReplica (mixedCoeff n d β x)
      (fun τ : Fin (r+1) → Configuration n => f (fun l => τ l.castSucc)*
        (overlap (τ i.castSucc) (τ (Fin.last r)))^(d k))-
    averagedReplica (mixedCoeff n d β x) f*
      averagedReplica (mixedCoeff n d β x)
        (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^(d k))-
    averagedReplica (mixedCoeff n d β x)
      (fun σ => f σ*∑ l ∈ Finset.univ.erase i, (overlap (σ i) (σ l))^(d k))

 

theorem mixedGGDefect_identity {n r : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ) :
    x k*mixedGGDefect d β x k i f =
      energyMean (mixedCoeff n d β x) (mixedNoise n d k)*
        averagedReplica (mixedCoeff n d β x) f-
      energyObservation (mixedCoeff n d β x) (mixedNoise n d k) i f := by
  have h := mixed_replica_identity hn d β x k i f
  change energyObservation (mixedCoeff n d β x) (mixedNoise n d k) i f =
    x k*averagedReplica (mixedCoeff n d β x) (fun σ => f σ*∑ l, overlap (σ i) (σ l)^(d k))-
      (r:ℝ)*x k*averagedReplica (mixedCoeff n d β x)
      (fun τ : Fin (r+1) → Configuration n => f (fun l => τ l.castSucc)*
        overlap (τ i.castSucc) (τ (Fin.last r))^(d k)) at h
  have he (σ : Fin r → Configuration n) : f σ*∑ l, overlap (σ i) (σ l)^(d k) =
      f σ+f σ*∑ l ∈ Finset.univ.erase i, overlap (σ i) (σ l)^(d k) := by
    have hs := Finset.sum_erase_add Finset.univ (fun l => overlap (σ i) (σ l)^(d k)) (Finset.mem_univ i)
    rw [overlap_self hn, one_pow] at hs
    rw [← hs]
    ring
  simp_rw [he, averagedReplica_add] at h
  rw [mixed_energyMean hn, h]
  unfold mixedGGDefect
  ring

 

theorem mixedGGDefect_bound {n r : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K)
    (i : Fin r) (f : (Fin r → Configuration n) → ℝ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ σ, |f σ|≤M) :
    |x k*mixedGGDefect d β x k i f| ≤
      M*energyDeviation (mixedCoeff n d β x) (mixedNoise n d k)
        (energyMean (mixedCoeff n d β x) (mixedNoise n d k)) := by
  rw [mixedGGDefect_identity hn, abs_sub_comm]
  exact energyObservation_covariance_bound _ _ i f hM hf _

lemma mixed_energyMean_bounds {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) (k : K) (ht : 0 ≤ x k) :
    0≤energyMean (mixedCoeff n d β x) (mixedNoise n d k) ∧
      energyMean (mixedCoeff n d β x) (mixedNoise n d k)≤2*x k := by
  have hb : |averagedReplica (mixedCoeff n d β x)
      (fun τ : Fin 2 → Configuration n => (overlap (τ 0) (τ 1))^(d k))|≤1 := by
    apply averagedReplica_abs_bound
    intro τ
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_overlap_le_one _ _)
  rw [mixed_energyMean hn]
  rw [abs_le] at hb
  constructor
  · exact mul_nonneg ht (by linarith)
  · nlinarith [mul_le_mul_of_nonneg_left hb.1 ht]

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKGaussian ParisiFinite ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

omit [Fintype ι] [Nonempty ι] in
lemma continuous_field_coeff (z : κ → ℝ) : Continuous (fun A : ι → κ → ℝ => field A z) := by
  unfold field
  fun_prop

lemma continuous_gibbsMean_first (v : ι → ℝ) : Continuous (fun x => gibbsMean 1 x v) := by
  unfold gibbsMean
  simp only [one_mul]
  exact continuous_finsetSum _ fun s _ => (continuous_weight s).mul continuous_const

lemma continuous_gibbsCov_first (v : ι → ℝ) : Continuous (fun x => gibbsCov 1 x v v) := by
  unfold gibbsCov
  exact (continuous_gibbsMean_first _).sub ((continuous_gibbsMean_first v).mul (continuous_gibbsMean_first v))

lemma continuous_energyMean_coeff (B : ι → κ → ℝ) : Continuous (fun A => energyMean A B) := by
  unfold energyMean
  suffices h : Continuous (fun A => ∫ z, gibbsMean 1 (field A z) (field B z) ∂gaussianLaw κ) by
    simpa only [gibbsMean, one_mul] using h
  apply continuous_of_dominated (bound:=fun z => ‖field B z‖)
  · intro A
    simpa only [zero_smul, add_zero] using (continuous_lineMean A B 0).aestronglyMeasurable
  · intro A
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using abs_gibbsMean_le 1 (field A z) (field B z)
  · exact integrable_norm_field B
  · exact ae_of_all _ fun z => (continuous_gibbsMean_first _).comp (continuous_field_coeff z)

lemma abs_energyMean_le (A B : ι → κ → ℝ) :
    |energyMean A B| ≤ ∫ z, ‖field B z‖ ∂gaussianLaw κ := by
  apply abs_integral_le_integral_abs.trans
  refine integral_mono ?_ (integrable_norm_field B) (fun z => ?_)
  · simpa only [gibbsMean, one_mul, zero_smul, add_zero] using (integrable_lineMean A B 0).abs
  · simpa only [gibbsMean, one_mul] using abs_gibbsMean_le 1 (field A z) (field B z)

 
def energyVariance (A B : ι → κ → ℝ) : ℝ :=
  ∫ z, gibbsCov 1 (field A z) (field B z) (field B z) ∂gaussianLaw κ

lemma energyVariance_nonneg (A B : ι → κ → ℝ) : 0 ≤ energyVariance A B :=
  integral_nonneg fun _ => gibbsCov_self_nonneg _ _ _

lemma continuous_energyVariance_coeff (B : ι → κ → ℝ) : Continuous (fun A => energyVariance A B) := by
  apply continuous_of_dominated (bound:=fun z => 2*‖field B z‖^2)
  · intro A
    simpa only [zero_smul, add_zero] using (continuous_lineVariance A B 0).aestronglyMeasurable
  · intro A
    exact ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs, sq, mul_assoc] using abs_gibbsCov_le 1 (field A z) (field B z) (field B z)
  · exact (integrable_norm_field_sq B).const_mul 2
  · exact ae_of_all _ fun z => (continuous_gibbsCov_first _).comp (continuous_field_coeff z)

lemma abs_energyVariance_le (A B : ι → κ → ℝ) :
    |energyVariance A B| ≤ ∫ z, 2*‖field B z‖^2 ∂gaussianLaw κ := by
  apply abs_integral_le_integral_abs.trans
  refine integral_mono ?_ ((integrable_norm_field_sq B).const_mul 2) (fun z => ?_)
  · simpa only [zero_smul, add_zero] using (integrable_lineVariance A B 0).abs
  · simpa only [sq, mul_assoc] using abs_gibbsCov_le 1 (field A z) (field B z) (field B z)

omit [Nonempty ι] in
lemma varianceLine_eq_energyVariance (A B : ι → κ → ℝ) (t : ℝ) :
    varianceLine A B t = energyVariance (affineCoeff A B t) B := by
  simp only [varianceLine, energyVariance, field_affineCoeff]

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity

 

def intervalLaw (a b : ℝ) : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc a b)

instance intervalLaw_isFiniteMeasure (a b : ℝ) : IsFiniteMeasure (intervalLaw a b) := by
  unfold intervalLaw
  infer_instance

lemma intervalLaw_probability {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (intervalLaw a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

lemma intervalLaw_ae (a b : ℝ) : ∀ᵐ t ∂intervalLaw a b, t ∈ Set.Icc a b :=
  ae_cond_mem measurableSet_Icc

lemma integral_intervalLaw {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ t, f t ∂intervalLaw a b) = (b-a)⁻¹*(∫ t in a..b, f t) := by
  simp only [intervalLaw, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

abbrev boxLaw (m : ℕ) (a b : ℝ) : Measure (Fin m → ℝ) := Measure.pi (fun _ => intervalLaw a b)

lemma boxLaw_ae (m : ℕ) (a b : ℝ) : ∀ᵐ x ∂boxLaw m a b, ∀ k, x k∈Set.Icc a b := by
  apply ae_all_iff.mpr
  intro k
  exact Measure.tendsto_eval_ae_ae.eventually (intervalLaw_ae a b)

 
lemma integral_boxLaw_coordinate {m : ℕ} {a b : ℝ} (_hab : a < b)
    (k : Fin (m+1)) {F : (Fin (m+1) → ℝ) → ℝ} (hF : Integrable F (boxLaw (m+1) a b)) :
    (∫ x, F x ∂boxLaw (m+1) a b) =
      ∫ y : Fin m → ℝ, ∫ t : ℝ, F (k.insertNth t y) ∂intervalLaw a b ∂boxLaw m a b := by
  let := intervalLaw_probability _hab
  let T := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) k).symm
  have hm : MeasurePreserving T ((intervalLaw a b).prod (boxLaw m a b)) (boxLaw (m+1) a b) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => intervalLaw a b) k).symm
  have hi : Integrable (fun p => F (T p)) ((intervalLaw a b).prod (boxLaw m a b)) :=
    (hm.integrable_comp hF.aestronglyMeasurable).mpr hF
  rw [← hm.integral_comp' F, integral_prod_symm _ hi]
  rfl

 

theorem exists_box_sum_le {m : ℕ} {a b C : ℝ} (hab : a < b)
    (F : Fin (m+1) → (Fin (m+1) → ℝ) → ℝ)
    (hc : ∀ k, Continuous (F k))
    (hb : ∀ k, ∃ M : ℝ, ∀ x, |F k x| ≤ M)
    (hi : ∀ k (y : Fin m → ℝ), (∀ j, y j∈Set.Icc a b) →
      (∫ t in a..b, F k (k.insertNth t y)) ≤ (b-a)*C) :
    ∃ x : Fin (m+1) → ℝ, (∀ k, x k∈Set.Icc a b) ∧
      (∑ k, F k x) ≤ (m+1:ℕ)*C := by
  let := intervalLaw_probability hab
  have hI (k) : Integrable (F k) (boxLaw (m+1) a b) := by
    obtain ⟨M, hM⟩ := hb k
    exact Integrable.of_bound (hc k).aestronglyMeasurable M (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x)
  have hsum : Integrable (fun x => ∑ k, F k x) (boxLaw (m+1) a b) :=
    integrable_finsetSum _ fun k _ => hI k
  have hnull : boxLaw (m+1) a b {x | ¬∀ k, x k∈Set.Icc a b}=0 := by
    exact ae_iff.mp (boxLaw_ae (m+1) a b)
  obtain ⟨x, hx, hle⟩ := exists_notMem_null_le_integral hsum hnull
  refine ⟨x, not_not.mp hx, hle.trans ?_⟩
  rw [integral_finsetSum _ (fun k _ => hI k)]
  calc
    _ ≤ ∑ _k : Fin (m+1), C := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_boxLaw_coordinate hab k (hI k)]
      have hint : Integrable (fun y : Fin m → ℝ => ∫ t, F k (k.insertNth t y) ∂intervalLaw a b) (boxLaw m a b) := by
        let T := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) k).symm
        have hm : MeasurePreserving T ((intervalLaw a b).prod (boxLaw m a b)) (boxLaw (m+1) a b) :=
          (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => intervalLaw a b) k).symm
        exact ((hm.integrable_comp (hc k).aestronglyMeasurable).mpr (hI k)).integral_prod_right
      have hj := integral_mono_ae hint (integrable_const C) ?_
      · simpa using hj
      filter_upwards [boxLaw_ae m a b] with y hy
      rw [integral_intervalLaw hab.le]
      have hi' := hi k y hy
      have hp : 0 < b-a := sub_pos.mpr hab
      calc
        _ ≤ (b-a)⁻¹*((b-a)*C) := mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr hp.le)
        _ = C := by field_simp
    _ = _ := by simp

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite
variable {K : Type*} [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
lemma continuous_mixedCoeff (n : ℕ) (d : K → ℕ) (β : ℝ) :
    Continuous (mixedCoeff n d β) := by
  apply continuous_pi
  intro σ
  apply continuous_pi
  intro u
  cases u with
  | inl e => exact continuous_const
  | inr u => exact (continuous_apply u.1).mul continuous_const

omit [Fintype K] in
lemma continuous_shiftCoord (k : K) (t : ℝ) :
    Continuous (fun x : K → ℝ => Function.update x k (x k+t)) := by
  apply continuous_pi
  intro j
  by_cases h : j=k
  · subst j
    simpa only [Function.update_self] using (continuous_apply k : Continuous (fun x : K → ℝ => x k)).add_const t
  · simpa only [Function.update_of_ne h] using continuous_apply j

 

def mixedError (n : ℕ) (d : K → ℕ) (β δ V : ℝ) (k : K) (x : K → ℝ) : ℝ :=
  energyVariance (mixedCoeff n d β x) (mixedNoise n d k)+(1+4*V/δ)+
    (energyMean (mixedCoeff n d β (Function.update x k (x k+δ))) (mixedNoise n d k)-
      energyMean (mixedCoeff n d β (Function.update x k (x k-δ))) (mixedNoise n d k))

lemma continuous_mixedError (n : ℕ) (d : K → ℕ) (β δ V : ℝ) (k : K) :
    Continuous (mixedError n d β δ V k) := by
  apply (((continuous_energyVariance_coeff _).comp (continuous_mixedCoeff n d β)).add continuous_const).add
  apply Continuous.sub
  · exact (continuous_energyMean_coeff _).comp ((continuous_mixedCoeff n d β).comp (continuous_shiftCoord k δ))
  · have hc := (continuous_energyMean_coeff (mixedNoise n d k)).comp
      ((continuous_mixedCoeff n d β).comp (continuous_shiftCoord k (-δ)))
    change Continuous (fun x => energyMean (mixedCoeff n d β (Function.update x k (x k+(-δ)))) (mixedNoise n d k)) at hc
    simpa only [sub_eq_add_neg] using hc

lemma mixedError_bounded (n : ℕ) (d : K → ℕ) (β δ V : ℝ) (k : K) :
    ∃ M : ℝ, ∀ x, |mixedError n d β δ V k x| ≤ M := by
  let B := mixedNoise n d k
  let U := ∫ z, ‖field B z‖ ∂gaussianLaw (MixedIndex n d)
  let W := ∫ z, 2*‖field B z‖^2 ∂gaussianLaw (MixedIndex n d)
  refine ⟨W+|1+4*V/δ|+2*U, fun x => ?_⟩
  have h0 := abs_energyVariance_le (mixedCoeff n d β x) B
  have h1 := abs_energyMean_le (mixedCoeff n d β (Function.update x k (x k+δ))) B
  have h2 := abs_energyMean_le (mixedCoeff n d β (Function.update x k (x k-δ))) B
  change _ ≤ W at h0
  change _ ≤ U at h1 h2
  unfold mixedError
  calc
    _ ≤ |energyVariance (mixedCoeff n d β x) B+(1+4*V/δ)|+
      |energyMean (mixedCoeff n d β (Function.update x k (x k+δ))) B-
        energyMean (mixedCoeff n d β (Function.update x k (x k-δ))) B| := abs_add_le _ _
    _ ≤ _ := by
      linarith [abs_add_le (energyVariance (mixedCoeff n d β x) B) (1+4*V/δ),
        abs_sub (energyMean (mixedCoeff n d β (Function.update x k (x k+δ))) B)
          (energyMean (mixedCoeff n d β (Function.update x k (x k-δ))) B)]

lemma mixedError_as_line (n : ℕ) (d : K → ℕ) (β δ V : ℝ) (k : K) (x : K → ℝ) (t : ℝ) :
    mixedError n d β δ V k (Function.update x k t) =
      varianceLine (mixedCoeff n d β (Function.update x k 0)) (mixedNoise n d k) t+(1+4*V/δ)+
      (meanLine (mixedCoeff n d β (Function.update x k 0)) (mixedNoise n d k) (t+δ)-
        meanLine (mixedCoeff n d β (Function.update x k 0)) (mixedNoise n d k) (t-δ)) := by
  simp only [varianceLine_eq_energyVariance, meanLine_eq_energyMean, affineCoeff_mixed_update,
    mixedError, Function.update_self, Function.update_idem]

lemma mixedError_dominates {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) (k : K) (x : K → ℝ)
    (hx : ∀ j, x j∈Set.Icc s (2*s)) :
    energyDeviation (mixedCoeff n d β x) (mixedNoise n d k)
      (energyMean (mixedCoeff n d β x) (mixedNoise n d k)) ≤
    mixedError n d β δ (Real.sqrt (β^2*n/2+9*(Fintype.card K:ℝ)*s^2)) k x := by
  let A := mixedCoeff n d β (Function.update x k 0)
  let B := mixedNoise n d k
  let V := Real.sqrt (β^2*n/2+9*(Fintype.card K:ℝ)*s^2)
  have hV (u : ℝ) (hu : u∈Set.Icc (s-δ) (2*s+δ)) : pressureFluctuation (affineCoeff A B u) ≤ V := by
    rw [affineCoeff_mixed_update]
    apply (mixed_pressureFluctuation_le hn d β _).trans
    apply Real.sqrt_le_sqrt
    have hcoord (j : K) : (Function.update x k u j)^2 ≤ 9*s^2 := by
      have hj : 0 ≤ Function.update x k u j ∧ Function.update x k u j ≤ 3*s := by
        by_cases h : j=k
        · subst j
          simp only [Function.update_self]
          constructor <;> linarith [hu.1, hu.2]
        · rw [Function.update_of_ne h]
          constructor <;> linarith [(hx j).1, (hx j).2]
      nlinarith [sq_nonneg (3*s-Function.update x k u j)]
    have hsum := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hcoord j)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    nlinarith [sq_nonneg β]
  have h := energyDeviation_amplitude_bound A B hδ (hx k) hV
  rw [varianceLine_eq_energyVariance, meanLine_eq_energyMean, meanLine_eq_energyMean,
    affineCoeff_mixed_update, affineCoeff_mixed_update, affineCoeff_mixed_update,
    Function.update_eq_self] at h
  exact h

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma mixedError_insert {m : ℕ} (n : ℕ) (d : Fin (m+1) → ℕ) (β δ V : ℝ)
    (k : Fin (m+1)) (y : Fin m → ℝ) (t : ℝ) :
    mixedError n d β δ V k (k.insertNth t y) =
      varianceLine (mixedCoeff n d β (k.insertNth 0 y)) (mixedNoise n d k) t+(1+4*V/δ)+
      (meanLine (mixedCoeff n d β (k.insertNth 0 y)) (mixedNoise n d k) (t+δ)-
        meanLine (mixedCoeff n d β (k.insertNth 0 y)) (mixedNoise n d k) (t-δ)) := by
  simpa only [Fin.update_insertNth] using mixedError_as_line n d β δ V k (k.insertNth 0 y) t

lemma integral_mixedError_le {m n : ℕ} (hn : 0<n) (d : Fin (m+1) → ℕ) (β V : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s)
    (k : Fin (m+1)) (y : Fin m → ℝ) :
    (∫ t in s..2*s, mixedError n d β δ V k (k.insertNth t y)) ≤
      s*(5+4*V/δ+12*δ) := by
  let A := mixedCoeff n d β (k.insertNth 0 y)
  let B := mixedNoise n d k
  have hp : Continuous (fun t => meanLine A B (t+δ)-meanLine A B (t-δ)) :=
    ((continuous_meanLine A B).comp (continuous_id.add_const δ)).sub
      ((continuous_meanLine A B).comp (continuous_id.sub continuous_const))
  simp_rw [mixedError_insert]
  change (∫ t in s..2*s, (varianceLine A B t+(1+4*V/δ))+(meanLine A B (t+δ)-meanLine A B (t-δ))) ≤ _
  have hv : Continuous (fun t => varianceLine A B t+(1+4*V/δ)) :=
    (continuous_varianceLine A B).add continuous_const
  rw [intervalIntegral.integral_add (hv.intervalIntegrable s (2*s)) (hp.intervalIntegrable s (2*s))]
  rw [intervalIntegral.integral_add ((continuous_varianceLine A B).intervalIntegrable s (2*s))
    (continuous_const.intervalIntegrable s (2*s)), integral_varianceLine, intervalIntegral.integral_const, smul_eq_mul]
  have hb (t : ℝ) (ht : 0 ≤ t) : 0 ≤ meanLine A B t ∧ meanLine A B t ≤ 2*t := by
    have he : affineCoeff A B t = mixedCoeff n d β (k.insertNth t y) := by
      simpa only [A, B, Fin.update_insertNth] using affineCoeff_mixed_update n d β (k.insertNth 0 y) k t
    rw [meanLine_eq_energyMean, he]
    simpa only [Fin.insertNth_apply_same] using mixed_energyMean_bounds hn d β (k.insertNth t y) k
      (by simpa only [Fin.insertNth_apply_same] using ht)
  have h2 := hb (2*s) (by linarith)
  have h1 := hb s hs.le
  have hup := hb (2*s+δ) (by linarith)
  have hlo := hb (s-δ) (by linarith)
  have hi := integral_meanLine_increment_le A B s (2*s) hδ
  have hh : meanLine A B (2*s+δ)-meanLine A B (s-δ) ≤ 6*s := by linarith
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤2*δ)
  nlinarith

 

theorem exists_mixed_energy_amplitude {m n : ℕ} (hn : 0<n) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) :
    ∃ x : Fin (m+1) → ℝ, (∀ k, x k∈Set.Icc s (2*s)) ∧
      ∀ k, energyDeviation (mixedCoeff n d β x) (mixedNoise n d k)
        (energyMean (mixedCoeff n d β x) (mixedNoise n d k)) ≤
      (m+1:ℕ)*(5+4*Real.sqrt (β^2*n/2+9*(m+1:ℕ)*s^2)/δ+12*δ) := by
  let V := Real.sqrt (β^2*n/2+9*(m+1:ℕ)*s^2)
  obtain ⟨x, hx, hsum⟩ := exists_box_sum_le (show s<2*s by linarith)
    (mixedError n d β δ V) (continuous_mixedError n d β δ V) (mixedError_bounded n d β δ V)
    (fun k y _ => by
      simpa only [show 2*s-s=s by ring] using integral_mixedError_le hn d β V hs hδ hδs k y)
  have hdom (k) := mixedError_dominates hn d β hs hδ hδs k x hx
  simp only [Fintype.card_fin] at hdom
  have hnon (k) : 0 ≤ mixedError n d β δ V k x :=
    (energyDeviation_nonneg _ _ _).trans (hdom k)
  refine ⟨x, hx, fun k => (hdom k).trans ?_⟩
  apply le_trans _ hsum
  exact Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ k)

 

theorem exists_mixed_GG_amplitude {m n : ℕ} (hn : 0<n) (d : Fin (m+1) → ℕ) (β : ℝ)
    {s δ : ℝ} (hs : 0<s) (hδ : 0<δ) (hδs : δ ≤ s) :
    ∃ x : Fin (m+1) → ℝ, (∀ k, x k∈Set.Icc s (2*s)) ∧
      ∀ (k : Fin (m+1)) (r : ℕ) (i : Fin r) (f : (Fin r → Configuration n) → ℝ),
      (∀ σ, |f σ|≤1) → |mixedGGDefect d β x k i f| ≤
      ((m+1:ℕ)*(5+4*Real.sqrt (β^2*n/2+9*(m+1:ℕ)*s^2)/δ+12*δ))/s := by
  obtain ⟨x, hx, h⟩ := exists_mixed_energy_amplitude hn d β hs hδ hδs
  refine ⟨x, hx, fun k r i f hf => ?_⟩
  have hgg := mixedGGDefect_bound hn d β x k i f (by norm_num : (0:ℝ)≤1) hf
  rw [one_mul, abs_mul, abs_of_nonneg (hs.le.trans (hx k).1)] at hgg
  have hmul := mul_le_mul_of_nonneg_right (hx k).1 (abs_nonneg (mixedGGDefect d β x k i f))
  apply (le_div_iff₀ hs).mpr
  nlinarith only [hgg, hmul, h k]

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {K : Type*} [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
lemma increment_mixed_sub {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration n) :
    ParisiInterpolation.increment (mixedCoeff n d β x) σ τ-
      ParisiInterpolation.increment (fun s e => β*skCoeff n s e) σ τ =
      ∑ k, 2*(x k)^2*(1-(overlap σ τ)^(d k)) := by
  have hk (s t : Configuration n) : kernel (mixedCoeff n d β x) s t =
      kernel (fun s e => β*skCoeff n s e) s t+∑ k, (x k)^2*(overlap s t)^(d k) := by
    rw [mixedCoeff_kernel hn, kernel_scale, kernel, coeff_covariance hn]
    ring
  rw [increment_eq_kernel, increment_eq_kernel, hk, hk, hk, overlap_self hn, overlap_self hn]
  simp only [one_pow, mul_one]
  have hs : (∑ k, (x k)^2)+(∑ k, (x k)^2)-2*(∑ k, (x k)^2*(overlap σ τ)^(d k))=
      ∑ k, 2*(x k)^2*(1-(overlap σ τ)^(d k)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  linarith only [hs]

omit [DecidableEq K] in
lemma abs_increment_mixed_sub_le {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ)
    (σ τ : Configuration n) :
    |ParisiInterpolation.increment (mixedCoeff n d β x) σ τ-
      ParisiInterpolation.increment (fun s e => β*skCoeff n s e) σ τ| ≤ 4*∑ k, (x k)^2 := by
  rw [increment_mixed_sub hn, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤2*(x k)^2)]
  have h : |(overlap σ τ)^(d k)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_overlap_le_one _ _)
  have hd : |1-(overlap σ τ)^(d k)| ≤ 2 := by
    have := abs_sub_le (1:ℝ) 0 ((overlap σ τ)^(d k))
    simp only [sub_zero, zero_sub, abs_neg, abs_one] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0:ℝ)≤2*(x k)^2)]

 

omit [DecidableEq K] in
theorem mixed_pressure_error {n : ℕ} (hn : 0<n) (d : K → ℕ) (β : ℝ) (x : K → ℝ) :
    |expected (mixedCoeff n d β x)-expected (fun s e => β*skCoeff n s e)| ≤
      Real.pi*(∑ k, (x k)^2) := by
  have h := expected_difference_le (fun s e => β*skCoeff n s e) (mixedCoeff n d β x)
    (show (0:ℝ)≤4*∑ k, (x k)^2 by positivity) (abs_increment_mixed_sub_le hn d β x)
  convert h using 1
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma mixed_root_pressure_bound {n L : ℕ} (hn : 0<n) (hL : 0<L) (β : ℝ) :
    Real.sqrt (β^2*(n:ℝ)/2+9*(L:ℝ)*(eighthRootScale n^3)^2) ≤
      (|β|+3*(L:ℝ))*eighthRootScale n^4 := by
  let r := eighthRootScale n
  have hr : 1≤r := one_le_eighthRootScale hn
  have hr0 : 0≤r := by linarith
  have hL' : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hp : (r^3)^2 ≤ r^8 := by
    have h : r^6 ≤ r^8 := pow_le_pow_right₀ hr (by norm_num : 6≤8)
    nlinarith only [h]
  have hn' : (n:ℝ)=r^8 := (eighthRootScale_pow_eight n).symm
  have hβ : β^2/2+9*(L:ℝ) ≤ (|β|+3*(L:ℝ))^2 := by
    nlinarith [sq_abs β, abs_nonneg β, sq_nonneg β,
      mul_nonneg (sub_nonneg.mpr hL') (Nat.cast_nonneg L), mul_nonneg (abs_nonneg β) (Nat.cast_nonneg L)]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · change β^2*(n:ℝ)/2+9*(L:ℝ)*(r^3)^2 ≤ ((|β|+3*(L:ℝ))*r^4)^2
    rw [hn']
    have hh := mul_le_mul_of_nonneg_right hβ (pow_nonneg hr0 8)
    have hh' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤9*(L:ℝ))
    nlinarith only [hh, hh']

lemma mixed_root_GG_bound {n L : ℕ} (hn : 0<n) (hL : 0<L) (β : ℝ) :
    ((L:ℝ)*(5+4*Real.sqrt (β^2*(n:ℝ)/2+9*(L:ℝ)*(eighthRootScale n^3)^2)/(eighthRootScale n^2)+
      12*(eighthRootScale n^2)))/(eighthRootScale n^3) ≤
      ((L:ℝ)*(17+4*|β|+12*(L:ℝ)))/eighthRootScale n := by
  let r := eighthRootScale n
  have hr : 1≤r := one_le_eighthRootScale hn
  have hrp : 0<r := by linarith
  have hb := mixed_root_pressure_bound hn hL β
  change Real.sqrt (β^2*(n:ℝ)/2+9*(L:ℝ)*(r^3)^2) ≤ (|β|+3*(L:ℝ))*r^4 at hb
  have hd := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)) (sq_nonneg r)
  have he : 4*((|β|+3*(L:ℝ))*r^4)/r^2=4*(|β|+3*(L:ℝ))*r^2 := by field_simp
  rw [he] at hd
  have hinner : 5+4*Real.sqrt (β^2*(n:ℝ)/2+9*(L:ℝ)*(r^3)^2)/r^2+12*r^2 ≤
      (17+4*|β|+12*(L:ℝ))*r^2 := by nlinarith [sq_nonneg (r-1)]
  have hm := mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg L)
  change ((L:ℝ)*(5+4*Real.sqrt (β^2*(n:ℝ)/2+9*(L:ℝ)*(r^3)^2)/r^2+12*r^2))/r^3 ≤ _
  apply (div_le_iff₀ (pow_pos hrp 3)).mpr
  have he' : (((L:ℝ)*(17+4*|β|+12*(L:ℝ)))/r)*r^3=(L:ℝ)*((17+4*|β|+12*(L:ℝ))*r^2) := by field_simp
  rw [he']
  exact hm

lemma exists_mixed_root_amplitude {m n : ℕ} (hn : 0<n) (d : Fin (m+1) → ℕ) (β : ℝ) :
    ∃ x : Fin (m+1) → ℝ, (∀ k, x k∈Set.Icc (eighthRootScale n^3) (2*eighthRootScale n^3)) ∧
      ∀ (k : Fin (m+1)) (r : ℕ) (i : Fin r) (f : (Fin r → Configuration n) → ℝ),
      (∀ σ, |f σ|≤1) → |mixedGGDefect d β x k i f| ≤
      ((m+1:ℕ)*(17+4*|β|+12*(m+1:ℕ)))/eighthRootScale n := by
  have hh := one_le_eighthRootScale hn
  have hp : 0<eighthRootScale n := by linarith
  have hδs : eighthRootScale n^2 ≤ eighthRootScale n^3 := pow_le_pow_right₀ hh (by norm_num : 2≤3)
  obtain ⟨x, hx, h⟩ := exists_mixed_GG_amplitude hn d β (pow_pos hp 3) (pow_pos hp 2) hδs
  exact ⟨x, hx, fun k r i f hf => (h k r i f hf).trans (mixed_root_GG_bound hn (Nat.succ_pos m) β)⟩

end SKCavity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity

 

def allPowerRoot (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (eighthRootScale n))
def powerCutoff (n : ℕ) : ℕ := ⌊allPowerRoot n⌋₊

lemma allPowerRoot_nonneg (n : ℕ) : 0 ≤ allPowerRoot n := Real.sqrt_nonneg _
lemma allPowerRoot_pow_four (n : ℕ) : allPowerRoot n^4=eighthRootScale n := by
  have h1 := Real.sq_sqrt (Real.sqrt_nonneg (eighthRootScale n))
  have h2 := Real.sq_sqrt (eighthRootScale_nonneg n)
  change allPowerRoot n^2=Real.sqrt (eighthRootScale n) at h1
  calc
    allPowerRoot n^4=(allPowerRoot n^2)^2 := by ring
    _=eighthRootScale n := by rw [h1, h2]
lemma one_le_allPowerRoot {n : ℕ} (hn : 0<n) : 1 ≤ allPowerRoot n := by
  have h := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (one_le_eighthRootScale hn))
  simpa only [Real.sqrt_one, allPowerRoot] using h
lemma tendsto_allPowerRoot : Tendsto allPowerRoot atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_eighthRootScale)
lemma tendsto_powerCutoff : Tendsto powerCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp tendsto_allPowerRoot

lemma powerCutoff_cast_bound {n : ℕ} (hn : 0<n) : (powerCutoff n+1:ℕ) ≤ 2*allPowerRoot n := by
  have h := Nat.floor_le (allPowerRoot_nonneg n)
  have hh := one_le_allPowerRoot hn
  simp only [Nat.cast_add, Nat.cast_one]
  change (⌊allPowerRoot n⌋₊:ℝ)+1 ≤ 2*allPowerRoot n
  linarith

lemma allPower_GG_rate {n : ℕ} (hn : 0<n) (β : ℝ) :
    ((powerCutoff n+1:ℕ)*(17+4*|β|+12*(powerCutoff n+1:ℕ)))/eighthRootScale n ≤
      (82+8*|β|)/(allPowerRoot n^2) := by
  let q := allPowerRoot n
  let L : ℝ := (powerCutoff n+1:ℕ)
  have hq : 1 ≤ q := one_le_allPowerRoot hn
  have hqp : 0 < q := by linarith
  have hL : L ≤ 2*q := powerCutoff_cast_bound hn
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hc : 17+4*|β|+12*L ≤ (41+4*|β|)*q := by
    have ht := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 17+4*|β|)
    nlinarith only [ht, hL]
  have hm := mul_le_mul hL hc (by positivity : (0:ℝ) ≤ 17+4*|β|+12*L) (by positivity : (0:ℝ) ≤ 2*q)
  have he : (82+8*|β|)/q^2=((2*q)*((41+4*|β|)*q))/q^4 := by field_simp; ring
  change (L*(17+4*|β|+12*L))/eighthRootScale n ≤ _
  rw [← allPowerRoot_pow_four n]
  rw [show (82+8*|β|)/allPowerRoot n^2=((2*q)*((41+4*|β|)*q))/q^4 from he]
  exact div_le_div_of_nonneg_right hm (pow_nonneg hqp.le 4)

lemma allPower_amplitude_variance_density {n : ℕ} (hn : 0<n)
    (x : Fin (powerCutoff n+1) → ℝ)
    (hx : ∀ k, x k∈Set.Icc (eighthRootScale n^3) (2*eighthRootScale n^3)) :
    (∑ k, (x k)^2)/(n:ℝ) ≤ 8/(allPowerRoot n^7) := by
  let q := allPowerRoot n
  have hq : 1 ≤ q := one_le_allPowerRoot hn
  have hqp : 0<q := by linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => eighthRoot_amplitude_pressure_bound hn (hx k))
  rw [← Finset.sum_div] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hL := powerCutoff_cast_bound hn
  have hm := mul_le_mul_of_nonneg_right hL (show 0 ≤ 4/(eighthRootScale n^2) by positivity)
  have he : (2*q)*(4/(eighthRootScale n^2))=8/(q^7) := by
    rw [← allPowerRoot_pow_four n]
    change (2*q)*(4/((q^4)^2))=8/(q^7)
    field_simp
    ring
  exact hsum.trans (hm.trans_eq he)

end SKCavity

end

end OAI
