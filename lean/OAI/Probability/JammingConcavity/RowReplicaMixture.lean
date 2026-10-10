import Mathlib
import OAI.Probability.JammingConcavity.CascadePathCoordinates

namespace OAI

/-! Row Replica Mixture. -/

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
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

def cascadeFiniteReplicaLaw (ms : List ℝ) (r : ℕ) : Measure (Fin r → CascadePath ms.length) :=
  (cascadeReplicaLaw ms).map (fun x i => x i.val)

def rowReplicaMarkedLaw (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (μ : Measure (Fin r → CascadePath k)) :
    Measure ((Fin r → CascadePath k) × EuclideanSpace ℝ (Fin r)) :=
  (μ.prod ((Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance k d p₀ a))).prod
    (Measure.pi (fun _ : Fin r => gaussianReal 0 Δ)))).map
    (fun w => (w.1,rowReplicaResidualField k r w.1 w.2))

def RowReplicaMixtureStatement : Prop :=
  ∀ (ms : List ℝ) (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0),
    rowReplicaMarkedLaw ms.length r d p₀ Δ (cascadeFiniteReplicaLaw ms r) =
      gaussianAdjunctionMeasure r (rowReplicaResidualCovariance ms.length r d p₀ Δ)
        (cascadeFiniteReplicaLaw ms r)
end MicroscopicJamming

 
 

open MeasureTheory Set
open scoped NNReal BigOperators

namespace MicroscopicJamming

def FiniteRank {n : ℕ} (R : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, R i i=1) ∧ (∀ i j, R i j=R j i) ∧
  (∀ i j, 0 ≤ R i j ∧ R i j ≤ 1) ∧
  (∀ i j k, min (R i j) (R j k) ≤ R i k)

def rankBirth {n : ℕ} (R : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  ((Finset.univ.filter (fun i => i < j)).sup (fun i => (R i j).toNNReal) : ℝ≥0)

def rankLink {n : ℕ} (R : Fin n → Fin n → ℝ) (j : Fin n) (v : ℝ) (i : Fin n) : ℝ :=
  min (R i j) (max (rankBirth R j) v)

def rankInsert {n : ℕ} (R : Fin n → Fin n → ℝ) (j : Fin n) (v : ℝ) :
    Fin (n+1) → Fin (n+1) → ℝ :=
  Fin.lastCases (Fin.lastCases 1 (rankLink R j v))
    (fun i => Fin.lastCases (rankLink R j v i) (R i))

def rankCluster {n : ℕ} (R : Fin n → Fin n → ℝ) (i : Fin n) (m : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => m ≤ R i j)

def RPCRankInsertionStatement : Prop :=
  (∀ n (R : Fin n → Fin n → ℝ) (j : Fin n) (v : ℝ), FiniteRank R →
    v ∈ Set.Icc (0:ℝ) 1 → FiniteRank (rankInsert R j v)) ∧
  (∀ n, Continuous (fun z : (Fin n → Fin n → ℝ) × (Fin n × ℝ) =>
    rankInsert z.1 z.2.1 z.2.2)) ∧
  (∀ n (R : Fin n → Fin n → ℝ) (i : Fin n) (m : ℝ), FiniteRank R → 0 < m → m ≤ 1 →
    (∑ j : Fin n, (volume {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i}).toReal) /
      (n:ℝ) = ((rankCluster R i m).card-m)/(n:ℝ))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace MicroscopicJamming

abbrev RankSeed := (n : ℕ) → Fin (n+1) × ℝ

def rankInnovationLaw (n : ℕ) : Measure (Fin (n+1) × ℝ) :=
  (PMF.uniformOfFintype (Fin (n+1))).toMeasure.prod (volume.restrict (Set.Icc (0:ℝ) 1))

def rankSeedLaw : Measure RankSeed := Measure.infinitePi rankInnovationLaw

def rankGrowing : (n : ℕ) → RankSeed → Fin (n+1) → Fin (n+1) → ℝ
  | 0,_ => fun _ _ => 1
  | n+1,z => rankInsert (rankGrowing n z) (z n).1 (z n).2

def realizedRank (z : RankSeed) : ℕ → ℕ → ℝ := fun i j =>
  rankGrowing (max i j) z ⟨i,Nat.lt_succ_of_le (le_max_left _ _)⟩
    ⟨j,Nat.lt_succ_of_le (le_max_right _ _)⟩

def realizedRankLaw : Measure (ℕ → ℕ → ℝ) := rankSeedLaw.map realizedRank

def RPCRankRealizationStatement : Prop :=
  Continuous realizedRank ∧ IsProbabilityMeasure realizedRankLaw ∧
  (∀ n (z : RankSeed) (i j : Fin (n+1)), realizedRank z i j=rankGrowing n z i j) ∧
  (∀ᵐ U ∂realizedRankLaw, (∀ i, U i i=1) ∧ (∀ i j, U i j=U j i) ∧
    (∀ i j, 0 ≤ U i j ∧ U i j ≤ 1) ∧
    (∀ i j k, min (U i j) (U j k) ≤ U i k)) ∧
  realizedRankLaw.map (fun U => U 0 1) = volume.restrict (Set.Icc (0:ℝ) 1)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

abbrev RowRankSignature (r : ℕ) := Fin r → Fin r → ℕ

def cascadeGenealogySignature (k r : ℕ) (xs : Fin r → CascadePath k) : RowRankSignature r :=
  fun i j => cascadeSharedEdges k (xs i) (xs j)

def rankGenealogySignature (ms : List ℝ) (r : ℕ) (U : RankArray) : RowRankSignature r :=
  fun i j => if i=j then ms.length else rpcStepLevel ms (U i.val j.val)

def rowSignatureCovariance (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (s : RowRankSignature r) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => (p₀:ℝ) + (∑ a : Fin k, if a.val+1 ≤ s i j then (d a:ℝ) else 0) +
    if i=j then (Δ:ℝ) else 0

def RowRankGaussianStatement : Prop :=
  ∀ (ms : List ℝ), ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0),
    (rowReplicaMarkedLaw ms.length r d p₀ Δ (cascadeFiniteReplicaLaw ms r)).map
      (Prod.map (cascadeGenealogySignature ms.length r) id) =
      gaussianAdjunctionMeasure r (rowSignatureCovariance ms.length r d p₀ Δ)
        (realizedRankLaw.map (rankGenealogySignature ms r))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def replicaClip (L x : ℝ) : ℝ := max (-L) (min L x)

def replicaZ {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (G : Kernel Ω S) (V : Ω × S → ℝ) (ω : Ω) : ℝ :=
  ∫ x, Real.exp (V (ω,x)) ∂G ω

def replicaNum {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (G : Kernel Ω S) (V : Ω × S → ℝ) {r : ℕ}
    (B : Ω × (Fin r → S) → ℝ) (ω : Ω) : ℝ :=
  ∫ xs, B (ω,xs) * ∏ i : Fin r, Real.exp (V (ω,xs i))
    ∂Measure.pi (fun _ : Fin r => G ω)

def ReplicaTruncationStatement : Prop :=
  ∀ (Ω S : ℕ → Type) (_mΩ : ∀ n, MeasurableSpace (Ω n))
    (_mS : ∀ n, MeasurableSpace (S n)),
  ∀ (ν : ∀ n, Measure (Ω n)) (G : ∀ n, Kernel (Ω n) (S n)),
    (∀ n, IsProbabilityMeasure (ν n)) → (∀ n, IsMarkovKernel (G n)) →
  ∀ (V : ∀ n, Ω n × S n → ℝ), (∀ n, Measurable (V n)) →
    (∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ n,
      Integrable (fun z => Real.exp (a * |V n z|)) ((ν n) ⊗ₘ (G n)) ∧
      (∫ z, Real.exp (a * |V n z|) ∂((ν n) ⊗ₘ (G n))) ≤ C) →
  ∀ (r : ℕ) (B : ∀ n, Ω n × (Fin r → S n) → ℝ),
    (∀ n, Measurable (B n)) →
    (∃ K : ℝ, ∀ n z, |B n z| ≤ K) →
    (∀ (L k : ℕ), CauchySeq (fun n =>
      ∫ ω, (replicaZ (G n) (fun z => replicaClip (L+1) (V n z)) ω)^k ∂ν n)) →
    (∀ (L k : ℕ), CauchySeq (fun n =>
      ∫ ω, replicaNum (G n) (fun z => replicaClip (L+1) (V n z)) (B n) ω *
        (replicaZ (G n) (fun z => replicaClip (L+1) (V n z)) ω)^k ∂ν n)) →
    (∃ ℓ : ℝ, Tendsto (fun n => ∫ ω, Real.log (replicaZ (G n) (V n) ω) ∂ν n)
      atTop (𝓝 ℓ)) ∧
    (∃ b : ℝ, Tendsto (fun n => ∫ ω,
      replicaNum (G n) (V n) (B n) ω / (replicaZ (G n) (V n) ω)^r ∂ν n)
      atTop (𝓝 b))
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MicroscopicJamming

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def gibbsZ (μ : Measure X) (B : X → ℝ) : ℝ := ∫ x, Real.exp (B x) ∂μ
def gibbsMean (μ : Measure X) (B f : X → ℝ) : ℝ :=
  (∫ x, f x * Real.exp (B x) ∂μ) / gibbsZ μ B

lemma integrable_exp_bounded {B : X → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : ∀ x, B x ≤ K) : Integrable (fun x => Real.exp (B x)) μ := by
  apply (integrable_const (Real.exp K)).mono' hB.exp.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hK x)

lemma gibbsZ_pos {B : X → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : ∀ x, B x ≤ K) : 0 < gibbsZ μ B :=
  integral_exp_pos (integrable_exp_bounded (μ := μ) hB hK)

omit [IsProbabilityMeasure μ] in
lemma gibbsMean_eq_integral_tilted [IsProbabilityMeasure μ] (B f : X → ℝ) :
    gibbsMean μ B f = ∫ x, f x ∂μ.tilted B := by
  rw [integral_tilted, gibbsMean, gibbsZ, ← integral_div]
  congr 1
  ext x
  simp only [smul_eq_mul]
  ring

lemma gibbsMean_const {B : X → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : ∀ x, B x ≤ K) (c : ℝ) : gibbsMean μ B (fun _ => c) = c := by
  let := isProbabilityMeasure_tilted (integrable_exp_bounded (μ := μ) hB hK)
  rw [gibbsMean_eq_integral_tilted]
  simp

lemma gibbsMean_abs_le {B f : X → ℝ} (hB : Measurable B) (hf : Measurable f)
    {K C : ℝ} (hK : ∀ x, B x ≤ K) (hC : ∀ x, |f x| ≤ C) :
    |gibbsMean μ B f| ≤ C := by
  let := isProbabilityMeasure_tilted (integrable_exp_bounded (μ := μ) hB hK)
  rw [gibbsMean_eq_integral_tilted]
  have hm : Integrable f (μ.tilted B) :=
    (MemLp.of_bound (p := (1:ℝ≥0∞)) hf.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)).integrable le_rfl
  calc
    |∫ x, f x ∂μ.tilted B| ≤ ∫ x, |f x| ∂μ.tilted B := abs_integral_le_integral_abs
    _ ≤ ∫ _ : X, C ∂μ.tilted B := integral_mono hm.norm (integrable_const _) hC
    _ = C := by simp

lemma integrable_gibbs_moment {B f : X → ℝ} (hB : Measurable B) (hf : Measurable f)
    {K C : ℝ} (hK : ∀ x, B x ≤ K) (hC : ∀ x, |f x| ≤ C) :
    Integrable (fun x => f x * Real.exp (B x)) μ := by
  apply (integrable_const (C*Real.exp K)).mono' (hf.mul hB.exp).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hC x) (Real.exp_le_exp.mpr (hK x))
      (Real.exp_pos _).le ((abs_nonneg _).trans (hC x))

 

lemma hasDerivAt_gibbs_moment {B h f : X → ℝ}
    (hB : Measurable B) (hh : Measurable h) (hf : Measurable f)
    {KB KH KF : ℝ} (hKB : ∀ x, B x ≤ KB) (hKH : ∀ x, |h x| ≤ KH)
    (hKF : ∀ x, |f x| ≤ KF) (z : ℝ) :
    HasDerivAt (fun t => ∫ x, f x * Real.exp (B x+t*h x) ∂μ)
      (∫ x, f x*h x*Real.exp (B x+z*h x) ∂μ) z := by
  have hKH0 : 0 ≤ KH := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure μ
    exact (abs_nonneg (h x)).trans (hKH x)
  have hKF0 : 0 ≤ KF := by
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure μ
    exact (abs_nonneg (f x)).trans (hKF x)
  have hpot (t : ℝ) (x : X) : B x+t*h x ≤ KB+|t| *KH := by
    calc
      _ ≤ KB+|t*h x| := add_le_add (hKB x) (le_abs_self _)
      _ ≤ _ := by rw [abs_mul]; gcongr; exact hKH x
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Metric.ball z 1) (bound := fun _ => KF*KH*Real.exp (KB+(|z| +1)*KH))
    (Metric.ball_mem_nhds z zero_lt_one)
    (Filter.Eventually.of_forall fun t => (hf.mul (hB.add (hh.const_mul t)).exp).aestronglyMeasurable)
    (integrable_gibbs_moment (hB.add (hh.const_mul z)) hf (hpot z) hKF)
    ((hf.mul hh).mul (hB.add (hh.const_mul z)).exp).aestronglyMeasurable
    ?_ (integrable_const _) ?_).2
  · exact ae_of_all _ fun x t ht => by
      have ht' : |t| ≤ |z| +1 := by
        have htz : |t-z| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
        have htri := abs_add_le (t-z) z
        simp only [sub_add_cancel] at htri
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (mul_le_mul (hKF x) (hKH x) (abs_nonneg _) hKF0)
        (Real.exp_le_exp.mpr ((hpot t x).trans ?_)) (Real.exp_pos _).le
        (mul_nonneg hKF0 hKH0)
      gcongr
  · exact ae_of_all _ fun x t _ => by
      convert ((((hasDerivAt_id t).mul_const (h x)).const_add (B x)).exp).const_mul (f x) using 1 <;>
        norm_num [id_eq]
      ring

lemma hasDerivAt_gibbsZ {B h : X → ℝ}
    (hB : Measurable B) (hh : Measurable h)
    {KB KH : ℝ} (hKB : ∀ x, B x ≤ KB) (hKH : ∀ x, |h x| ≤ KH) (z : ℝ) :
    HasDerivAt (fun t => gibbsZ μ (fun x => B x+t*h x))
      (∫ x, h x*Real.exp (B x+z*h x) ∂μ) z := by
  simpa only [gibbsZ, one_mul] using
    hasDerivAt_gibbs_moment (μ := μ) hB hh measurable_const hKB hKH
      (fun _ => (show |(1:ℝ)| ≤ 1 by norm_num)) z

lemma hasDerivAt_log_gibbsZ {B h : X → ℝ}
    (hB : Measurable B) (hh : Measurable h)
    {KB KH : ℝ} (hKB : ∀ x, B x ≤ KB) (hKH : ∀ x, |h x| ≤ KH) (z : ℝ) :
    HasDerivAt (fun t => Real.log (gibbsZ μ (fun x => B x+t*h x)))
      (gibbsMean μ (fun x => B x+z*h x) h) z := by
  have hp : ∀ x, B x+z*h x ≤ KB+|z| *KH := by
    intro x
    calc
      _ ≤ KB+|z*h x| := add_le_add (hKB x) (le_abs_self _)
      _ ≤ _ := by rw [abs_mul]; gcongr; exact hKH x
  exact (hasDerivAt_gibbsZ hB hh hKB hKH z).log
    (gibbsZ_pos (hB.add (hh.const_mul z)) hp).ne'

lemma hasDerivAt_gibbsMean {B h f : X → ℝ}
    (hB : Measurable B) (hh : Measurable h) (hf : Measurable f)
    {KB KH KF : ℝ} (hKB : ∀ x, B x ≤ KB) (hKH : ∀ x, |h x| ≤ KH)
    (hKF : ∀ x, |f x| ≤ KF) (z : ℝ) :
    HasDerivAt (fun t => gibbsMean μ (fun x => B x+t*h x) f)
      (gibbsMean μ (fun x => B x+z*h x) (fun x => f x*h x) -
        gibbsMean μ (fun x => B x+z*h x) f *
        gibbsMean μ (fun x => B x+z*h x) h) z := by
  have hp : ∀ x, B x+z*h x ≤ KB+|z| *KH := by
    intro x
    calc
      _ ≤ KB+|z*h x| := add_le_add (hKB x) (le_abs_self _)
      _ ≤ _ := by rw [abs_mul]; gcongr; exact hKH x
  have hz := (gibbsZ_pos (μ := μ) (hB.add (hh.const_mul z)) hp).ne'
  have hd := (hasDerivAt_gibbs_moment (μ := μ) hB hh hf hKB hKH hKF z).div
    (hasDerivAt_gibbsZ (μ := μ) hB hh hKB hKH z) hz
  apply hd.congr_deriv
  have halg (a b c d : ℝ) : (a*d-b*c)/d^2 = a/d - b/d*(c/d) := by
    by_cases hd : d = 0
    · simp [hd]
    · field_simp
  exact halg _ _ _ _

 

lemma continuous_gibbs_moment {m : ℕ} {B f : X → ℝ} {h : Fin m → X → ℝ}
    (hB : Measurable B) (hf : Measurable f) (hh : ∀ i, Measurable (h i))
    {KB KF KH : ℝ} (hKB : ∀ x, B x ≤ KB) (hKF : ∀ x, |f x| ≤ KF)
    (hKH : ∀ i x, |h i x| ≤ KH) (_hKH0 : 0 ≤ KH) :
    Continuous (fun a : Fin m → ℝ => ∫ x, f x *
      Real.exp (B x+∑ i, a i*h i x) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply continuousAt_of_dominated
    (bound := fun _ => KF * Real.exp (KB+(∑ i : Fin m, (|a i|+1))*KH))
  · exact Filter.Eventually.of_forall fun b =>
      (hf.mul (hB.add (Finset.measurable_sum _ fun i _ => (hh i).const_mul (b i))).exp).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds a zero_lt_one] with b hb
    apply ae_of_all
    intro x
    have hb' (i : Fin m) : |b i| ≤ |a i|+1 := by
      have hd : |b i-a i| < 1 := by
        have := (dist_pi_lt_iff zero_lt_one).mp hb i
        simpa only [Real.dist_eq] using this
      have ht := abs_add_le (b i-a i) (a i)
      simp only [sub_add_cancel] at ht
      linarith
    have hpot : B x+∑ i, b i*h i x ≤ KB+(∑ i : Fin m, (|a i|+1))*KH := by
      rw [Finset.sum_mul]
      apply add_le_add (hKB x)
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ |b i*h i x| := le_abs_self _
        _ = |b i| * |h i x| := abs_mul _ _
        _ ≤ (|a i|+1)*KH := mul_le_mul (hb' i) (hKH i x) (abs_nonneg _) (by positivity)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hKF x) (Real.exp_le_exp.mpr hpot) (Real.exp_pos _).le
      ((abs_nonneg _).trans (hKF x))
  · exact integrable_const _
  · exact ae_of_all _ fun x => by
      have hs : Continuous (fun a : Fin m → ℝ => B x+∑ i, a i*h i x) :=
        continuous_const.add (continuous_finsetSum _ fun i _ =>
          (continuous_apply i).mul continuous_const)
      exact (continuous_const.mul (Real.continuous_exp.comp hs)).continuousAt

lemma continuous_gibbsMean {m : ℕ} {B f : X → ℝ} {h : Fin m → X → ℝ}
    (hB : Measurable B) (hf : Measurable f) (hh : ∀ i, Measurable (h i))
    {KB KF KH : ℝ} (hKB : ∀ x, B x ≤ KB) (hKF : ∀ x, |f x| ≤ KF)
    (hKH : ∀ i x, |h i x| ≤ KH) (hKH0 : 0 ≤ KH) :
    Continuous (fun a : Fin m → ℝ => gibbsMean μ
      (fun x => B x+∑ i, a i*h i x) f) := by
  apply (continuous_gibbs_moment hB hf hh hKB hKF hKH hKH0).div
    (by
      simpa only [gibbsZ, one_mul] using
        (continuous_gibbs_moment (μ := μ) hB measurable_const hh hKB
          (fun _ => (show |(1:ℝ)| ≤ 1 by norm_num)) hKH hKH0))
  intro a
  apply (gibbsZ_pos (μ := μ)
    (hB.add (Finset.measurable_sum _ fun i _ => (hh i).const_mul (a i)))
    (K := KB+∑ i, |a i| *KH) ?_).ne'
  intro x
  apply add_le_add (hKB x)
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ |a i*h i x| := le_abs_self _
    _ = |a i| * |h i x| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hKH i x) (abs_nonneg _)

lemma log_gibbsZ_abs_le {B : X → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : ∀ x, |B x| ≤ K) : |Real.log (gibbsZ μ B)| ≤ K := by
  have hi := integrable_exp_bounded (μ := μ) hB (fun x => (hK x).trans' (le_abs_self _))
  have hz := gibbsZ_pos (μ := μ) hB (fun x => (hK x).trans' (le_abs_self _))
  apply abs_le.mpr
  constructor
  · apply (Real.le_log_iff_exp_le hz).mpr
    have hh := integral_mono (integrable_const (Real.exp (-K))) hi
      (fun x => Real.exp_le_exp.mpr (abs_le.mp (hK x)).1)
    simpa [gibbsZ] using hh
  · apply (Real.log_le_iff_le_exp hz).mpr
    have hh := integral_mono hi (integrable_const (Real.exp K))
      (fun x => Real.exp_le_exp.mpr (abs_le.mp (hK x)).2)
    simpa [gibbsZ] using hh

lemma gibbsMean_sq_le {B f : X → ℝ} (hB : Measurable B) (hf : Measurable f)
    {K C : ℝ} (hK : ∀ x, B x ≤ K) (hC : ∀ x, |f x| ≤ C) :
    (gibbsMean μ B f)^2 ≤ gibbsMean μ B (fun x => (f x)^2) := by
  let := isProbabilityMeasure_tilted (integrable_exp_bounded (μ := μ) hB hK)
  have hm : MemLp f 2 (μ.tilted B) :=
    MemLp.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  simp only [gibbsMean_eq_integral_tilted]
  have hh := variance_nonneg f (μ.tilted B)
  rw [variance_eq_sub hm] at hh
  simp only [Pi.pow_apply] at hh
  linarith

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def replicaPotential (B : X → ℝ) (k : ℕ) (y : Fin k → X) : ℝ := ∑ r, B (y r)

lemma gibbsZ_replicas (B : X → ℝ) (k : ℕ) :
    gibbsZ (Measure.pi fun _ : Fin k => μ) (replicaPotential B k) =
      ∏ _ : Fin k, gibbsZ μ B := by
  simp only [gibbsZ, replicaPotential, Real.exp_sum]
  exact integral_fintype_prod_eq_prod (μ := fun _ : Fin k => μ)
    (fun _ : Fin k => fun x : X => Real.exp (B x))

lemma tilted_replicas (B : X → ℝ) (k : ℕ) :
    (Measure.pi fun _ : Fin k => μ).tilted (replicaPotential B k) =
      Measure.pi (fun _ : Fin k => μ.tilted B) := by
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs)]
  simp_rw [tilted_apply_eq_ofReal_integral' _ (hs _)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun r _ =>
    integral_nonneg fun _ => div_nonneg (Real.exp_pos _).le
      (integral_nonneg fun _ => (Real.exp_pos _).le))]
  apply congrArg ENNReal.ofReal
  change (∫ y in Set.univ.pi s, Real.exp (replicaPotential B k y) /
    gibbsZ (Measure.pi fun _ : Fin k => μ) (replicaPotential B k)
      ∂Measure.pi (fun _ : Fin k => μ)) = _
  rw [gibbsZ_replicas, Measure.restrict_pi_pi]
  simp only [replicaPotential, Real.exp_sum, ← Finset.prod_div_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun r : Fin k => μ.restrict (s r))
    (fun _ : Fin k => fun x : X => Real.exp (B x) / gibbsZ μ B)

lemma gibbsMean_replicas_eq (B : X → ℝ) (k : ℕ) (F : (Fin k → X) → ℝ) :
    gibbsMean (Measure.pi fun _ : Fin k => μ) (replicaPotential B k) F =
      ∫ y, F y ∂Measure.pi (fun _ : Fin k => μ.tilted B) := by
  rw [gibbsMean_eq_integral_tilted, tilted_replicas]

lemma measurePreserving_snoc (ν : Measure X) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (fun p : X × (Fin k → X) => Fin.snoc p.2 p.1)
      (ν.prod (Measure.pi fun _ : Fin k => ν)) (Measure.pi fun _ : Fin (k+1) => ν) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last'] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => ν) (Fin.last k)).symm

lemma integral_replicas_mul_last (ν : Measure X) [IsProbabilityMeasure ν] (k : ℕ)
    {F : (Fin k → X) → ℝ} {f : X → ℝ} (hF : Measurable F) (hf : Measurable f) :
    (∫ y : Fin (k+1) → X, F (fun r : Fin k => y r.castSucc) * f (y (Fin.last k))
      ∂Measure.pi (fun _ => ν)) =
      (∫ y : Fin k → X, F y ∂Measure.pi (fun _ => ν)) * ∫ x, f x ∂ν := by
  have hp := measurePreserving_snoc ν k
  rw [← hp.map_eq]
  erw [integral_map hp.measurable.aemeasurable
    ((hF.comp (Measurable.of_eval fun r => measurable_pi_apply r.castSucc)).mul
      (hf.comp (measurable_pi_apply _))).aestronglyMeasurable]
  simp only [Pi.mul_apply, Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [mul_comm (F _) (f _)]
  rw [integral_prod_mul]
  ring

lemma integral_replicas_init (ν : Measure X) [IsProbabilityMeasure ν] (k : ℕ)
    {F : (Fin k → X) → ℝ} (hF : Measurable F) :
    (∫ y : Fin (k+1) → X, F (fun r : Fin k => y r.castSucc)
      ∂Measure.pi (fun _ => ν)) = ∫ y : Fin k → X, F y ∂Measure.pi (fun _ => ν) := by
  simpa using
    integral_replicas_mul_last ν k hF (measurable_const (a := (1:ℝ)))

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

def replicaKernel (G : Kernel Ω S) : (r : ℕ) → Kernel Ω (Fin r → S)
  | 0 => Kernel.const Ω (Measure.dirac (fun i => Fin.elim0 i))
  | r+1 => (G.prod (replicaKernel G r)).map (fun p => Fin.snoc p.2 p.1)

lemma measurable_replica_snoc (r : ℕ) :
    Measurable (fun p : S × (Fin r → S) => (Fin.snoc p.2 p.1 : Fin (r+1) → S)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (measurable_fst : Measurable (@Prod.fst S (Fin r → S)))
  · simp only [Fin.snoc_castSucc]
    fun_prop

lemma replicaKernel_apply (G : Kernel Ω S) [IsMarkovKernel G] (r : ℕ) (ω : Ω) :
    replicaKernel G r ω = Measure.pi (fun _ : Fin r => G ω) := by
  induction r generalizing ω with
  | zero =>
    simp only [replicaKernel,Kernel.const_apply]
    exact (Measure.pi_of_empty _ _).symm
  | succ r ih =>
    have hprev := ih
    have : IsMarkovKernel (replicaKernel G r) := ⟨fun ω => by rw [hprev ω]; infer_instance⟩
    rw [replicaKernel,Kernel.map_apply _ (measurable_replica_snoc r),Kernel.prod_apply,hprev ω]
    exact (measurePreserving_snoc (G ω) r).map_eq

instance (G : Kernel Ω S) [IsMarkovKernel G] (r : ℕ) : IsMarkovKernel (replicaKernel G r) :=
  ⟨fun ω => by rw [replicaKernel_apply]; infer_instance⟩

lemma measurable_replicaZ (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V) : Measurable (replicaZ G V) :=
  hV.exp.stronglyMeasurable.integral_kernel_prod_right.measurable

lemma measurable_replicaNum (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V) {r : ℕ}
    {B : Ω × (Fin r → S) → ℝ} (hB : Measurable B) : Measurable (replicaNum G V B) := by
  have hm : Measurable (fun z : Ω × (Fin r → S) =>
      B z * ∏ i, Real.exp (V (z.1,z.2 i))) :=
    hB.mul (Finset.measurable_prod _ fun i _ =>
      (hV.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).exp)
  have hh := hm.stronglyMeasurable.integral_kernel_prod_right (κ := replicaKernel G r)
    (f := fun ω xs => B (ω,xs)*∏ i, Real.exp (V (ω,xs i)))
  change Measurable (fun ω => ∫ xs, B (ω,xs)*∏ i, Real.exp (V (ω,xs i))
    ∂Measure.pi (fun _ : Fin r => G ω))
  simpa only [replicaKernel_apply] using hh.measurable

lemma measurable_replicaExpMoment (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V) (a : ℝ) :
    Measurable (fun ω => ∫ x, Real.exp (a*|V (ω,x)|) ∂G ω) :=
  (hV.abs.const_mul a).exp.stronglyMeasurable.integral_kernel_prod_right.measurable
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma pointCloud_position_preserving {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (n j : ℕ) :
    MeasurePreserving (fun ω : PointCloud A => ((ω n).2 j).1) (pointCloudLaw ν) cloudUniform := by
  have h₁ := measurePreserving_eval_infinitePi (fun _ : ℕ => poissonBinLaw (cloudUniform.prod ν)) n
  have h₂ : MeasurePreserving Prod.snd (poissonBinLaw (cloudUniform.prod ν))
      (Measure.infinitePi (fun _ : ℕ => cloudUniform.prod ν)) := measurePreserving_snd
  have h₃ := measurePreserving_eval_infinitePi (fun _ : ℕ => cloudUniform.prod ν) j
  have h₄ : MeasurePreserving Prod.fst (cloudUniform.prod ν) cloudUniform := measurePreserving_fst
  exact h₄.comp (h₃.comp (h₂.comp h₁))

lemma pointCloud_samebin_pair_preserving {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (n : ℕ) {i j : ℕ} (hij : i ≠ j) :
    MeasurePreserving (fun ω : PointCloud A => (((ω n).2 i).1, ((ω n).2 j).1))
      (pointCloudLaw ν) (cloudUniform.prod cloudUniform) := by
  have h₁ := measurePreserving_eval_infinitePi (fun _ : ℕ => poissonBinLaw (cloudUniform.prod ν)) n
  have h₂ : MeasurePreserving Prod.snd (poissonBinLaw (cloudUniform.prod ν))
      (Measure.infinitePi (fun _ : ℕ => cloudUniform.prod ν)) := measurePreserving_snd
  have h₃ : MeasurePreserving (fun y : ℕ → ℝ × A => (y i,y j))
      (Measure.infinitePi (fun _ : ℕ => cloudUniform.prod ν))
      ((cloudUniform.prod ν).prod (cloudUniform.prod ν)) :=
    ⟨by fun_prop, Measure.infinitePi_map_eval_prod hij⟩
  have h₄ : MeasurePreserving Prod.fst (cloudUniform.prod ν) cloudUniform := measurePreserving_fst
  exact (h₄.prod h₄).comp (h₃.comp (h₂.comp h₁))

lemma pointCloud_positions_ae {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂pointCloudLaw ν, ∀ n j, ((ω n).2 j).1 ∈ Set.Ico (0:ℝ) 1 := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro j
  exact (pointCloud_position_preserving ν n j).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Ico)

lemma pointCloud_samebin_distinct_ae {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂pointCloudLaw ν, ∀ n i j, i ≠ j → ((ω n).2 i).1 ≠ ((ω n).2 j).1 := by
  let : NullSingletonClass cloudUniform := by
    unfold cloudUniform
    infer_instance
  have hprod : ∀ᵐ z ∂cloudUniform.prod cloudUniform, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Eventually.of_forall fun x => (cloudUniform.ae_ne x).mono fun y hy => Ne.symm hy
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro i
  rw [ae_all_iff]; intro j
  by_cases hij : i = j
  · exact Eventually.of_forall fun ω h => (h hij).elim
  · exact ((pointCloud_samebin_pair_preserving ν n hij).quasiMeasurePreserving.ae hprod).mono
      fun ω h _ => h

lemma cloudLabelPoint_injective_ae {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂pointCloudLaw ν, Function.Injective (cloudLabelPoint ω) := by
  filter_upwards [pointCloud_positions_ae ν, pointCloud_samebin_distinct_ae ν] with ω hpos hdist
  rintro ⟨n,i⟩ ⟨m,j⟩ he
  have hx : (n:ℝ)+((ω n).2 i).1 = (m:ℝ)+((ω m).2 j).1 := congrArg Prod.fst he
  have hn := hpos n i
  have hm := hpos m j
  have hnm : n = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hc : (n:ℝ)+1 ≤ m := by exact_mod_cast h
      linarith [hn.1, hn.2, hm.1, hm.2]
    · have hc : (m:ℝ)+1 ≤ n := by exact_mod_cast h
      linarith [hn.1, hn.2, hm.1, hm.2]
  subst m
  have hij : i = j := by
    by_contra hne
    exact hdist n i j hne (by linarith)
  subst j
  rfl
end MicroscopicJamming

end

end OAI
