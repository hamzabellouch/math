import Mathlib
import OAI.Probability.ParisiFinite.Law
import OAI.Probability.ParisiFinite.SquareKernel

namespace OAI

/-! Average. -/

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace SKCavity
open SKQAOA SKGaussian

 
def average {ι : Type*} [Fintype ι] (x f : ι → ℝ) : ℝ := ∑ i, weight x i*f i

lemma average_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : 0 < average x f := by
  apply Finset.sum_pos (fun i _ => mul_pos (weight_pos x i) (hf i)) Finset.univ_nonempty

lemma partition_mul_average {ι : Type*} [Fintype ι] [Nonempty ι] (x f : ι → ℝ) :
    partition x * average x f = ∑ i, Real.exp (x i)*f i := by
  unfold average
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold weight
  field_simp [(partition_pos x).ne']

lemma log_average_exp {ι : Type*} [Fintype ι] [Nonempty ι] (x y : ι → ℝ) :
    Real.log (average x (fun i => Real.exp (y i))) =
      logPartition (fun i => x i+y i)-logPartition x := by
  have hp : partition (fun i => x i+y i)=partition x*average x (fun i => Real.exp (y i)) := by
    rw [partition_mul_average]
    simp [partition,Real.exp_add]
  rw [logPartition, hp, Real.log_mul (partition_pos x).ne'
    (average_pos x _ (fun i => Real.exp_pos _)).ne']
  simp [logPartition]

lemma restrictLeft_snoc {n : ℕ} (σ : Configuration n) (b : Bool) :
    restrictLeft (Fin.snoc σ b) = σ := by
  ext i
  change (Fin.snoc σ b : Configuration (n+1)) i.castSucc=σ i
  simp

 
def extend {n : ℕ} (x z : Configuration n → ℝ) (σ : Configuration (n+1)) : ℝ :=
  x (restrictLeft σ)+spin σ (Fin.last n)*z (restrictLeft σ)

lemma partition_extend {n : ℕ} (x z : Configuration n → ℝ) :
    partition (extend x z) = ∑ σ, Real.exp (x σ)*(2*Real.cosh (z σ)) := by
  classical
  let e : (Bool × Configuration n) ≃ Configuration (n+1) := Fin.snocEquiv (fun _ => Bool)
  rw [partition, ← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  change (∑ b : Bool, Real.exp (extend x z (Fin.snoc σ b)))=_
  simp only [Fintype.sum_bool, extend, restrictLeft_snoc, spin, Fin.snoc_last,
    Bool.false_eq_true, ite_true, ite_false]
  simp [Real.cosh_eq, Real.exp_add, Real.exp_neg]
  ring

lemma logPartition_extend {n : ℕ} (x z : Configuration n → ℝ) :
    logPartition (extend x z) = logPartition x+Real.log (average x (fun σ => 2*Real.cosh (z σ))) := by
  rw [logPartition, partition_extend, ← partition_mul_average,
    Real.log_mul (partition_pos x).ne' (average_pos x _ (fun σ => by positivity)).ne']
  rfl

 
def site (n : ℕ) (g : Fin n → ℝ) (σ : Configuration n) : ℝ :=
  cavityScale n * ∑ i, g i*spin σ i

def core (n : ℕ) (J : Disorder n) (σ : Configuration n) : ℝ :=
  coreScale n*hamiltonian n J σ

def correctionField (n : ℕ) (J : Disorder n) (σ : Configuration n) : ℝ :=
  cavityScale n*hamiltonian n J σ

lemma field_cavityCoeff (n : ℕ) (J : (Edge n ⊕ Fin n) → ℝ) :
    field (cavityCoeff n) J = extend (core n (fun e => J (Sum.inl e)))
      (site n (fun i => J (Sum.inr i))) := by
  ext σ
  simp only [field, cavityCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    extend, core, site, hamiltonian_eq_coeff, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma field_correctedCoeff (n : ℕ) (J : (Edge n ⊕ Edge n) → ℝ) :
    field (correctedCoeff n) J = fun σ => core n (fun e => J (Sum.inl e)) σ+
      correctionField n (fun e => J (Sum.inr e)) σ := by
  ext σ
  simp only [field, correctedCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    core, correctionField, hamiltonian_eq_coeff, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma extend_scale {n : ℕ} (β : ℝ) (x z : Configuration n → ℝ) :
    (fun σ => β*extend x z σ)=extend (fun σ => β*x σ) (fun σ => β*z σ) := by
  ext σ
  unfold extend
  ring

 
def cavityLog (n : ℕ) (β : ℝ) (J : (Edge n ⊕ Fin n) → ℝ) : ℝ :=
  Real.log (average (fun σ => β*core n (fun e => J (Sum.inl e)) σ)
    (fun σ => 2*Real.cosh (β*site n (fun i => J (Sum.inr i)) σ)))

 
def correctionLog (n : ℕ) (β : ℝ) (J : (Edge n ⊕ Edge n) → ℝ) : ℝ :=
  Real.log (average (fun σ => β*core n (fun e => J (Sum.inl e)) σ)
    (fun σ => Real.exp (β*correctionField n (fun e => J (Sum.inr e)) σ)))

lemma cavityLog_sub (n : ℕ) (β : ℝ) (J : (Edge n ⊕ Fin n) → ℝ) :
    cavityLog n β J = logPartition (fun σ => β*field (cavityCoeff n) J σ)-
      logPartition (fun σ => β*core n (fun e => J (Sum.inl e)) σ) := by
  rw [field_cavityCoeff, extend_scale, logPartition_extend]
  simp only [cavityLog, add_sub_cancel_left]

lemma correctionLog_sub (n : ℕ) (β : ℝ) (J : (Edge n ⊕ Edge n) → ℝ) :
    correctionLog n β J = logPartition (fun σ => β*field (correctedCoeff n) J σ)-
      logPartition (fun σ => β*core n (fun e => J (Sum.inl e)) σ) := by
  rw [field_correctedCoeff]
  simp only [mul_add]
  exact log_average_exp _ _
end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace SKCavity
open SKQAOA SKGaussian

 
def coreLift (n : ℕ) (κ : Type*) (β : ℝ) (σ : Configuration n) : Edge n ⊕ κ → ℝ :=
  Sum.elim (fun e => β*coreScale n*skCoeff n σ e) (fun _ => 0)

lemma field_coreLift (n : ℕ) {κ : Type*} [Fintype κ] (β : ℝ) (J : (Edge n ⊕ κ) → ℝ) :
    field (coreLift n κ β) J = fun σ => β*core n (fun e => J (Sum.inl e)) σ := by
  ext σ
  simp only [field, coreLift, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    zero_mul, Finset.sum_const_zero, add_zero, core, hamiltonian_eq_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma integrable_coreLift (n : ℕ) {κ : Type*} [Fintype κ] (β : ℝ) :
    Integrable (fun J : (Edge n ⊕ κ) → ℝ =>
      logPartition (fun σ => β*core n (fun e => J (Sum.inl e)) σ)) (gaussianLaw (Edge n ⊕ κ)) := by
  simp_rw [← field_coreLift]
  exact integrable_logPartition (fun σ => integrable_field _ σ)

lemma expected_coreLift (n : ℕ) {κ : Type*} [Fintype κ] (β : ℝ) :
    (∫ J : (Edge n ⊕ κ) → ℝ,
      logPartition (fun σ => β*core n (fun e => J (Sum.inl e)) σ) ∂gaussianLaw (Edge n ⊕ κ)) =
      pressure (β*coreScale n) n := by
  simp_rw [← field_coreLift]
  unfold coreLift
  rw [integral_field_inl]
  simp_rw [field_scale, field_skCoeff]
  rfl

lemma integrable_cavityLog (n : ℕ) (β : ℝ) :
    Integrable (cavityLog n β) (gaussianLaw (Edge n ⊕ Fin n)) := by
  have he : cavityLog n β = fun J => logPartition (fun σ => β*field (cavityCoeff n) J σ)-
    logPartition (fun σ => β*core n (fun e => J (Sum.inl e)) σ) := funext (cavityLog_sub n β)
  rw [he]
  exact (integrable_logPartition (fun σ => (integrable_field _ σ).const_mul β)).sub (integrable_coreLift n β)

lemma integrable_correctionLog (n : ℕ) (β : ℝ) :
    Integrable (correctionLog n β) (gaussianLaw (Edge n ⊕ Edge n)) := by
  have he : correctionLog n β = fun J => logPartition (fun σ => β*field (correctedCoeff n) J σ)-
      logPartition (fun σ => β*core n (fun e => J (Sum.inl e)) σ) := funext (correctionLog_sub n β)
  rw [he]
  exact (integrable_logPartition (fun σ => (integrable_field _ σ).const_mul β)).sub (integrable_coreLift n β)

lemma expected_cavityLog {n : ℕ} (hn : 0 < n) (β : ℝ) :
    (∫ J, cavityLog n β J ∂gaussianLaw (Edge n ⊕ Fin n)) =
      pressure β (n+1)-pressure (β*coreScale n) n := by
  simp_rw [cavityLog_sub]
  rw [integral_sub (integrable_logPartition (fun σ => (integrable_field _ σ).const_mul β))
    (integrable_coreLift n β), expected_cavity_pressure hn, expected_coreLift]

lemma expected_correctionLog (n : ℕ) (β : ℝ) :
    (∫ J, correctionLog n β J ∂gaussianLaw (Edge n ⊕ Edge n)) =
      pressure β n-pressure (β*coreScale n) n := by
  simp_rw [correctionLog_sub]
  rw [integral_sub (integrable_logPartition (fun σ => (integrable_field _ σ).const_mul β))
    (integrable_coreLift n β), expected_corrected_pressure, expected_coreLift]

 
def increment (β : ℝ) (n : ℕ) : ℝ :=
  (∫ J, cavityLog n β J ∂gaussianLaw (Edge n ⊕ Fin n))-
    ∫ J, correctionLog n β J ∂gaussianLaw (Edge n ⊕ Edge n)

 
lemma increment_eq {n : ℕ} (hn : 0 < n) (β : ℝ) :
    increment β n=pressure β (n+1)-pressure β n := by
  rw [increment, expected_cavityLog hn, expected_correctionLog]
  ring

lemma increment_lower {n : ℕ} (hn : 0 < n) (β : ℝ) :
    pressure β 1 ≤ increment β n := by
  rw [increment_eq hn]
  linarith [pressure_superadditive β n 1]
end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace SKCavity
open SKQAOA SKGaussian

 

lemma frequently_increment_le_of_slope {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun n => a n/(n:ℝ)) atTop (𝓝 L)) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n in atTop, a (n+1)-a n ≤ L+ε := by
  rw [frequently_atTop]
  intro N
  by_contra! h
  have hb (n : ℕ) (hn : N ≤ n) : a N+((n:ℝ)-N)*(L+ε) ≤ a n := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hh := h n hn
      push_cast
      linarith
  have hh : ∀ᶠ (n : ℕ) in atTop, (a N-(N:ℝ)*(L+ε))/(n:ℝ)+(L+ε) ≤ a n/(n:ℝ) := by
    filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hn hp
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hp
    apply (le_div_iff₀ hn').mpr
    have he : ((a N-(N:ℝ)*(L+ε))/(n:ℝ)+(L+ε))*(n:ℝ)=a N+((n:ℝ)-N)*(L+ε) := by
      field_simp
      ring
    rw [he]
    exact hb n hn
  have hc := (tendsto_const_div_atTop_nhds_zero_nat (a N-(N:ℝ)*(L+ε))).add_const (L+ε)
  have he := le_of_tendsto_of_tendsto hc ha hh
  simp only [zero_add] at he
  linarith

lemma tendsto_pressure_perSpin {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => pressure β n/(n:ℝ)) atTop (𝓝 (β*limitingFreeEnergy β)) := by
  have he (n : ℕ) : pressure β n/(n:ℝ)=β*freeEnergy β n := by
    unfold freeEnergy
    field_simp
  simp_rw [he]
  exact (tendsto_freeEnergy hβ).const_mul β

lemma frequently_cavity_upper {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n in atTop, increment β n ≤ β*limitingFreeEnergy β+ε := by
  have h := frequently_increment_le_of_slope (tendsto_pressure_perSpin hβ) hε
  apply (h.and_eventually (eventually_gt_atTop 0)).mono
  rintro n ⟨hn,hp⟩
  rwa [increment_eq hp]

lemma increment_bounded_below (β : ℝ) :
    IsBoundedUnder (fun x y : ℝ => y ≤ x) atTop (increment β) := by
  refine ⟨pressure β 1, ?_⟩
  change ∀ᶠ (n : ℕ) in atTop, pressure β 1 ≤ increment β n
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact increment_lower hn β

 

lemma limitingFreeEnergy_ge_cavity_liminf {β : ℝ} (hβ : 0 < β) :
    liminf (increment β) atTop ≤ β*limitingFreeEnergy β := by
  apply le_of_forall_pos_le_add
  intro ε hε
  exact liminf_le_of_frequently_le (frequently_cavity_upper hβ hε) (increment_bounded_below β)
end SKCavity

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

 
def replicaWeight {ι : Type*} [Fintype ι] {r : ℕ} (x : ι → ℝ) (σ : Fin r → ι) : ℝ :=
  ∏ l, weight x (σ l)

lemma replicaWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (x : ι → ℝ) (σ : Fin r → ι) : 0 ≤ replicaWeight x σ :=
  Finset.prod_nonneg (fun l _ => (weight_pos x (σ l)).le)

lemma replicaWeight_le_one {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (x : ι → ℝ) (σ : Fin r → ι) : replicaWeight x σ ≤ 1 :=
  Finset.prod_le_one₀ (fun l _ => (weight_pos x (σ l)).le) (fun l _ => weight_le_one x (σ l))

lemma sum_replicaWeight {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℕ) (x : ι → ℝ) :
    (∑ σ : Fin r → ι, replicaWeight x σ)=1 := by
  classical
  simp only [replicaWeight, ← Fintype.prod_sum, sum_weight, Finset.prod_const_one]

lemma continuous_replicaWeight {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℕ}
    (σ : Fin r → ι) : Continuous (fun x : ι → ℝ => replicaWeight x σ) := by
  unfold replicaWeight
  apply continuous_finsetProd
  intro l _
  exact continuous_weight (σ l)

 
def coreGibbs (n : ℕ) (β : ℝ) (J : Disorder n) : Configuration n → ℝ :=
  fun σ => β*core n J σ

lemma coreGibbs_eq_field (n : ℕ) (β : ℝ) (J : Disorder n) :
    coreGibbs n β J=field (fun σ e => β*coreScale n*skCoeff n σ e) J := by
  rw [field_scale,field_skCoeff]
  ext σ
  simp [coreGibbs, core, mul_assoc]

lemma continuous_coreGibbs (n : ℕ) (β : ℝ) : Continuous (coreGibbs n β) := by
  have he : coreGibbs n β=field (fun σ e => β*coreScale n*skCoeff n σ e) := funext (coreGibbs_eq_field n β)
  rw [he]
  exact continuous_field _

lemma integrable_replicaWeight (n r : ℕ) (β : ℝ) (σ : Fin r → Configuration n) :
    Integrable (fun J => replicaWeight (coreGibbs n β J) σ) (disorderLaw n) := by
  have : IsProbabilityMeasure (disorderLaw n) := by unfold disorderLaw; infer_instance
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_replicaWeight σ).comp (continuous_coreGibbs n β)).aestronglyMeasurable
  filter_upwards with J
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (replicaWeight_nonneg _ _)]
  exact replicaWeight_le_one _ _

 
def replicaMass (n r : ℕ) (β : ℝ) (σ : Fin r → Configuration n) : ℝ :=
  ∫ J, replicaWeight (coreGibbs n β J) σ ∂disorderLaw n

lemma replicaMass_nonneg (n r : ℕ) (β : ℝ) (σ : Fin r → Configuration n) :
    0 ≤ replicaMass n r β σ := integral_nonneg (fun _ => replicaWeight_nonneg _ _)

lemma sum_replicaMass (n r : ℕ) (β : ℝ) :
    (∑ σ : Fin r → Configuration n, replicaMass n r β σ)=1 := by
  have : IsProbabilityMeasure (disorderLaw n) := by unfold disorderLaw; infer_instance
  unfold replicaMass
  rw [← integral_finsetSum _ (fun σ _ => integrable_replicaWeight n r β σ)]
  simp only [sum_replicaWeight]
  simp

 
def finiteProbability {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (f : ι → Ω) : ProbabilityMeasure Ω :=
  ⟨∑ i, ENNReal.ofReal (p i) • Measure.dirac (f i), ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hs, ENNReal.ofReal_one]⟩⟩

lemma integral_finiteProbability {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) (f : ι → Ω) (g : Ω → ℝ) :
    (∫ x, g x ∂(finiteProbability p hp hs f : Measure Ω)) = ∑ i, p i*g (f i) := by
  change (∫ x, g x ∂∑ i, ENNReal.ofReal (p i) • Measure.dirac (f i))=_
  rw [integral_finsetSum_measure (fun i _ => (integrable_dirac (by finiteness)).smul_measure (by finiteness))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp i), smul_eq_mul]

 
def replicaLaw (n r : ℕ) (β : ℝ) : ProbabilityMeasure (Fin r → Configuration n) :=
  finiteProbability (replicaMass n r β) (replicaMass_nonneg n r β) (sum_replicaMass n r β) id

lemma integral_replicaLaw (n r : ℕ) (β : ℝ) (f : (Fin r → Configuration n) → ℝ) :
    (∫ σ, f σ ∂(replicaLaw n r β : Measure _)) =
      ∫ J, ∑ σ : Fin r → Configuration n, replicaWeight (coreGibbs n β J) σ*f σ ∂disorderLaw n := by
  rw [replicaLaw, integral_finiteProbability, integral_finsetSum _
    (fun σ _ => (integrable_replicaWeight n r β σ).mul_const (f σ))]
  simp only [integral_mul_const, replicaMass, id_eq]
end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

abbrev OverlapEntry := Set.Icc (-1 : ℝ) 1
abbrev OverlapArray := ℕ → ℕ → OverlapEntry

lemma abs_overlap_le_one {n : ℕ} (σ τ : Configuration n) : |overlap σ τ| ≤ 1 := by
  have hs : |overlapSum σ τ| ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ i, |spin σ i * spin τ i| := Finset.abs_sum_le_sum_abs _ _
      _ = n := by simp [abs_mul]
  by_cases hn : n=0
  · subst n; simp [overlap]
  · rw [overlap, abs_div, abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) by positivity)]
    exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr hs

lemma overlap_symm {n : ℕ} (σ τ : Configuration n) : overlap σ τ=overlap τ σ := by
  simp only [overlap, overlapSum, mul_comm]

lemma overlap_self {n : ℕ} (hn : 0<n) (σ : Configuration n) : overlap σ σ=1 := by
  simp only [overlap, overlapSum, ← sq, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

 

def extendReplicas {n r : ℕ} (σ : Fin (r+1) → Configuration n) (i : ℕ) : Configuration n :=
  if h : i<r+1 then σ ⟨i,h⟩ else σ 0

@[simp] lemma extendReplicas_eq {n r : ℕ} (σ : Fin (r+1) → Configuration n)
    (i : Fin (r+1)) : extendReplicas σ i=σ i := by simp [extendReplicas, i.isLt]

def configurationOverlap {n r : ℕ} (σ : Fin (r+1) → Configuration n) : OverlapArray :=
  fun i j => ⟨overlap (extendReplicas σ i) (extendReplicas σ j),
    (abs_le.mp (abs_overlap_le_one _ _))⟩

 

def overlapLaw (n : ℕ) (β : ℝ) : ProbabilityMeasure OverlapArray :=
  finiteProbability (replicaMass n (n+1) β) (replicaMass_nonneg n (n+1) β)
    (sum_replicaMass n (n+1) β) configurationOverlap

lemma integral_overlapLaw (n : ℕ) (β : ℝ) (f : OverlapArray → ℝ) :
    (∫ R, f R ∂(overlapLaw n β : Measure _)) =
      ∫ J, ∑ σ : Fin (n+1) → Configuration n,
        replicaWeight (coreGibbs n β J) σ * f (configurationOverlap σ) ∂disorderLaw n := by
  rw [overlapLaw, integral_finiteProbability, integral_finsetSum _
    (fun σ _ => (integrable_replicaWeight n (n+1) β σ).mul_const (f (configurationOverlap σ)))]
  simp only [integral_mul_const, replicaMass]

 

theorem exists_overlap_limit (β : ℝ) :
    ∃ μ : ProbabilityMeasure OverlapArray, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k => overlapLaw (φ k) β) atTop (𝓝 μ) := by
  exact CompactSpace.tendsto_subseq (fun n => overlapLaw n β)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma overlap_quadratic {n m : ℕ} (σ : Fin m → Configuration n) (c : Fin m → ℝ) :
    (∑ a, ∑ b, c a*c b*overlap (σ a) (σ b)) =
      (∑ i, (∑ a, c a*spin (σ a) i)^2)/(n:ℝ) := by
  have hi (i : Fin n) : (∑ a, ∑ b, c a*c b*(spin (σ a) i*spin (σ b) i))=
      (∑ a, c a*spin (σ a) i)^2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc
    _ = (∑ a, ∑ b, ∑ i, c a*c b*(spin (σ a) i*spin (σ b) i))/(n:ℝ) := by
      simp only [overlap, overlapSum, mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    _ = (∑ i, ∑ a, ∑ b, c a*c b*(spin (σ a) i*spin (σ b) i))/(n:ℝ) := by
      congr 1
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (f := fun a i => c a * c _ * (spin (σ a) i * spin (σ _) i))]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = _ := by simp_rw [hi]

 
def GramArrays : Set OverlapArray := {R |
  (∀ i j, R i j=R j i) ∧ (∀ i, (R i i : ℝ)=1) ∧
  ∀ (m : ℕ) (c : Fin m → ℝ), 0 ≤ ∑ a, ∑ b, c a*c b*(R a b : ℝ)}

lemma isClosed_GramArrays : IsClosed GramArrays := by
  unfold GramArrays
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter ?_
  exact isClosed_iInter fun m => isClosed_iInter fun c => isClosed_le continuous_const (by fun_prop)

lemma configurationOverlap_mem_Gram {n r : ℕ} (hn : 0<n)
    (σ : Fin (r+1) → Configuration n) : configurationOverlap σ ∈ GramArrays := by
  refine ⟨fun i j => Subtype.ext (overlap_symm _ _), fun i => overlap_self hn _, ?_⟩
  intro m c
  change 0 ≤ ∑ a, ∑ b, c a*c b*overlap (extendReplicas σ a) (extendReplicas σ b)
  rw [overlap_quadratic]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg n)

lemma finiteProbability_set_of_forall {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (f : ι → Ω)
    {s : Set Ω} (hf : ∀ i, f i ∈ s) : (finiteProbability p hp hs f : Measure Ω) s=1 := by
  change (∑ i, ENNReal.ofReal (p i) • Measure.dirac (f i)) s=1
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (hf _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hs, ENNReal.ofReal_one]

lemma overlapLaw_Gram {n : ℕ} (hn : 0<n) (β : ℝ) :
    (overlapLaw n β : Measure OverlapArray) GramArrays=1 :=
  finiteProbability_set_of_forall _ _ _ _ (configurationOverlap_mem_Gram hn)

lemma overlap_limit_Gram (β : ℝ) {μ : ProbabilityMeasure OverlapArray} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hμ : Tendsto (fun k => overlapLaw (φ k) β) atTop (𝓝 μ)) :
    (μ : Measure OverlapArray) GramArrays=1 := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_GramArrays
  have he : ∀ᶠ k in atTop, (overlapLaw (φ k) β : Measure OverlapArray) GramArrays=(1:ℝ≥0∞) :=
    (hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)).mono (fun _ hk => overlapLaw_Gram hk β)
  rw [limsup_congr he, limsup_const] at h
  exact le_antisymm (prob_le_one) h

 

theorem exists_Gram_overlap_limit (β : ℝ) :
    ∃ μ : ProbabilityMeasure OverlapArray, (μ : Measure _) GramArrays=1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => overlapLaw (φ k) β) atTop (𝓝 μ) := by
  obtain ⟨μ,φ,hφ,hμ⟩ := exists_overlap_limit β
  exact ⟨μ,overlap_limit_Gram β hφ hμ,φ,hφ,hμ⟩
end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 

omit [Nonempty ι] in
lemma tuple_partition (r : ℕ) (x : ι → ℝ) :
    partition (fun σ : Fin r → ι => ∑ l, x (σ l)) = ∏ _ : Fin r, partition x := by
  simp only [partition, Real.exp_sum]
  exact (Fintype.prod_sum (fun (_ : Fin r) (i : ι) => Real.exp (x i))).symm

omit [Nonempty ι] in
lemma replicaWeight_eq_weight {r : ℕ} (x : ι → ℝ) (σ : Fin r → ι) :
    replicaWeight x σ=weight (fun τ : Fin r → ι => ∑ l, x (τ l)) σ := by
  rw [weight, tuple_partition, Real.exp_sum]
  simp only [replicaWeight, weight, Finset.prod_div_distrib]

 
def tupleCoeff {d r : ℕ} (A : ι → Fin d → ℝ) (σ : Fin r → ι) (k : Fin d) : ℝ :=
  ∑ l, A (σ l) k

omit [Fintype ι] [Nonempty ι] in
lemma linearField_tupleCoeff {d r : ℕ} (A : ι → Fin d → ℝ) (z : Fin d → ℝ)
    (σ : Fin r → ι) : linearField (tupleCoeff A) z σ=∑ l, linearField A z (σ l) := by
  simp only [linearField, tupleCoeff, Finset.sum_mul]
  exact Finset.sum_comm

omit [Nonempty ι] in
lemma replicaWeight_tupleCoeff {d r : ℕ} (A : ι → Fin d → ℝ) (z : Fin d → ℝ)
    (σ : Fin r → ι) : weight (linearField (tupleCoeff A) z) σ=replicaWeight (linearField A z) σ := by
  have he : linearField (tupleCoeff A (r:=r)) z = fun τ => ∑ l, linearField A z (τ l) :=
    funext (linearField_tupleCoeff A z)
  rw [he]
  exact (replicaWeight_eq_weight _ _).symm

lemma integrable_linear_replicaWeight {d r : ℕ} (A : ι → Fin d → ℝ) (σ : Fin r → ι) :
    Integrable (fun z => replicaWeight (linearField A z) σ) (standardLaw d) := by
  simp_rw [← replicaWeight_tupleCoeff A]
  exact integrable_weight (tupleCoeff A) σ

lemma integrable_coord_replicaWeight {d r : ℕ} (A : ι → Fin d → ℝ)
    (σ : Fin r → ι) (k : Fin d) :
    Integrable (fun z => z k*replicaWeight (linearField A z) σ) (standardLaw d) := by
  simp_rw [← replicaWeight_tupleCoeff A]
  exact integrable_coord_weight (tupleCoeff A) σ k

 

lemma integral_coord_replicaWeight {d r : ℕ} (A : ι → Fin d → ℝ)
    (σ : Fin r → ι) (k : Fin d) :
    (∫ z, z k*replicaWeight (linearField A z) σ ∂standardLaw d) =
      ∫ z, replicaWeight (linearField A z) σ *
        ((∑ l, A (σ l) k)-(∑ τ : Fin r → ι,
          replicaWeight (linearField A z) τ * ∑ l, A (τ l) k)) ∂standardLaw d := by
  have h := integral_coord_weight (tupleCoeff A) σ k
  simp only [replicaWeight_tupleCoeff, tupleCoeff] at h
  exact h

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace GaussianConcentration
open SKGaussian ParisiInterpolation

lemma memLp_lipschitz {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] {L : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith L f) (hx : MemLp id 2 μ) : MemLp f 2 μ := by
  have hsub : LipschitzWith L (fun x => f x-f 0) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    simpa only [sub_sub_sub_cancel_right] using hf.norm_sub_le x y
  have h := hsub.comp_memLp (by simp) hx
  convert h.add (memLp_const (f 0)) using 1
  ext x
  simp

lemma memLp_standard_id (n : ℕ) : MemLp id 2 (standardLaw n) := by
  apply memLp_pi_iff.mpr
  intro i
  exact (memLp_id_gaussianReal (μ:=0) (v:=1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)

lemma standard_second_moment : (∫ z : ℝ, z^2 ∂gaussianReal 0 1)=1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
  rw [variance_id_gaussianReal] at h
  simpa using h.symm

 

lemma variance_lipschitz_real {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) :
    variance f (gaussianReal 0 1) ≤ (L:ℝ)^2 := by
  have hm := memLp_lipschitz hf (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
  have hs : variance f (gaussianReal 0 1)=variance (fun z => f z-f 0) (gaussianReal 0 1) :=
    (variance_sub_const hm.aestronglyMeasurable (f 0)).symm
  rw [hs]
  apply (variance_le_expectation_sq (hm.sub (memLp_const (f 0))).aestronglyMeasurable).trans
  have hj := integral_mono ((hm.sub (memLp_const (f 0))).integrable_sq)
    (((memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq).const_mul ((L:ℝ)^2))
    (fun z => by
      have h := hf.norm_sub_le z 0
      simp only [Real.norm_eq_abs, sub_zero] at h
      have hsq := sq_le_sq₀ (abs_nonneg (f z-f 0)) (by positivity : 0 ≤ (L:ℝ)*|z|) |>.mpr h
      simpa [mul_pow, sq_abs] using hsq)
  simpa only [Pi.pow_apply, id_eq, integral_const_mul, standard_second_moment, mul_one] using hj

 

def CoordinateLipschitz {n : ℕ} (c : Fin n → ℝ≥0) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y, |f x-f y| ≤ ∑ i, (c i:ℝ)*|x i-y i|

lemma CoordinateLipschitz.lipschitz {n : ℕ} {c : Fin n → ℝ≥0}
    {f : (Fin n → ℝ) → ℝ} (hf : CoordinateLipschitz c f) :
    LipschitzWith (∑ i,c i) f := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [Real.norm_eq_abs]
  apply (hf x y).trans
  calc
    _ ≤ ∑ i, (c i:ℝ)*‖x-y‖ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x-y) i)
        (c i).coe_nonneg)
    _ = _ := by simp [← Finset.sum_mul]

lemma CoordinateLipschitz.memLp {n : ℕ} {c : Fin n → ℝ≥0}
    {f : (Fin n → ℝ) → ℝ} (hf : CoordinateLipschitz c f) : MemLp f 2 (standardLaw n) :=
  memLp_lipschitz hf.lipschitz (memLp_standard_id n)

end GaussianConcentration

end

end OAI
