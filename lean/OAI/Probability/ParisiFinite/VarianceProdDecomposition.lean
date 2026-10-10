import Mathlib
import OAI.Probability.ParisiFinite.Average

namespace OAI

/-! Variance Prod Decomposition. -/

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
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace GaussianConcentration
open SKGaussian ParisiInterpolation

 
lemma variance_prod_decomposition {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : E × F → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (hs : ∀ y, MemLp (fun x => f (x,y)) 2 μ)
    (hm : MemLp (fun y => ∫ x, f (x,y) ∂μ) 2 ν) :
    variance f (μ.prod ν) = (∫ y, variance (fun x => f (x,y)) μ ∂ν)+
      variance (fun y => ∫ x, f (x,y) ∂μ) ν := by
  have he (y : F) : variance (fun x => f (x,y)) μ=
      (∫ x, f (x,y)^2 ∂μ)-(∫ x, f (x,y) ∂μ)^2 := variance_eq_sub (hs y)
  simp_rw [he]
  rw [variance_eq_sub hf, variance_eq_sub hm,
    integral_sub hf.integrable_sq.integral_prod_right hm.integrable_sq]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hf.integrable_sq,
    integral_prod_symm _ (hf.integrable (by norm_num))]
  ring

def firstMean {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∫ z, f (Fin.cons z y) ∂gaussianReal 0 1

lemma CoordinateLipschitz.first_slice {n : ℕ} {c : Fin (n+1) → ℝ≥0}
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : CoordinateLipschitz c f) (y : Fin n → ℝ) :
    LipschitzWith (c 0) (fun z => f (Fin.cons z y)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro z w
  simpa [Fin.sum_univ_succ, Real.norm_eq_abs] using hf (Fin.cons z y) (Fin.cons w y)

lemma CoordinateLipschitz.firstMean {n : ℕ} {c : Fin (n+1) → ℝ≥0}
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : CoordinateLipschitz c f) :
    CoordinateLipschitz (fun i => c i.succ) (firstMean f) := by
  intro x y
  have hmx := memLp_lipschitz (hf.first_slice x) (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
  have hmy := memLp_lipschitz (hf.first_slice y) (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
  have hix := hmx.integrable (by norm_num)
  have hiy := hmy.integrable (by norm_num)
  unfold GaussianConcentration.firstMean
  rw [← integral_sub hix hiy]
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono (hix.sub hiy).abs
    (integrable_const (∑ i, (c i.succ:ℝ)*|x i-y i|) : Integrable _ (gaussianReal 0 1))
    (fun z => by simpa [Fin.sum_univ_succ] using hf (Fin.cons z x) (Fin.cons z y))
  simpa using h

 

theorem CoordinateLipschitz.variance_le {n : ℕ} {c : Fin n → ℝ≥0}
    {f : (Fin n → ℝ) → ℝ} (hf : CoordinateLipschitz c f) :
    variance f (standardLaw n) ≤ ∑ i, (c i:ℝ)^2 := by
  induction n with
  | zero =>
    have he : f=fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
    rw [he]
    simp [variance, evariance]
  | succ n ih =>
    let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
    have hpres : MeasurePreserving e ((gaussianReal 0 1).prod (standardLaw n)) (standardLaw (n+1)) :=
      (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) 0).symm
    have he (z : ℝ) (y : Fin n → ℝ) : e (z,y)=Fin.cons z y := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hfull : MemLp (fun p => f (e p)) 2 ((gaussianReal 0 1).prod (standardLaw n)) :=
      hf.memLp.comp_measurePreserving hpres
    have hs (y : Fin n → ℝ) : MemLp (fun z => f (e (z,y))) 2 (gaussianReal 0 1) := by
      simp_rw [he]
      exact memLp_lipschitz (hf.first_slice y) (memLp_id_gaussianReal (μ:=0) (v:=1) 2)
    have htotal := variance_prod_decomposition hfull hs (by
      simp only [he]
      change MemLp (GaussianConcentration.firstMean f) 2 (standardLaw n)
      exact hf.firstMean.memLp)
    have hv : variance (fun p => f (e p)) ((gaussianReal 0 1).prod (standardLaw n))=
        variance f (standardLaw (n+1)) := hpres.variance_fun_comp hf.memLp.aemeasurable
    rw [hv] at htotal
    simp only [he] at htotal
    rw [htotal, Fin.sum_univ_succ]
    apply add_le_add _ (ih hf.firstMean)
    have hmvar : Integrable (fun y => variance (fun z => f (Fin.cons z y)) (gaussianReal 0 1))
        (standardLaw n) := by
      have hv' (y : Fin n → ℝ) := variance_eq_sub (hs y)
      simp only [he] at hv'
      simp_rw [hv']
      have hin : Integrable (fun y => ∫ z, f (Fin.cons z y)^2 ∂gaussianReal 0 1) (standardLaw n) := by
        simpa only [he] using hfull.integrable_sq.integral_prod_right
      exact hin.sub hf.firstMean.memLp.integrable_sq
    have hle := integral_mono hmvar (integrable_const ((c 0:ℝ)^2))
      (fun y => variance_lipschitz_real (hf.first_slice y))
    simpa using hle
end GaussianConcentration

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace GaussianConcentration
open SKGaussian SKQAOA ParisiInterpolation ParisiFinite

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma logPartition_lipschitz : LipschitzWith 1 (@logPartition ι _) := by
  have he : spinTrace (ι:=ι) 1 = logPartition := by funext x; simp [spinTrace]
  rw [← he]
  exact spinTrace_lipschitz one_ne_zero

lemma logPartition_coordinate {d : ℕ} (A : ι → Fin d → ℝ) (c : Fin d → ℝ≥0)
    (hA : ∀ s k, |A s k| ≤ c k) :
    CoordinateLipschitz c (fun z => logPartition (linearField A z)) := by
  intro x y
  have h := logPartition_lipschitz.norm_sub_le (linearField A x) (linearField A y)
  simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs] at h
  apply h.trans
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro s
  calc
    ‖linearField A x s-linearField A y s‖ = |∑ k, A s k*(x k-y k)| := by
      simp only [linearField, Real.norm_eq_abs, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ k, |A s k*(x k-y k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun k _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA s k) (abs_nonneg _))

omit [Fintype ι] [Nonempty ι] in
lemma variance_reindex_field {κ : Type*} [Fintype κ] (A : ι → κ → ℝ)
    (f : (ι → ℝ) → ℝ) :
    variance (fun z => f (linearField (fun s k => A s ((Fintype.equivFin κ).symm k)) z))
      (standardLaw (Fintype.card κ)) = variance (fun z => f (field A z)) (gaussianLaw κ) := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let T : (Fin (Fintype.card κ) → ℝ) ≃ᵐ (κ → ℝ) := MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  have hm : MeasurePreserving T (standardLaw (Fintype.card κ)) (gaussianLaw κ) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have he (x : Fin (Fintype.card κ) → ℝ) :
      field A (T x) = linearField (fun s k => A s (e k)) x := by
    funext s
    change (∑ k, A s k*T x k)=∑ k, A s (e k)*x k
    rw [← e.sum_comp (fun k => A s k*T x k)]
    simp [T, MeasurableEquiv.piCongrLeft_apply_apply]
  rw [← hm.map_eq, variance_map_equiv]
  change _ = variance (fun z => f (field A (T z))) _
  simp_rw [he]
  rfl

 

lemma variance_field_logPartition_le {κ : Type*} [Fintype κ]
    (A : ι → κ → ℝ) (c : κ → ℝ≥0) (hA : ∀ s k, |A s k| ≤ c k) :
    variance (fun z => logPartition (field A z)) (gaussianLaw κ) ≤ ∑ k, (c k:ℝ)^2 := by
  rw [← variance_reindex_field]
  have h := (logPartition_coordinate (fun s k => A s ((Fintype.equivFin κ).symm k))
    (fun k => c ((Fintype.equivFin κ).symm k)) (fun s k => hA s _)).variance_le
  rw [(Fintype.equivFin κ).symm.sum_comp (fun k => (c k:ℝ)^2)] at h
  exact h

 

theorem sk_logPartition_variance_le {n : ℕ} (hn : 0 < n) (β : ℝ) :
    variance (fun J => logPartition (fun σ => β*hamiltonian n J σ)) (disorderLaw n) ≤
      β^2*((n:ℝ)-1)/2 := by
  let b : ℝ≥0 := ⟨|β| *(Real.sqrt (n:ℝ))⁻¹, by positivity⟩
  have hb (σ : Configuration n) (e : Edge n) : |β*skCoeff n σ e| ≤ b := by
    change |β*skCoeff n σ e| ≤ |β| * (Real.sqrt (n:ℝ))⁻¹
    simp [skCoeff, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), spin_abs]
  have h := variance_field_logPartition_le (fun σ e => β*skCoeff n σ e) (fun _ => b) hb
  simp only [field_scale, field_skCoeff] at h
  change variance (fun J => logPartition (fun σ => β*hamiltonian n J σ)) (disorderLaw n) ≤ _ at h
  apply h.trans_eq
  change (∑ _ : Edge n, (|β| * (Real.sqrt (n:ℝ))⁻¹)^2) = _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc := card_edges_real n
  field_simp [hn']
  nlinarith only [hc]

lemma sk_pressureDensity_variance_le {n : ℕ} (hn : 0 < n) (β : ℝ) :
    variance (fun J => logPartition (fun σ => β*hamiltonian n J σ)/(n:ℝ)) (disorderLaw n) ≤
      β^2/(2*(n:ℝ)) := by
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  have h := mul_le_mul_of_nonneg_right (sk_logPartition_variance_le hn β) (sq_nonneg ((n:ℝ)⁻¹))
  apply h.trans
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  field_simp
  nlinarith [sq_nonneg β]

 

theorem tendsto_sk_pressureDensity_variance (β : ℝ) :
    Tendsto (fun n : ℕ => variance
      (fun J => logPartition (fun σ => β*hamiltonian n J σ)/(n:ℝ)) (disorderLaw n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun n => variance_nonneg _ _))
    ((eventually_gt_atTop 0).mono fun n hn => sk_pressureDensity_variance_le hn β)
  have h := (tendsto_const_nhds (x := β^2/2) (f := atTop)).mul
    (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop))
  convert h using 1 <;> simp [div_eq_mul_inv, mul_left_comm, mul_comm]

end GaussianConcentration

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 
def replicaMean {r : ℕ} (x : ι → ℝ) (f : (Fin r → ι) → ℝ) : ℝ :=
  ∑ σ, replicaWeight x σ*f σ

lemma replicaMean_single {r : ℕ} (x : ι → ℝ) (i : Fin r) (f : ι → ℝ) :
    replicaMean x (fun σ => f (σ i)) = ∑ s, weight x s*f s := by
  classical
  have h := Fintype.prod_sum (fun (j : Fin r) (s : ι) => weight x s * if j=i then f s else 1)
  have he (σ : Fin r → ι) :
      (∏ j, weight x (σ j)*(if j=i then f (σ j) else 1))=replicaWeight x σ*f (σ i) := by
    rw [Finset.prod_mul_distrib]
    simp [replicaWeight]
  simp_rw [he] at h
  unfold replicaMean
  rw [← h]
  have he' (j : Fin r) : (∑ s, weight x s*(if j=i then f s else 1))=
      if j=i then ∑ s, weight x s*f s else 1 := by
    split <;> simp_all [sum_weight]
  simp_rw [he']
  simp

lemma replicaMean_sum {r : ℕ} (x : ι → ℝ) (f : Fin r → ι → ℝ) :
    replicaMean x (fun σ => ∑ l, f l (σ l))=∑ l, ∑ s, weight x s*f l s := by
  simp only [replicaMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  exact replicaMean_single x l (f l)

lemma replicaMean_sum_same {r : ℕ} (x : ι → ℝ) (f : ι → ℝ) :
    replicaMean x (fun σ : Fin r → ι => ∑ l, f (σ l))=(r:ℝ)*∑ s, weight x s*f s := by
  rw [replicaMean_sum]
  simp

omit [Nonempty ι] in
lemma replicaWeight_snoc {r : ℕ} (x : ι → ℝ) (σ : Fin r → ι) (s : ι) :
    replicaWeight x (Fin.snoc σ s)=replicaWeight x σ*weight x s := by
  simp [replicaWeight, Fin.prod_univ_castSucc]

omit [Nonempty ι] in
lemma sum_tuples_snoc {r : ℕ} (f : (Fin (r+1) → ι) → ℝ) :
    (∑ τ, f τ) = ∑ σ : Fin r → ι, ∑ s, f (Fin.snoc σ s) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (r+1) => ι)).sum_comp f, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

omit [Nonempty ι] in
lemma replicaMean_snoc {r : ℕ} (x : ι → ℝ) (f : (Fin (r+1) → ι) → ℝ) :
    replicaMean x f = ∑ σ : Fin r → ι, replicaWeight x σ*∑ s, weight x s*f (Fin.snoc σ s) := by
  unfold replicaMean
  rw [sum_tuples_snoc]
  simp only [replicaWeight_snoc, Finset.mul_sum, mul_assoc]

lemma replicaMean_marginal {r : ℕ} (x : ι → ℝ) (f : (Fin r → ι) → ℝ) :
    replicaMean x (fun τ : Fin (r+1) → ι => f (fun l => τ l.castSucc))=replicaMean x f := by
  rw [replicaMean_snoc]
  simp [replicaMean, ← Finset.sum_mul, sum_weight]

lemma integrable_replicaMean {d r : ℕ} (A : ι → Fin d → ℝ) (f : (Fin r → ι) → ℝ) :
    Integrable (fun z => replicaMean (linearField A z) f) (standardLaw d) := by
  exact integrable_finsetSum _ (fun σ _ => (integrable_linear_replicaWeight A σ).mul_const (f σ))

 

lemma integrable_replica_energy {d r : ℕ} (A : ι → Fin d → ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) :
    Integrable (fun z => ∑ σ, replicaWeight (linearField A z) σ*
      (linearField A z (σ i)*f σ)) (standardLaw d) := by
  apply integrable_finsetSum
  intro σ _
  have he (z : Fin d → ℝ) : replicaWeight (linearField A z) σ*(linearField A z (σ i)*f σ)=
      ∑ k, (A (σ i) k*f σ)*(z k*replicaWeight (linearField A z) σ) := by
    simp only [linearField, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun k _ => (integrable_coord_replicaWeight A σ k).const_mul _)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma integrable_replicaWeight_derivative {d r : ℕ} (A : ι → Fin d → ℝ)
    (σ : Fin r → ι) (k : Fin d) :
    Integrable (fun z => replicaWeight (linearField A z) σ *
      ((∑ l, A (σ l) k) - (∑ τ : Fin r → ι,
        replicaWeight (linearField A z) τ * ∑ l, A (τ l) k))) (standardLaw d) := by
  have h := integrable_weight_derivative (tupleCoeff A) σ k
  simp only [replicaWeight_tupleCoeff, tupleCoeff] at h
  exact h

 
def crossKernel {d : ℕ} (B A : ι → Fin d → ℝ) (s t : ι) : ℝ :=
  ∑ k, B s k*A t k

lemma replica_covariance_algebra {d r : ℕ} (A B : ι → Fin d → ℝ)
    (x : ι → ℝ) (σ : Fin r → ι) (s : ι) :
    (∑ k, B s k*((∑ l, A (σ l) k)-(∑ τ : Fin r → ι,
      replicaWeight x τ*∑ l, A (τ l) k))) =
      (∑ l, crossKernel B A s (σ l))-(r:ℝ)*∑ t, weight x t*crossKernel B A s t := by
  have he (k : Fin d) : (∑ τ : Fin r → ι, replicaWeight x τ*∑ l, A (τ l) k)=
      (r:ℝ)*∑ t, weight x t*A t k := replicaMean_sum_same x (fun t => A t k)
  simp_rw [he]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    rfl
  · simp only [crossKernel, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma integral_replica_linear {d r : ℕ} (A B : ι → Fin d → ℝ)
    (σ : Fin r → ι) (s : ι) :
    (∫ z, linearField B z s * replicaWeight (linearField A z) σ ∂standardLaw d) =
      ∫ z, replicaWeight (linearField A z) σ *
        ((∑ l, crossKernel B A s (σ l))-(r:ℝ)*∑ t, weight (linearField A z) t*crossKernel B A s t)
        ∂standardLaw d := by
  have hleft (z : Fin d → ℝ) : linearField B z s*replicaWeight (linearField A z) σ=
      ∑ k, B s k*(z k*replicaWeight (linearField A z) σ) := by
    simp [linearField, Finset.sum_mul, mul_assoc]
  simp_rw [hleft]
  rw [integral_finsetSum _ (fun k _ => (integrable_coord_replicaWeight A σ k).const_mul _)]
  simp_rw [integral_const_mul, integral_coord_replicaWeight]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun k _ => (integrable_replicaWeight_derivative A σ k).const_mul _)]
  apply integral_congr_ae
  filter_upwards with z
  rw [← replica_covariance_algebra A B]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Nonempty ι] in
lemma replica_covariance_snoc {d r : ℕ} (A B : ι → Fin d → ℝ) (x : ι → ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) :
    replicaMean x (fun τ : Fin (r+1) → ι =>
      f (fun l => τ l.castSucc)*crossKernel B A (τ i.castSucc) (τ (Fin.last r))) =
      ∑ σ : Fin r → ι, replicaWeight x σ*f σ*∑ t, weight x t*crossKernel B A (σ i) t := by
  rw [replicaMean_snoc]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  simp only [mul_comm (weight x _), mul_assoc, ← Finset.mul_sum]

 

theorem integral_replica_energy_covariance {d r : ℕ} (A B : ι → Fin d → ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) :
    (∫ z, ∑ σ, replicaWeight (linearField A z) σ*(linearField B z (σ i)*f σ)
      ∂standardLaw d) =
      (∫ z, replicaMean (linearField A z) (fun σ => f σ*∑ l, crossKernel B A (σ i) (σ l))
        ∂standardLaw d) - (r:ℝ)*
      (∫ z, replicaMean (linearField A z) (fun τ : Fin (r+1) → ι =>
        f (fun l => τ l.castSucc)*crossKernel B A (τ i.castSucc) (τ (Fin.last r))) ∂standardLaw d) := by
  have hi (σ : Fin r → ι) : Integrable (fun z => linearField B z (σ i)*
      replicaWeight (linearField A z) σ) (standardLaw d) := by
    have he (z : Fin d → ℝ) : linearField B z (σ i)*replicaWeight (linearField A z) σ=
        ∑ k, B (σ i) k*(z k*replicaWeight (linearField A z) σ) := by
      simp [linearField, Finset.sum_mul, mul_assoc]
    simp_rw [he]
    exact integrable_finsetSum _ (fun k _ => (integrable_coord_replicaWeight A σ k).const_mul _)
  have hir (σ : Fin r → ι) : Integrable (fun z => replicaWeight (linearField A z) σ *
      ((∑ l, crossKernel B A (σ i) (σ l))-(r:ℝ)*∑ t, weight (linearField A z) t*crossKernel B A (σ i) t))
      (standardLaw d) := by
    simp_rw [← replica_covariance_algebra A B]
    have he (z : Fin d → ℝ) : replicaWeight (linearField A z) σ *
        (∑ k, B (σ i) k*((∑ l, A (σ l) k)-(∑ τ : Fin r → ι,
          replicaWeight (linearField A z) τ*∑ l, A (τ l) k)))=
        ∑ k, B (σ i) k*(replicaWeight (linearField A z) σ *
          ((∑ l, A (σ l) k)-(∑ τ : Fin r → ι,
            replicaWeight (linearField A z) τ*∑ l, A (τ l) k))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    exact integrable_finsetSum _ (fun k _ => (integrable_replicaWeight_derivative A σ k).const_mul _)
  have he (z : Fin d → ℝ) (σ : Fin r → ι) :
      replicaWeight (linearField A z) σ*(linearField B z (σ i)*f σ)=
      (linearField B z (σ i)*replicaWeight (linearField A z) σ)*f σ := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun σ _ => (hi σ).mul_const (f σ))]
  simp_rw [integral_mul_const, integral_replica_linear, ← integral_mul_const]
  rw [← integral_finsetSum _ (fun σ _ => (hir σ).mul_const (f σ))]
  rw [← integral_const_mul, ← integral_sub (integrable_replicaMean A _)
    ((integrable_replicaMean A _).const_mul _)]
  apply integral_congr_ae
  filter_upwards with z
  rw [replica_covariance_snoc]
  simp only [replicaMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  simp [mul_sub, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

 
def crossCov (B A : ι → κ → ℝ) (s t : ι) : ℝ := ∑ k, B s k*A t k

omit [Fintype ι] [Nonempty ι] in
lemma crossCov_reindex (B A : ι → κ → ℝ) (s t : ι) :
    crossKernel (fun s k => B s ((Fintype.equivFin κ).symm k))
      (fun s k => A s ((Fintype.equivFin κ).symm k)) s t = crossCov B A s t :=
  (Fintype.equivFin κ).symm.sum_comp (fun k => B s k*A t k)

 

omit [Fintype ι] [Nonempty ι] in
lemma integral_reindex_pair (A B : ι → κ → ℝ) (f : (ι → ℝ) → (ι → ℝ) → ℝ) :
    (∫ z, f (linearField (fun s k => A s ((Fintype.equivFin κ).symm k)) z)
      (linearField (fun s k => B s ((Fintype.equivFin κ).symm k)) z)
        ∂standardLaw (Fintype.card κ)) = ∫ z, f (field A z) (field B z) ∂gaussianLaw κ := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let T : (Fin (Fintype.card κ) → ℝ) ≃ᵐ (κ → ℝ) := MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  have hm : MeasurePreserving T (standardLaw (Fintype.card κ)) (gaussianLaw κ) :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) e
  have he (C : ι → κ → ℝ) (z : Fin (Fintype.card κ) → ℝ) :
      field C (T z) = linearField (fun s k => C s (e k)) z := by
    funext s
    change (∑ k, C s k*T z k)=∑ k, C s (e k)*z k
    rw [← e.sum_comp (fun k => C s k*T z k)]
    simp [T, MeasurableEquiv.piCongrLeft_apply_apply]
  have h := hm.integral_comp' (fun z => f (field A z) (field B z))
  simp_rw [he] at h
  exact h

lemma integrable_field_replicaWeight {r : ℕ} (A : ι → κ → ℝ) (σ : Fin r → ι) :
    Integrable (fun z => replicaWeight (field A z) σ) (gaussianLaw κ) := by
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_replicaWeight σ).comp (continuous_field A)).aestronglyMeasurable
  filter_upwards with z
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (replicaWeight_nonneg _ _)] using replicaWeight_le_one (field A z) σ

lemma integrable_field_replicaMean {r : ℕ} (A : ι → κ → ℝ) (f : (Fin r → ι) → ℝ) :
    Integrable (fun z => replicaMean (field A z) f) (gaussianLaw κ) := by
  exact integrable_finsetSum _ (fun σ _ => (integrable_field_replicaWeight A σ).mul_const (f σ))

lemma integrable_field_replica_energy {r : ℕ} (A B : ι → κ → ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) :
    Integrable (fun z => ∑ σ, replicaWeight (field A z) σ*(field B z (σ i)*f σ)) (gaussianLaw κ) := by
  apply integrable_finsetSum
  intro σ _
  have h := ((integrable_field B (σ i)).mul_const (f σ)).bdd_mul
    ((continuous_replicaWeight σ).comp (continuous_field A)).aestronglyMeasurable
    (c:=1) (Eventually.of_forall fun z => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (replicaWeight_nonneg _ _)] using replicaWeight_le_one (field A z) σ)
  exact h

 

theorem integral_field_replica_energy_covariance {r : ℕ} (A B : ι → κ → ℝ)
    (i : Fin r) (f : (Fin r → ι) → ℝ) :
    (∫ z, ∑ σ, replicaWeight (field A z) σ*(field B z (σ i)*f σ) ∂gaussianLaw κ) =
      (∫ z, replicaMean (field A z) (fun σ => f σ*∑ l, crossCov B A (σ i) (σ l)) ∂gaussianLaw κ) -
      (r:ℝ)*(∫ z, replicaMean (field A z) (fun τ : Fin (r+1) → ι =>
        f (fun l => τ l.castSucc)*crossCov B A (τ i.castSucc) (τ (Fin.last r))) ∂gaussianLaw κ) := by
  have h := integral_replica_energy_covariance
    (fun s k => A s ((Fintype.equivFin κ).symm k))
    (fun s k => B s ((Fintype.equivFin κ).symm k)) i f
  simp only [crossCov_reindex] at h
  rw [integral_reindex_pair A B
    (fun x y => ∑ σ, replicaWeight x σ*(y (σ i)*f σ))] at h
  rw [integral_reindex_pair A A (fun x _ => replicaMean x (fun σ => f σ*∑ l, crossCov B A (σ i) (σ l))),
    integral_reindex_pair A A (fun x _ => replicaMean x (fun τ : Fin (r+1) → ι =>
      f (fun l => τ l.castSucc)*crossCov B A (τ i.castSucc) (τ (Fin.last r))))] at h
  exact h

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation GaussianConcentration

 

def pSpinCoeff (n p : ℕ) (σ : Configuration n) (a : Fin p → Fin n) : ℝ :=
  ∏ l, (Real.sqrt (n:ℝ))⁻¹*spin σ (a l)

lemma pSpinCoeff_abs (n p : ℕ) (σ : Configuration n) (a : Fin p → Fin n) :
    |pSpinCoeff n p σ a|=((Real.sqrt (n:ℝ))⁻¹)^p := by
  simp [pSpinCoeff, Finset.abs_prod, abs_mul, spin_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]

 
lemma pSpinCoeff_kernel {n : ℕ} (_hn : 0 < n) (p : ℕ) (σ τ : Configuration n) :
    kernel (pSpinCoeff n p) σ τ=(overlap σ τ)^p := by
  have he (a : Fin p → Fin n) : pSpinCoeff n p σ a*pSpinCoeff n p τ a=
      ∏ l, ((Real.sqrt (n:ℝ))⁻¹*spin σ (a l))*((Real.sqrt (n:ℝ))⁻¹*spin τ (a l)) := by
    simp only [pSpinCoeff, Finset.prod_mul_distrib]
  unfold kernel
  simp_rw [he]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (i : Fin n) =>
    ((Real.sqrt (n:ℝ))⁻¹*spin σ i)*((Real.sqrt (n:ℝ))⁻¹*spin τ i))]
  have he' : (∑ i : Fin n, ((Real.sqrt (n:ℝ))⁻¹*spin σ i)*
      ((Real.sqrt (n:ℝ))⁻¹*spin τ i))=overlap σ τ := by
    calc
      _ = ((Real.sqrt (n:ℝ))⁻¹)^2*overlapSum σ τ := by
        simp only [overlapSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; simp [overlap, div_eq_mul_inv, mul_comm]
  simp_rw [he']
  simp

lemma pSpinCoeff_diag {n : ℕ} (hn : 0 < n) (p : ℕ) (σ : Configuration n) :
    kernel (pSpinCoeff n p) σ σ=1 := by rw [pSpinCoeff_kernel hn, overlap_self hn, one_pow]

 

def perturbedCoeff (n p : ℕ) (β a : ℝ) (σ : Configuration n) :
    Edge n ⊕ (Fin p → Fin n) → ℝ :=
  Sum.elim (fun e => β*skCoeff n σ e) (fun u => a*pSpinCoeff n p σ u)

lemma perturbedCoeff_kernel {n : ℕ} (hn : 0 < n) (p : ℕ) (β a : ℝ)
    (σ τ : Configuration n) :
    kernel (perturbedCoeff n p β a) σ τ =
      β^2*((overlapSum σ τ)^2-(n:ℝ))/(2*n)+a^2*(overlap σ τ)^p := by
  unfold kernel perturbedCoeff
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  change kernel (fun s e => β*skCoeff n s e) σ τ+
    kernel (fun s u => a*pSpinCoeff n p s u) σ τ=_
  rw [kernel_scale, kernel_scale, kernel, coeff_covariance hn, pSpinCoeff_kernel hn]
  ring

 

lemma variance_logPartition_le_diagonal {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (A : ι → κ → ℝ) (s : ι) (hA : ∀ t k, |A t k|=|A s k|) :
    variance (fun z => logPartition (field A z)) (gaussianLaw κ) ≤ kernel A s s := by
  have h := variance_field_logPartition_le A (fun k => ‖A s k‖₊) (fun t k => by
    simpa only [coe_nnnorm, Real.norm_eq_abs] using (hA t k).le)
  apply h.trans_eq
  simp only [coe_nnnorm, Real.norm_eq_abs, sq_abs]
  simp only [kernel, sq]

lemma perturbedCoeff_abs (n p : ℕ) (β a : ℝ) (σ τ : Configuration n)
    (k : Edge n ⊕ (Fin p → Fin n)) :
    |perturbedCoeff n p β a σ k|=|perturbedCoeff n p β a τ k| := by
  cases k with
  | inl e => simp [perturbedCoeff, skCoeff, abs_mul, spin_abs]
  | inr u => simp [perturbedCoeff, abs_mul, pSpinCoeff_abs]

 

lemma perturbed_logPartition_variance_le {n : ℕ} (hn : 0 < n) (p : ℕ) (β a : ℝ) :
    variance (fun z => logPartition (field (perturbedCoeff n p β a) z))
      (gaussianLaw (Edge n ⊕ (Fin p → Fin n))) ≤ β^2*((n:ℝ)-1)/2+a^2 := by
  let σ : Configuration n := fun _ => false
  apply (variance_logPartition_le_diagonal (perturbedCoeff n p β a) σ
    (fun τ k => perturbedCoeff_abs n p β a τ σ k)).trans_eq
  rw [perturbedCoeff_kernel hn, overlap_self hn, one_pow, mul_one]
  have hs : overlapSum σ σ=(n:ℝ) := by
    simp [overlapSum, ← sq, spin_sq]
  rw [hs]
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiInterpolation
open SKGaussian
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

lemma replicaAverage_abs_le (A : ι → κ → ℝ) {K : ι → ι → ℝ} {M : ℝ}
    (hK : ∀ s t, |K s t| ≤ M) (z : κ → ℝ) : |replicaAverage A K z| ≤ M := by
  calc
    _ ≤ ∑ i, ∑ j, |weight (field A z) i*weight (field A z) j*K i j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, weight (field A z) i*weight (field A z) j*M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le)]
      exact mul_le_mul_of_nonneg_left (hK i j) (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le)
    _ = M := replicaAverage_const A z M

lemma replicaMean_abs_le (A : ι → κ → ℝ) {K : ι → ι → ℝ} {M : ℝ}
    (hK : ∀ s t, |K s t| ≤ M) : |replicaMean A K| ≤ M := by
  apply abs_integral_le_integral_abs.trans
  have h := integral_mono (integrable_replicaAverage A K).abs (integrable_const M)
    (replicaAverage_abs_le A hK)
  simpa using h

 

lemma expected_difference_le_orthogonal (A B : ι → κ → ℝ)
    (hAB : ∀ i j, ∑ k, A i k*B j k=0) {M : ℝ} (hM : 0 ≤ M)
    (hinc : ∀ s t, |increment B s t-increment A s t| ≤ M) :
    |expected B-expected A| ≤ M*Real.pi/4 := by
  let L : ℝ≥0 := ⟨M/2, by positivity⟩
  have hLip : LipschitzWith L (fun t => expected (rotate A B t)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_expected_rotate_mean A B hAB t).differentiableAt)
    intro t
    rw [(hasDerivAt_expected_rotate_mean A B hAB t).deriv]
    have hr := replicaMean_abs_le (rotate A B t) hinc
    have htrig : |Real.sin t*Real.cos t| ≤ 1 := by
      rw [abs_mul]
      calc
        |Real.sin t| * |Real.cos t| ≤ 1 * |Real.cos t| :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _)
        _ ≤ 1 := by simpa using Real.abs_cos_le_one t
    have hnorm : ‖Real.sin t*Real.cos t/2*
        replicaMean (rotate A B t) (fun i j => increment B i j-increment A i j)‖ ≤ M/2 := by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      have h1 := mul_le_mul (div_le_div_of_nonneg_right htrig (by norm_num)) hr
        (abs_nonneg _) (by positivity : 0 ≤ (1:ℝ)/2)
      nlinarith only [h1]
    exact_mod_cast hnorm
  have he0 : rotate A B 0=A := by ext i k; simp [rotate]
  have he1 : rotate A B (Real.pi/2)=B := by ext i k; simp [rotate]
  have h := hLip.norm_sub_le (Real.pi/2) 0
  rw [he0, he1] at h
  change |expected B-expected A| ≤ (M/2)*|Real.pi/2-0| at h
  simpa only [sub_zero, abs_of_nonneg (by positivity : 0 ≤ Real.pi/2), div_mul_div_comm, show (2:ℝ)*2=4 by norm_num] using h

lemma expected_difference_le {κ' : Type*} [Fintype κ'] (A : ι → κ → ℝ) (B : ι → κ' → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hinc : ∀ s t, |increment B s t-increment A s t| ≤ M) :
    |expected B-expected A| ≤ M*Real.pi/4 := by
  let A' : ι → κ ⊕ κ' → ℝ := fun s => Sum.elim (A s) (fun _ => 0)
  let B' : ι → κ ⊕ κ' → ℝ := fun s => Sum.elim (fun _ => 0) (B s)
  have ha (s t : ι) : increment A' s t=increment A s t := by
    simp [increment, A', Fintype.sum_sum_type]
  have hb (s t : ι) : increment B' s t=increment B s t := by
    simp [increment, B', Fintype.sum_sum_type]
  have h := expected_difference_le_orthogonal A' B'
    (fun s t => by simp [A', B', Fintype.sum_sum_type]) hM (fun s t => by simpa only [ha,hb] using hinc s t)
  have hea : expected A'=expected A := integral_field_inl A logPartition
  have heb : expected B'=expected B := integral_field_inr B logPartition
  rwa [hea,heb] at h

end ParisiInterpolation

end

end OAI
