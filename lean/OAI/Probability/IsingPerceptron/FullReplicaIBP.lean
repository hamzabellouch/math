import Mathlib
import OAI.Probability.IsingPerceptron.DeviationRate

namespace OAI

/-! Full Replica I B P. -/

noncomputable section

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology
variable {S I : Type*} [Fintype S] [Nonempty S] [Fintype I] [DecidableEq I]

theorem replicated_gaussian_cross_ibp {m : ℕ} (W : S → ℝ) (D : (I → S) → ℝ)
    (A B : S → Fin (m+1) → ℝ) (t : ℝ) (head : I) :
    (∫g,replicatedGibbs (gaussianGibbsH W A t g)
      (fun x => D x*gaussianLinear B g (x head)) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫g,t*(replicatedGibbs (gaussianGibbsH W A t g)
      (fun x => D x*∑l,(∑i,B (x head) i*A (x l) i))-
      (Fintype.card I:ℝ)*replicatedGibbs (gaussianGibbsH W A t g)
      (fun x => finiteGibbs (gaussianGibbsH W A t g)
        (fun z => D x*(∑i,B (x head) i*A z i))))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have h := gaussianGibbs_ibp (replicasEnergy W) D
    (fun x : I → S => fun i => ∑l,A (x l) i) (fun x i => B (x head) i) t
  simp only [replicas_gaussian_hamiltonian] at h
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards [] with g
  let H := gaussianGibbsH W A t g
  have hc (x y : I → S) : (∑i,B (x head) i*(∑l,A (y l) i))=
      ∑l,(∑i,B (x head) i*A (y l) i) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  simp only [hc]
  have hp (x : I → S) : finiteGibbs (replicasEnergy H)
      (fun y : I → S => D x*∑l,(∑i,B (x head) i*A (y l) i))=
      (Fintype.card I:ℝ)*finiteGibbs H (fun z => D x*(∑i,B (x head) i*A z i)) := by
    simp only [Finset.mul_sum,finiteGibbs_sum]
    have hm (l : I) : finiteGibbs (replicasEnergy H)
        (fun y : I → S => D x*(∑i,B (x head) i*A (y l) i))=
        finiteGibbs H (fun z => D x*(∑i,B (x head) i*A z i)) :=
      replicatedGibbs_marginal H (fun z => D x*(∑i,B (x head) i*A z i)) l
    simp only [Finset.mul_sum,finiteGibbs_sum] at hm
    simp only [hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact Finset.mul_sum _ _ _
  change t*(finiteGibbs (replicasEnergy H) _-
    finiteGibbs (replicasEnergy H) (fun x => finiteGibbs (replicasEnergy H) _))=_
  simp only [hp,finiteGibbs_const_mul,replicatedGibbs]
  rfl

lemma fullTensor_selected_cross {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (x y : Spins N) :
    (∑i,fullTensorCoefficient hN s (selectedParameter (j.val+1)) x i*
      fullTensorCoefficient hN s v y i)=
      (s*(1/2)^(j.val+1))^2*v (j.val+1)*(spinOverlap x y)^(j.val+1) := by
  classical
  unfold fullTensorCoefficient
  rw [(fullTensorEnumeration N).sum_comp
    (fun a => (tensorAmplitude s (selectedParameter (j.val+1)) (a.1.val+1)*
      tensorCoefficient hN (a.1.val+1) x a.2)*
      (tensorAmplitude s v (a.1.val+1)*tensorCoefficient hN (a.1.val+1) y a.2))]
  rw [Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [tensorAmplitude,selectedParameter,ite_true,mul_one]
    have hc := tensor_covariance hN (j.val+1) x y
    unfold gaussianCoefficientCov at hc
    rw [← hc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · intro k _ hkj
    have hk : k.val+1≠j.val+1 := by intro he; exact hkj (Fin.ext (by omega))
    simp only [tensorAmplitude,selectedParameter,ite_eq_right hk,mul_zero,zero_mul,Finset.sum_const_zero]
  · simp

lemma replicated_linear_cross_ibp {n : ℕ} (W : S → ℝ) (D : (I → S) → ℝ)
    (A B : S → Fin n → ℝ) (head : I) :
    (∫g,replicatedGibbs (fun z => W z+∑i,g i*A z i)
      (fun x => D x*(∑i,g i*B (x head) i)) ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    ∫g,(replicatedGibbs (fun z => W z+∑i,g i*A z i)
      (fun x => D x*∑l,(∑i,B (x head) i*A (x l) i))-
      (Fintype.card I:ℝ)*replicatedGibbs (fun z => W z+∑i,g i*A z i)
      (fun x => finiteGibbs (fun z => W z+∑i,g i*A z i)
        (fun z => D x*(∑i,B (x head) i*A z i))))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  cases n with
  | zero => simp [replicatedGibbs,finiteGibbs_const]
  | succ m =>
    have he (g : Fin (m+1) → ℝ) : gaussianGibbsH W A 1 g=
        fun z => W z+∑i,g i*A z i := by funext z; simp only [gaussianGibbsH,gaussianLinear,one_mul]
    simpa only [he,gaussianLinear,one_mul] using
      replicated_gaussian_cross_ibp W D A B 1 head

theorem fullTensor_replica_ibp {N : ℕ} (hN : 0<N) (s : ℝ) (v : ℕ → ℝ)
    (j : Fin N) (W : Spins N → ℝ) (D : (I → Spins N) → ℝ) (head : I) :
    (∫g,replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => D x*fullTensorEnergy hN s (selectedParameter (j.val+1)) g (x head))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    (s*(1/2)^(j.val+1))^2*v (j.val+1)*
    ∫g,(replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => D x*∑l,(spinOverlap (x head) (x l))^(j.val+1))-
      (Fintype.card I:ℝ)*replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => finiteGibbs (fun z => W z+fullTensorEnergy hN s v g z)
        (fun z => D x*(spinOverlap (x head) z)^(j.val+1))))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have h := replicated_linear_cross_ibp W D (fullTensorCoefficient hN s v)
    (fullTensorCoefficient hN s (selectedParameter (j.val+1))) head
  change (∫g,replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => D x*fullTensorEnergy hN s (selectedParameter (j.val+1)) g (x head))
      ∂Measure.pi (fun _ => gaussianReal 0 1))=_ at h
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [fullTensor_selected_cross,← Finset.mul_sum]
  let c := (s*(1/2)^(j.val+1))^2*v (j.val+1)
  have he (a b : ℝ) : a*(c*b)=c*(a*b) := by ring
  simp only [show (s*(1/2)^(j.val+1))^2*v (j.val+1)=c from rfl,he,
    replicatedGibbs,finiteGibbs_const_mul]
  simp only [fullTensorEnergy]
  ring

theorem fullTensor_raw_replica_ibp {N : ℕ} (hN : 0<N) (s : ℝ) (hs : s≠0) (v : ℕ → ℝ)
    (j : Fin N) (W : Spins N → ℝ) (D : (I → Spins N) → ℝ) (head : I) :
    (∫g,replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => D x*selectedTensorObservable hN j g (x head))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
    (s*(1/2)^(j.val+1))*v (j.val+1)*
    ∫g,(replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => D x*∑l,(spinOverlap (x head) (x l))^(j.val+1))-
      (Fintype.card I:ℝ)*replicatedGibbs (fun z => W z+fullTensorEnergy hN s v g z)
      (fun x => finiteGibbs (fun z => W z+fullTensorEnergy hN s v g z)
        (fun z => D x*(spinOverlap (x head) z)^(j.val+1))))
      ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have h := fullTensor_replica_ibp hN s v j W D head
  simp only [fullTensorEnergy_selected] at h
  have he (a b : ℝ) : a*((s*(1/2)^(j.val+1))*b)=(s*(1/2)^(j.val+1))*(a*b) := by ring
  simp only [he,replicatedGibbs,finiteGibbs_const_mul,integral_const_mul] at h
  apply mul_left_cancel₀ (show s*(1/2)^(j.val+1)≠0 from mul_ne_zero hs (pow_ne_zero _ (by norm_num)))
  change (s*(1/2)^(j.val+1))*(∫g,finiteGibbs _ _ ∂Measure.pi (fun _ => gaussianReal 0 1))=_
  rw [h]
  simp only [replicatedGibbs,finiteGibbs_const_mul]
  ring

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology

lemma finiteGibbs_abs_expectation {S : Type*} [Fintype S] [Nonempty S]
    (H V : S → ℝ) : |finiteGibbs H V| ≤ finiteGibbs H (fun x => |V x|) := by
  rw [finiteGibbs,abs_div,abs_of_pos (finiteGibbs_den_pos H)]
  apply div_le_div_of_nonneg_right _ (finiteGibbs_den_pos H).le
  calc
    _ ≤ ∑x,|exp (H x)*V x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul,abs_of_pos (exp_pos _)]

lemma replicatedGibbs_centered_bound {S I : Type*} [Fintype S] [Nonempty S]
    [Fintype I] [DecidableEq I] (H Y : S → ℝ) (c K : ℝ) (D : (I → S) → ℝ)
    (hD : ∀x,|D x| ≤ K) (head : I) :
    |replicatedGibbs H (fun x => D x*(Y (x head)-c))| ≤
      K*finiteGibbs H (fun z => |Y z-c|) := by
  apply (finiteGibbs_abs_expectation _ _).trans
  have hmono := finiteGibbs_mono (replicasEnergy H)
    (fun x : I → S => |D x*(Y (x head)-c)|)
    (fun x => K*|Y (x head)-c|) (fun x => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hD x) (abs_nonneg _))
  rw [finiteGibbs_const_mul] at hmono
  exact hmono.trans_eq (congrArg (K*·) (replicatedGibbs_marginal H (fun z => |Y z-c|) head))

def tensorReplicaCentered {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    (p : PerturbedDisorder M N) : ℝ :=
  replicatedGibbs (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z)
    (fun x => D x*(selectedTensorObservable hN j p.1 (x head)-
      ∫q,tensorMeanAt hN f s j v q ∂perturbedDisorderLaw M N))

lemma tensorReplicaCentered_measurable {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    Measurable (tensorReplicaCentered (M:=M) hN f s j v D head) := by
  unfold tensorReplicaCentered replicatedGibbs finiteGibbs replicasEnergy
    patternEnergy rowEvaluation fullTensorEnergy selectedTensorObservable tensorPerturbation gaussianLinear
  fun_prop

lemma tensorReplicaCentered_bound {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    {K : ℝ} (hD : ∀x,|D x| ≤ K) (p : PerturbedDisorder M N) :
    |tensorReplicaCentered hN f s j v D head p| ≤ K*tensorDeviationAt hN f s j v p := by
  simpa only [tensorReplicaCentered,tensorDeviationAt,rawTensorDeviation,rawTensorMean,tensorMeanAt,
    Function.update_eq_self] using replicatedGibbs_centered_bound
      (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z)
      (selectedTensorObservable hN j p.1)
      (∫q,tensorMeanAt hN f s j v q ∂perturbedDisorderLaw M N) K D hD head

lemma tensorReplicaCentered_integrable {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    Integrable (tensorReplicaCentered (M:=M) hN f s j v D head) (perturbedDisorderLaw M N) := by
  apply ((tensorDeviationAt_integrable (M:=M) hN hf s j v).const_mul
    (∑x,|D x|)).mono' (tensorReplicaCentered_measurable hN hf s j v D head).aestronglyMeasurable
  exact Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs] using tensorReplicaCentered_bound hN f s j v D head (finiteFunction_bound D) p)

lemma tensorReplicaCentered_integral_bound {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) {K : ℝ} (hD : ∀x,|D x| ≤ K) :
    |∫p,tensorReplicaCentered (M:=M) hN f s j v D head p ∂perturbedDisorderLaw M N| ≤
      K*meanTensorDeviation (M:=M) hN f s j v := by
  calc
    _ ≤ ∫p,|tensorReplicaCentered hN f s j v D head p| ∂perturbedDisorderLaw M N := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (tensorReplicaCentered (M:=M) hN f s j v D head)
    _ ≤ ∫p,K*tensorDeviationAt hN f s j v p ∂perturbedDisorderLaw M N :=
      integral_mono (tensorReplicaCentered_integrable hN hf s j v D head).abs
        ((tensorDeviationAt_integrable hN hf s j v).const_mul K)
        (tensorReplicaCentered_bound hN f s j v D head hD)
    _ = _ := by rw [integral_const_mul]; rfl

def sourceReplicaCentered {n : ℕ} (α : ℝ) (f : ℝ → ℝ) (j N : ℕ)
    (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n) : ℝ :=
  if h : j<N then
    (∫p,tensorReplicaCentered (M:=patternCount α N-2)
      (Nat.lt_of_le_of_lt (Nat.zero_le j) h) f (perturbationScale N) ⟨j,h⟩ v D head p
        ∂perturbedDisorderLaw (patternCount α N-2) N)/perturbationScale N
  else 0

lemma sourceReplicaCentered_bound {n : ℕ} (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (j N : ℕ) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    {K : ℝ} (hD : ∀x,|D x| ≤ K) :
    |sourceReplicaCentered α f j N v D head| ≤ K*sourceDeviation α f j N v := by
  unfold sourceReplicaCentered sourceDeviation
  split_ifs with h
  · have hn : (0:ℝ)<N := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j) h)
    have hs : 0<perturbationScale N := rpow_pos_of_pos hn _
    rw [abs_div,abs_of_pos hs,← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (tensorReplicaCentered_integral_bound _ hf _ _ _ D head hD) hs.le
  · simp

theorem source_good_replica_factorization {n : ℕ} (α : ℝ) (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C)
    (v : ℕ → (ℕ → ℝ)) (hv : ∀ᶠN in atTop,v N∈sourceGoodParameters α f N)
    (j : ℕ) (D : (N : ℕ) → (Fin n → Spins N) → ℝ) (head : Fin n)
    {K : ℝ} (hD : ∀N x,|D N x| ≤ K) :
    Tendsto (fun N => sourceReplicaCentered α f j N (v N) (D N) head) atTop (𝓝 0) := by
  have he := (source_good_parameters α hα hf hC).2.2 v hv j
  have hb : Tendsto (fun N => K*sourceDeviation α f j N (v N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul he
  apply squeeze_zero_norm' (Eventually.of_forall (fun N => by
    simpa only [Real.norm_eq_abs] using sourceReplicaCentered_bound α hf j N (v N) (D N) head (hD N))) hb

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators Topology

def tensorReplicaRaw {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    (p : PerturbedDisorder M N) : ℝ :=
  replicatedGibbs (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z)
    (fun x => D x*selectedTensorObservable hN j p.1 (x head))

def tensorReplicaResponse {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    (p : PerturbedDisorder M N) : ℝ :=
  let H := fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z
  replicatedGibbs H (fun x => D x*∑l,(spinOverlap (x head) (x l))^(j.val+1))-
    (n:ℝ)*replicatedGibbs H (fun x => finiteGibbs H
      (fun z => D x*(spinOverlap (x head) z)^(j.val+1)))

lemma tensorReplicaRaw_measurable {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    Measurable (tensorReplicaRaw (M:=M) hN f s j v D head) := by
  unfold tensorReplicaRaw replicatedGibbs finiteGibbs replicasEnergy
    patternEnergy rowEvaluation fullTensorEnergy selectedTensorObservable tensorPerturbation gaussianLinear
  fun_prop

lemma tensorReplicaRaw_integrable {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    Integrable (tensorReplicaRaw (M:=M) hN f s j v D head) (perturbedDisorderLaw M N) := by
  apply ((((tensorMajorant_memLp hN j).comp_measurePreserving measurePreserving_fst).integrable
    (by norm_num)).const_mul (∑x,|D x|)).mono'
      (tensorReplicaRaw_measurable hN hf s j v D head).aestronglyMeasurable
  filter_upwards [] with p
  change |replicatedGibbs _ _| ≤ _
  apply finiteGibbs_abs
  intro x
  rw [abs_mul]
  exact mul_le_mul (finiteFunction_bound D x)
    (finiteFunction_bound (selectedTensorObservable hN j p.1) (x head))
    (abs_nonneg _) (Finset.sum_nonneg (fun x _ => abs_nonneg (D x)))

lemma perturbed_replica_test_integrable {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) :
    Integrable (fun p : PerturbedDisorder M N =>
      replicatedGibbs (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z) D)
      (perturbedDisorderLaw M N) := by
  apply bounded_integrable _ _ (fun p => finiteGibbs_abs _ _ (finiteFunction_bound D))
  simp only [finiteGibbs,replicasEnergy,patternEnergy,rowEvaluation,fullTensorEnergy]
  fun_prop

lemma tensorReplicaResponse_integrable {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    Integrable (tensorReplicaResponse (M:=M) hN f s j v D head) (perturbedDisorderLaw M N) := by
  apply Integrable.sub (perturbed_replica_test_integrable hN hf s v _) (Integrable.const_mul _ _)
  let K := ∑x : Fin n → Spins N,∑z : Spins N,|D x*(spinOverlap (x head) z)^(j.val+1)|
  refine bounded_integrable (perturbedDisorderLaw M N) (C:=K) ?_ ?_
  · simp only [replicatedGibbs,finiteGibbs,replicasEnergy,patternEnergy,rowEvaluation,fullTensorEnergy]
    fun_prop
  · intro p
    apply finiteGibbs_abs
    intro x
    apply (finiteGibbs_abs _ _ (finiteFunction_bound _)).trans
    dsimp [K]
    exact Finset.single_le_sum
      (f:=fun a : Fin n → Spins N => ∑z : Spins N,|D a*(spinOverlap (a head) z)^(j.val+1)|)
      (fun a _ => Finset.sum_nonneg (fun z _ => abs_nonneg _)) (Finset.mem_univ x)

theorem actual_joint_tensor_replica_ibp {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (hs : s≠0) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    (∫p,tensorReplicaRaw (M:=M) hN f s j v D head p ∂perturbedDisorderLaw M N)=
      (s*(1/2)^(j.val+1))*v (j.val+1)*
        ∫p,tensorReplicaResponse (M:=M) hN f s j v D head p ∂perturbedDisorderLaw M N := by
  have hi := tensorReplicaRaw_integrable (M:=M) hN hf s j v D head
  have hr := tensorReplicaResponse_integrable (M:=M) hN hf s j v D head
  rw [perturbedDisorderLaw,integral_prod_symm _ hi,
    integral_prod_symm _ hr,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with rows
  simpa only [tensorReplicaRaw,tensorReplicaResponse,Fintype.card_fin] using
    fullTensor_raw_replica_ibp hN s hs v j (patternEnergy f rows) D head

end IsingPerceptron.Main

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators Topology

lemma spinOverlap_self {N : ℕ} (hN : 0<N) (x : Spins N) : spinOverlap x x=1 := by
  have he (i : Fin N) : spin x i*spin x i=1 := by
    dsimp [spin]; split_ifs <;> norm_num
  simp only [spinOverlap,he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))

def tensorReplicaTest {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (p : PerturbedDisorder M N) : ℝ :=
  replicatedGibbs (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z) D

def tensorPairOverlap {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (p : PerturbedDisorder M N) : ℝ :=
  let H := fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z
  finiteGibbs H (fun x => finiteGibbs H (fun y => (spinOverlap x y)^(j.val+1)))

lemma tensorPairOverlap_integrable {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (j : Fin N) (v : ℕ → ℝ) :
    Integrable (tensorPairOverlap (M:=M) hN f s j v) (perturbedDisorderLaw M N) := by
  refine bounded_integrable _ (C:=∑x : Spins N,∑y : Spins N,|(spinOverlap x y)^(j.val+1)|) ?_ ?_
  · unfold tensorPairOverlap finiteGibbs patternEnergy rowEvaluation fullTensorEnergy
    fun_prop
  · intro p
    apply finiteGibbs_abs
    intro x
    apply (finiteGibbs_abs _ _ (finiteFunction_bound _)).trans
    exact Finset.single_le_sum
      (f:=fun a : Spins N => ∑y : Spins N,|(spinOverlap a y)^(j.val+1)|)
      (fun a _ => Finset.sum_nonneg (fun y _ => abs_nonneg _)) (Finset.mem_univ x)

lemma tensorMeanAt_eq_raw_one {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (p : PerturbedDisorder M N) :
    tensorReplicaRaw hN f s j v (fun _ : Fin 1 → Spins N => 1) 0 p=
      tensorMeanAt hN f s j v p := by
  simp only [tensorReplicaRaw,one_mul,tensorMeanAt,rawTensorMean,Function.update_eq_self]
  exact replicatedGibbs_marginal _ _ _

lemma tensorResponse_one {M N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (p : PerturbedDisorder M N) :
    tensorReplicaResponse hN f s j v (fun _ : Fin 1 → Spins N => 1) 0 p=
      1-tensorPairOverlap hN f s j v p := by
  simp only [tensorReplicaResponse,Fin.sum_univ_one,spinOverlap_self hN,one_pow,one_mul,
    Nat.cast_one,tensorPairOverlap]
  rw [show replicatedGibbs (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z)
    (fun _ : Fin 1 → Spins N => (1:ℝ))=1 from finiteGibbs_const _ _]
  apply congrArg (1-·)
  exact replicatedGibbs_marginal
    (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z)
    (fun x : Spins N => finiteGibbs
      (fun z => patternEnergy f p.2 z+fullTensorEnergy hN s v p.1 z)
      (fun y => (spinOverlap x y)^(j.val+1))) (0:Fin 1)

lemma actual_tensor_mean_ibp {M N : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (hs : s≠0) (j : Fin N) (v : ℕ → ℝ) :
    (∫p,tensorMeanAt (M:=M) hN f s j v p ∂perturbedDisorderLaw M N)=
      (s*(1/2)^(j.val+1))*v (j.val+1)*
        (1-∫p,tensorPairOverlap (M:=M) hN f s j v p ∂perturbedDisorderLaw M N) := by
  have h := actual_joint_tensor_replica_ibp (M:=M) hN hf s hs j v
    (fun _ : Fin 1 → Spins N => 1) 0
  simp_rw [tensorMeanAt_eq_raw_one,tensorResponse_one] at h
  rw [integral_sub (integrable_const _) (tensorPairOverlap_integrable hN hf s j v)] at h
  simpa using h

def tensorGGResidual {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n) : ℝ :=
  (∫p,tensorReplicaResponse (M:=M) hN f s j v D head p ∂perturbedDisorderLaw M N)-
    (∫p,tensorReplicaTest (M:=M) hN f s v D p ∂perturbedDisorderLaw M N)*
      (1-∫p,tensorPairOverlap (M:=M) hN f s j v p ∂perturbedDisorderLaw M N)

lemma tensorReplicaCentered_eq {M N n : ℕ} (hN : 0<N) (f : ℝ → ℝ) (s : ℝ)
    (j : Fin N) (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    (p : PerturbedDisorder M N) :
    tensorReplicaCentered hN f s j v D head p=tensorReplicaRaw hN f s j v D head p-
      tensorReplicaTest hN f s v D p*(∫q,tensorMeanAt hN f s j v q ∂perturbedDisorderLaw M N) := by
  simp only [tensorReplicaCentered,tensorReplicaRaw,tensorReplicaTest,replicatedGibbs,
    mul_sub,finiteGibbs_sub,finiteGibbs_mul_const]

theorem actual_finite_GG_identity {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (hs : s≠0) (j : Fin N) (v : ℕ → ℝ)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) :
    (∫p,tensorReplicaCentered (M:=M) hN f s j v D head p ∂perturbedDisorderLaw M N)=
      (s*(1/2)^(j.val+1))*v (j.val+1)*tensorGGResidual (M:=M) hN f s j v D head := by
  have ht : Integrable (tensorReplicaTest (M:=M) hN f s v D) (perturbedDisorderLaw M N) :=
    perturbed_replica_test_integrable hN hf s v D
  simp_rw [tensorReplicaCentered_eq]
  rw [integral_sub (tensorReplicaRaw_integrable hN hf s j v D head)
    (ht.mul_const _),integral_mul_const,
    actual_joint_tensor_replica_ibp hN hf s hs j v D head,actual_tensor_mean_ibp hN hf s hs j v]
  unfold tensorGGResidual
  ring

lemma actual_finite_GG_bound {M N n : ℕ} (hN : 0<N) {f : ℝ → ℝ}
    (hf : Measurable f) (s : ℝ) (hs : 0<s) (j : Fin N) (v : ℕ → ℝ)
    (hv : 1 ≤ v (j.val+1)) (D : (Fin n → Spins N) → ℝ) (head : Fin n)
    {K : ℝ} (hD : ∀x,|D x| ≤ K) :
    |tensorGGResidual (M:=M) hN f s j v D head| ≤
      (K/(1/2)^(j.val+1))*(meanTensorDeviation (M:=M) hN f s j v/s) := by
  have ha : (0:ℝ)<(1/2)^(j.val+1) := pow_pos (by norm_num) _
  have hp : 0<s*(1/2)^(j.val+1)*v (j.val+1) := mul_pos (mul_pos hs ha) (lt_of_lt_of_le zero_lt_one hv)
  have hb := tensorReplicaCentered_integral_bound (M:=M) hN hf s j v D head hD
  rw [actual_finite_GG_identity hN hf s hs.ne' j v D head,abs_mul,abs_of_pos hp] at hb
  have hc : s*(1/2)^(j.val+1)*|tensorGGResidual (M:=M) hN f s j v D head| ≤
      K*meanTensorDeviation (M:=M) hN f s j v :=
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_pos hs ha).le hv)
      (abs_nonneg _)).trans hb
  apply le_of_mul_le_mul_left _ (mul_pos hs ha)
  have he : s*(1/2)^(j.val+1)*((K/(1/2)^(j.val+1))*(meanTensorDeviation (M:=M) hN f s j v/s))=
      K*meanTensorDeviation (M:=M) hN f s j v := by field_simp
  rw [he]
  exact hc

def sourcePolynomialGGResidual {n : ℕ} (α : ℝ) (f : ℝ → ℝ) (j N : ℕ)
    (v : ℕ → ℝ) (D : (Fin n → Spins N) → ℝ) (head : Fin n) : ℝ :=
  if h : j<N then
    tensorGGResidual (M:=patternCount α N-2) (Nat.lt_of_le_of_lt (Nat.zero_le j) h)
      f (perturbationScale N) ⟨j,h⟩ v D head
  else 0

lemma sourcePolynomialGGResidual_bound {n : ℕ} (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (j N : ℕ) (v : ℕ → ℝ) (hv : ∀k,1 ≤ v k)
    (D : (Fin n → Spins N) → ℝ) (head : Fin n) {K : ℝ} (hD : ∀x,|D x| ≤ K) :
    |sourcePolynomialGGResidual α f j N v D head| ≤
      (K/(1/2)^(j+1))*sourceDeviation α f j N v := by
  unfold sourcePolynomialGGResidual sourceDeviation
  split_ifs with h
  · have hn : (0:ℝ)<N := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j) h)
    exact actual_finite_GG_bound _ hf _ (rpow_pos_of_pos hn _) _ v (hv _) D head hD
  · simp

theorem source_good_polynomial_GG {n : ℕ} (α : ℝ) (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀z,|f z| ≤ C)
    (v : ℕ → (ℕ → ℝ)) (hv : ∀ᶠN in atTop,v N∈sourceGoodParameters α f N)
    (j : ℕ) (D : (N : ℕ) → (Fin n → Spins N) → ℝ) (head : Fin n)
    {K : ℝ} (hD : ∀N x,|D N x| ≤ K) :
    Tendsto (fun N => sourcePolynomialGGResidual α f j N (v N) (D N) head) atTop (𝓝 0) := by
  have he := (source_good_parameters α hα hf hC).2.2 v hv j
  have hb : Tendsto (fun N => (K/(1/2)^(j+1))*sourceDeviation α f j N (v N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul he
  apply squeeze_zero_norm' _ hb
  filter_upwards [hv] with N hv
  simpa only [Real.norm_eq_abs] using sourcePolynomialGGResidual_bound α hf j N (v N)
    (fun k => (hv.1 k).1) (D N) head (hD N)

end IsingPerceptron.Main

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

def spinBoolEquiv (N : ℕ) : Spin N ≃ Main.Spins N :=
  Equiv.piCongrRight (fun _ => finTwoEquiv)

lemma spinBoolEquiv_value {N : ℕ} (x : Spin N) (i : Fin N) :
    Main.spin (spinBoolEquiv N x) i = spinValue (x i) := by
  change (if finTwoEquiv (x i) then (1 : ℝ) else -1) =
    (if x i = 0 then -1 else 1)
  generalize x i = b
  fin_cases b <;> norm_num [finTwoEquiv]

def disorderCurry (α : ℝ) (N : ℕ) :
    Patterns (patternCount α N) N ≃ᵐ Main.Disorder α N :=
  MeasurableEquiv.curry _ _ ℝ

lemma disorderCurry_preserving (α : ℝ) (N : ℕ) :
    MeasurePreserving (disorderCurry α N)
      (gaussianPatterns (patternCount α N) N) (Main.disorderLaw α N) := by
  refine ⟨(disorderCurry α N).measurable, ?_⟩
  have he := Measure.infinitePi_map_curry
    (fun (_ : Fin (patternCount α N)) (_ : Fin N) => gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

lemma patternEvaluation_equivalent (α : ℝ) (N : ℕ)
    (g : Patterns (patternCount α N) N) (a : Fin (patternCount α N)) (x : Spin N) :
    Main.patternEvaluation (disorderCurry α N g) a (spinBoolEquiv N x) =
      projection g a x := by
  simp only [Main.patternEvaluation, projection, spinBoolEquiv_value]
  rfl

lemma pressure_equivalent (α : ℝ) (f : ℝ → ℝ) (N : ℕ)
    (g : Patterns (patternCount α N) N) :
    Main.pressure α f N (disorderCurry α N g) = pressure α f N g := by
  have hs := (spinBoolEquiv N).sum_comp
    (fun x => Real.exp (∑ a, f (Main.patternEvaluation (disorderCurry α N g) a x)))
  change (∑ x : Spin N,
    Real.exp (∑ a : Fin (patternCount α N),
      f (Main.patternEvaluation (disorderCurry α N g) a (spinBoolEquiv N x)))) = _ at hs
  simp_rw [patternEvaluation_equivalent] at hs
  simp only [Main.pressure, Main.partitionFunction, pressure, partitionFunction, hs]

lemma meanPressure_equivalent (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (N : ℕ) :
    Main.meanPressure α f N = expectedPressure α f N := by
  have h := integral_comp_preserving_ae (disorderCurry_preserving α N)
    (Main.pressure_measurable α hf N).aestronglyMeasurable
  simpa only [pressure_equivalent, Main.meanPressure, expectedPressure] using h.symm

lemma pressure_variance_equivalent (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (N : ℕ) :
    variance (Main.pressure α f N) (Main.disorderLaw α N) =
      variance (pressure α f N) (gaussianPatterns (patternCount α N) N) := by
  have h := variance_map (μ := gaussianPatterns (patternCount α N) N)
    (X := Main.pressure α f N) (Y := disorderCurry α N)
    (Main.pressure_measurable α hf N).aemeasurable
    (disorderCurry α N).measurable.aemeasurable
  simpa only [(disorderCurry_preserving α N).map_eq, Function.comp_def,
    pressure_equivalent] using h

theorem pressure_variance_bound (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (N : ℕ) :
    variance (pressure α f N) (gaussianPatterns (patternCount α N) N) ≤
      (patternCount α N : ℝ) * (2 * C / N) ^ 2 := by
  rw [← pressure_variance_equivalent α hf]
  exact Main.pressure_variance_bound α hf hC N

lemma pressure_tail_equivalent (α : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (N : ℕ) (ε p : ℝ) :
    gaussianPatterns (patternCount α N) N {g | ε < |pressure α f N g - p|} =
      Main.disorderLaw α N {g | ε < |Main.pressure α f N g - p|} := by
  have hs : MeasurableSet {g | ε < |Main.pressure α f N g - p|} :=
    measurableSet_lt measurable_const ((Main.pressure_measurable α hf N).sub_const p).abs
  simpa only [Set.preimage_ofPred_eq, pressure_equivalent] using
    (disorderCurry_preserving α N).measure_preimage hs.nullMeasurableSet

theorem pressure_tail_bound (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    gaussianPatterns (patternCount α N) N
      {g | ε < |pressure α f N g - expectedPressure α f N|} ≤
      ENNReal.ofReal ((4 * α * C ^ 2 / ε ^ 2) / N) := by
  rw [pressure_tail_equivalent α hf, ← meanPressure_equivalent α hf]
  exact Main.pressure_tail_bound α hα hf hC hN hε

theorem pressure_centered_concentration (α : ℝ) (hα : 0 ≤ α) {f : ℝ → ℝ}
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => gaussianPatterns (patternCount α N) N
      {g | ε < |pressure α f N g - expectedPressure α f N|}) atTop (𝓝 0) := by
  simpa only [pressure_tail_equivalent α hf, ← meanPressure_equivalent α hf] using
    (Main.pressure_centered_concentration α hα hf hbounded hε)

def PressureConvergesInProbability (α : ℝ) (f : ℝ → ℝ) (p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N => gaussianPatterns (patternCount α N) N
      {g | ε < |pressure α f N g - p|}) atTop (𝓝 0)

theorem pressure_probability_of_expected_limit (α : ℝ) (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    {p : ℝ} (hp : Tendsto (expectedPressure α f) atTop (𝓝 p)) :
    PressureConvergesInProbability α f p := by
  intro ε hε
  have hmean : Tendsto (fun N => |expectedPressure α f N - p|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hp.sub (tendsto_const_nhds (x := p))).abs
  have hhalf : 0 < ε / 2 := half_pos hε
  have hm := (tendsto_order.1 hmean).2 (ε / 2) hhalf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (pressure_centered_concentration α hα hf hbounded hhalf)
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hm] with N hN
    apply measure_mono
    intro g hg
    have ht := abs_sub_le (pressure α f N g) (expectedPressure α f N) p
    change ε < |pressure α f N g - p| at hg
    change ε / 2 < |pressure α f N g - expectedPressure α f N|
    linarith

lemma bounded_continuous_activation (β : ℝ) (hβ : 0 < β) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hbounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    Measurable (fun x => β * φ x) ∧
      (∃ C : ℝ, ∀ x, |β * φ x| ≤ C) := by
  refine ⟨measurable_const.mul hφ.measurable, ?_⟩
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨β * C, fun x => ?_⟩
  rw [abs_mul, abs_of_pos hβ]
  exact mul_le_mul_of_nonneg_left (hC x) hβ.le

end IsingPerceptron

end

end OAI
