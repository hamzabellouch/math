import OAI.Dynamics.SmoothObstruction.StationaryGauge
import OAI.Dynamics.SmoothObstruction.ShearGauge

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
variable {d : ℕ}

lemma norm_le_sum_coordinates (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

/-- Entry bounds produce Euclidean operator bounds. The dimension factor is
paid only at endpoints, never once per step. -/
lemma opNorm_le_entry (A : Matrix (Fin d) (Fin d) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) : ‖A‖ ≤ (d : ℝ)^2 * B := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  refine (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) A).opNorm_le_bound (mul_nonneg (sq_nonneg _) hB) ?_
  intro x
  calc
    _ ≤ ∑ i, ‖(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) A x) i‖ := norm_le_sum_coordinates _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, B*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(A *ᵥ x) i‖ ≤ _
      rw [Matrix.mulVec, dotProduct]
      calc
        _ ≤ ∑ j, ‖A i j*x j‖ := norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul,Real.norm_eq_abs]
          exact mul_le_mul (hA i j) (PiLp.norm_apply_le x j) (norm_nonneg _) hB
    _ = _ := by simp; ring

lemma opNorm_le_exp (A : Matrix (Fin d) (Fin d) ℝ) {C E : ℝ}
    (hE : 1 ≤ E) (hA : ∀ i j, |A i j| ≤ Real.exp (C*E)) :
    ‖A‖ ≤ Real.exp ((C+(d:ℝ)^2)*E) := by
  have hd : (d:ℝ)^2 ≤ Real.exp ((d:ℝ)^2*E) := by
    calc
      _ ≤ Real.exp ((d:ℝ)^2) := by linarith [Real.add_one_le_exp ((d:ℝ)^2)]
      _ ≤ _ := Real.exp_le_exp.mpr (le_mul_of_one_le_right (sq_nonneg _) hE)
  calc
    _ ≤ (d:ℝ)^2*Real.exp (C*E) := opNorm_le_entry A (Real.exp_nonneg _) hA
    _ ≤ Real.exp ((d:ℝ)^2*E)*Real.exp (C*E) :=
      mul_le_mul_of_nonneg_right hd (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

noncomputable def rate (lam : Fin d → ℝ) (l : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun j => Real.exp (l*lam j))

noncomputable def mask (S : Finset (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun j => if j ∈ S then 1 else 0)

@[simp] lemma rate_zero (lam : Fin d → ℝ) : rate lam 0=1 := by
  simp [rate]
lemma rate_add (lam : Fin d → ℝ) (a b : ℝ) :
    rate lam (a+b)=rate lam a*rate lam b := by
  rw [rate,rate,rate,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [add_mul,Real.exp_add]
lemma rate_mask_comm (lam : Fin d → ℝ) (l : ℝ) (S : Finset (Fin d)) :
    rate lam l*mask S=mask S*rate lam l := by
  simp only [rate,mask,Matrix.diagonal_mul_diagonal]; congr 1; funext i; ring
@[simp] lemma mask_sq (S : Finset (Fin d)) : mask S*mask S=mask S := by
  simp only [mask,Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split <;> simp
lemma mask_compl_add (S : Finset (Fin d)) : mask S+mask Sᶜ=1 := by
  rw [mask,mask,Matrix.diagonal_add]
  convert Matrix.diagonal_one (n:=Fin d) using 1
  congr 1; funext i; simp; split <;> norm_num
lemma mask_compl_mul (S : Finset (Fin d)) : mask S*mask Sᶜ=0 := by
  rw [mask,mask,Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_zero using 1
  congr 1; funext i; simp
lemma norm_mask (S : Finset (Fin d)) : ‖mask S‖ ≤ 1 := by
  rw [mask,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i; split <;> norm_num

/-- Gauge-coordinate fundamental matrix; both time directions are encoded. -/
noncomputable def transition (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (s t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  U t * rate lam ((t:ℝ)-s) * V s
noncomputable def projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (S : Finset (Fin d)) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  U t*mask S*V t

lemma transition_self (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (s : ℕ) : transition U V lam s s=1 := by
  simp [transition,hUV]
lemma transition_comp (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hVU : ∀ t, V t*U t=1) (s t u : ℕ) :
    transition U V lam t u*transition U V lam s t=transition U V lam s u := by
  simp only [transition]
  calc
    _ = U u*(rate lam ((u:ℝ)-t)*(V t*U t)*rate lam ((t:ℝ)-s))*V s := by noncomm_ring
    _ = _ := by rw [hVU,mul_one,←rate_add]; congr 3; ring
lemma transition_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hVU : ∀ t, V t*U t=1) (S : Finset (Fin d)) (s t : ℕ) :
    transition U V lam s t*projection U V S s=projection U V S t*transition U V lam s t := by
  dsimp [transition,projection]
  calc
    _ = U t*(rate lam ((t:ℝ)-s)*(V s*U s)*mask S)*V s := by noncomm_ring
    _ = U t*(mask S*rate lam ((t:ℝ)-s))*V s := by rw [hVU,mul_one,rate_mask_comm]
    _ = _ := by
      symm
      calc
        _ = U t*(mask S*(V t*U t)*rate lam ((t:ℝ)-s))*V s := by noncomm_ring
        _ = _ := by rw [hVU,mul_one]
lemma projection_idem (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hVU : ∀ t, V t*U t=1) (S : Finset (Fin d)) (t : ℕ) :
    projection U V S t*projection U V S t=projection U V S t := by
  dsimp [projection]
  calc
    _ = U t*(mask S*(V t*U t)*mask S)*V t := by noncomm_ring
    _ = _ := by rw [hVU,mul_one,mask_sq]
lemma projection_compl (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t, U t*V t=1) (S : Finset (Fin d)) (t : ℕ) :
    projection U V S t+projection U V Sᶜ t=1 := by
  dsimp [projection]
  rw [←add_mul,←mul_add,mask_compl_add,mul_one,hUV]
lemma norm_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    {K : ℝ} (S : Finset (Fin d)) (t : ℕ)
    (hU : ‖U t‖ ≤ Real.exp K) (hV : ‖V t‖ ≤ Real.exp K) :
    ‖projection U V S t‖ ≤ Real.exp (2*K) := by
  calc
    _ ≤ ‖U t‖ * ‖mask S‖ * ‖V t‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp K * 1 * Real.exp K := by gcongr; exact norm_mask S
    _ = _ := by rw [mul_one,←Real.exp_add]; congr 1; ring

lemma norm_rate_mask {lam : Fin d → ℝ} {l c : ℝ} (hl : 0 ≤ l)
    (S : Finset (Fin d)) (hc : ∀ j ∈ S, lam j ≤ c) :
    ‖rate lam l*mask S‖ ≤ Real.exp (c*l) := by
  simp only [rate,mask,Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
  intro i
  by_cases hi : i ∈ S
  · simp only [hi,ite_true,mul_one,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [hc i hi]
  · simp only [hi,ite_false,mul_zero,norm_zero]; exact Real.exp_nonneg _

/-- Subinterval propagation on a selected group. The only conditioning
loss is at the two endpoints. -/
lemma norm_transition_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hVU : ∀ t, V t*U t=1) (lam : Fin d → ℝ) {K c : ℝ}
    (S : Finset (Fin d)) (s t : ℕ) (hst : s ≤ t)
    (hU : ‖U t‖ ≤ Real.exp K) (hV : ‖V s‖ ≤ Real.exp K)
    (hc : ∀ j ∈ S, lam j ≤ c) :
    ‖transition U V lam s t*projection U V S s‖ ≤
      Real.exp (c*((t:ℝ)-s)+2*K) := by
  have hr : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr (by exact_mod_cast hst)
  have heq : transition U V lam s t*projection U V S s =
      U t*(rate lam ((t:ℝ)-s)*mask S)*V s := by
    dsimp [transition,projection]
    calc
      _ = U t*(rate lam ((t:ℝ)-s)*(V s*U s)*mask S)*V s := by noncomm_ring
      _ = _ := by rw [hVU,mul_one]
  rw [heq]
  calc
    _ ≤ ‖U t‖ * ‖rate lam ((t:ℝ)-s)*mask S‖ * ‖V s‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp K * Real.exp (c*((t:ℝ)-s)) * Real.exp K := by
      gcongr; exact norm_rate_mask hr S hc
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

/-- Conversion of the constructed finite triangular gauge to genuine
Euclidean operator bounds. The constant is independent of the interval. -/
theorem exists_operator_gauge (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (E : ℝ) (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
      (lam : Fin d → ℝ), 1 ≤ E → Real.log (N+1) ≤ E →
      (∀ t < N, (A t).IsUpperTriangular) →
      (∀ t < N, ∀ j, 0 < A t j j) →
      (∀ t < N, ∀ i j, |A t i j| ≤ Real.exp R) →
      (∀ j, |lam j| ≤ R) →
      (∀ t ≤ N, ∀ j, |NormalizedGauge.error A lam t j| ≤ E) →
      ∃ U V : ℕ → Matrix (Fin d) (Fin d) ℝ,
        (∀ t, U t*V t=1 ∧ V t*U t=1) ∧
        (∀ t ≤ N, ‖U t‖ ≤ Real.exp (C*E)) ∧
        (∀ t ≤ N, ‖V t‖ ≤ Real.exp (C*E)) ∧
        (∀ t < N, A t*U t=U (t+1)*rate lam 1) := by
  obtain ⟨C,hC,h⟩ := NormalizedGauge.exists_exponential_gauge d R hR
  refine ⟨C+(d:ℝ)^2,add_nonneg hC (sq_nonneg _),?_⟩
  intro N E A lam hE hlog htri hpos hA hlam he
  obtain ⟨U,V,hUV,hU,hV,hEq⟩ := h N E A lam hE hlog htri hpos hA hlam he
  refine ⟨U,V,hUV,fun t ht => opNorm_le_exp _ hE (hU t ht),
    fun t ht => opNorm_le_exp _ hE (hV t ht),?_⟩
  intro t ht
  simpa only [rate,one_mul] using hEq t ht

/-- Actual later-on-the-left product used in the manuscript. -/
def propagator (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (s : ℕ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | n+1 => A (s+n)*propagator A s n

lemma transition_one_step (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (t : ℕ)
    (hA : A t*U t=U (t+1)*rate lam 1) :
    A t=transition U V lam t (t+1) := by
  have ht : ((t+1:ℕ):ℝ)-t=1 := by push_cast; ring
  dsimp [transition]
  rw [ht]
  calc
    _ = (A t*U t)*V t := by rw [mul_assoc,hUV,mul_one]
    _ = _ := by rw [hA]

lemma propagator_eq_transition (A U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (lam : Fin d → ℝ) (hUV : ∀ t, U t*V t=1) (hVU : ∀ t, V t*U t=1)
    (N : ℕ) (hA : ∀ t < N, A t*U t=U (t+1)*rate lam 1)
    (s l : ℕ) (hl : s+l ≤ N) :
    propagator A s l=transition U V lam s (s+l) := by
  induction l with
  | zero => simpa only [Nat.add_zero,propagator] using (transition_self U V lam hUV s).symm
  | succ l ih =>
    rw [propagator,ih (by omega),transition_one_step A U V lam hUV (s+l) (hA _ (by omega)),
      transition_comp U V lam hVU]
    rfl

lemma norm_rate_mask_lower {lam : Fin d → ℝ} {l c : ℝ} (hl : l ≤ 0)
    (S : Finset (Fin d)) (hc : ∀ j ∈ S, c ≤ lam j) :
    ‖rate lam l*mask S‖ ≤ Real.exp (c*l) := by
  simp only [rate,mask,Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
  intro i
  by_cases hi : i ∈ S
  · simp only [hi,ite_true,mul_one,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [hc i hi]
  · simp only [hi,ite_false,mul_zero,norm_zero]; exact Real.exp_nonneg _

lemma norm_backward_projection (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hVU : ∀ t, V t*U t=1) (lam : Fin d → ℝ) {K c : ℝ}
    (S : Finset (Fin d)) (s t : ℕ) (hst : s ≤ t)
    (hU : ‖U s‖ ≤ Real.exp K) (hV : ‖V t‖ ≤ Real.exp K)
    (hc : ∀ j ∈ S, c ≤ lam j) :
    ‖transition U V lam t s*projection U V S t‖ ≤
      Real.exp (-c*((t:ℝ)-s)+2*K) := by
  have hr : (s:ℝ)-t ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hst)
  have heq : transition U V lam t s*projection U V S t =
      U s*(rate lam ((s:ℝ)-t)*mask S)*V t := by
    dsimp [transition,projection]
    calc
      _ = U s*(rate lam ((s:ℝ)-t)*(V t*U t)*mask S)*V t := by noncomm_ring
      _ = _ := by rw [hVU,mul_one]
  rw [heq]
  calc
    _ ≤ ‖U s‖ * ‖rate lam ((s:ℝ)-t)*mask S‖ * ‖V t‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp K * Real.exp (c*((s:ℝ)-t)) * Real.exp K := by
      gcongr; exact norm_rate_mask_lower hr S hc
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.QR
open Matrix
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

noncomputable def frameMatrix (e : Frame d) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (basis e).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def frameInverse (e : Frame d) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (basis e).repr.toContinuousLinearEquiv.toContinuousLinearMap

lemma frameMatrix_inverse (e : Frame d) : frameMatrix e*frameInverse e=1 ∧ frameInverse e*frameMatrix e=1 := by
  constructor <;> apply EquivLike.injective (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)) <;>
    simp only [map_mul,map_one,frameMatrix,frameInverse,StarAlgEquiv.apply_symm_apply]
  · apply ContinuousLinearMap.ext
    intro x
    exact (basis e).repr.symm_apply_apply x
  · apply ContinuousLinearMap.ext
    intro x
    exact (basis e).repr.apply_symm_apply x

lemma norm_frameMatrix (e : Frame d) : ‖frameMatrix e‖≤1 := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM,frameMatrix,StarAlgEquiv.apply_symm_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map,one_mul,le_refl]

lemma norm_frameInverse (e : Frame d) : ‖frameInverse e‖≤1 := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM,frameInverse,StarAlgEquiv.apply_symm_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.norm_map,one_mul,le_refl]

lemma triangular_bound (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) (i j : Fin d) : |triangular A e i j|≤‖A.toContinuousLinearMap‖ := by
  have h := norm_inner_le_norm (𝕜:=ℝ) ((step A e).val i) (A (e.val j))
  rw [(step A e).property.norm_eq_one,one_mul] at h
  apply h.trans
  change ‖A.toContinuousLinearMap (e.val j)‖≤‖A.toContinuousLinearMap‖
  simpa only [e.property.norm_eq_one,mul_one] using A.toContinuousLinearMap.le_opNorm (e.val j)

lemma matrix_qr (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : Frame d) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm A.toContinuousLinearMap*frameMatrix e=
      frameMatrix (step A e)*triangular A e := by
  apply EquivLike.injective (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ))
  simp only [map_mul,StarAlgEquiv.apply_symm_apply,frameMatrix]
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro j
  change A ((basis e).repr.symm (EuclideanSpace.basisFun (Fin d) ℝ j))=
    (basis (step A e)).repr.symm (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (triangular A e) (EuclideanSpace.basisFun (Fin d) ℝ j))
  have hcol : Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (triangular A e) (EuclideanSpace.basisFun (Fin d) ℝ j)=
      (basis (step A e)).repr (A (e.val j)) := by
    ext i
    simp only [Matrix.ofLp_toEuclideanCLM,EuclideanSpace.basisFun_apply,PiLp.ofLp_single,
      Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply,
      OrthonormalBasis.repr_apply_apply,basis_apply,triangular]
  rw [hcol,LinearIsometryEquiv.symm_apply_apply]
  congr 1
  apply (basis e).repr.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  simpa only [basis_apply,EuclideanSpace.basisFun_apply] using ((basis e).repr_self j).symm

/-- The actual QR frame change transfers a triangular finite gauge to the
original derivative matrices, at no loss in operator norm. -/
theorem transfer_gauge
    (A : ℕ → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : ℕ → Frame d) (he : ∀ t,e (t+1)=step (A t) (e t))
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (N : ℕ) (K : ℝ)
    (hUV : ∀ t,U t*V t=1 ∧ V t*U t=1)
    (hU : ∀ t≤N,‖U t‖≤Real.exp K) (hV : ∀ t≤N,‖V t‖≤Real.exp K)
    (hEq : ∀ t<N,triangular (A t) (e t)*U t=U (t+1)*EuclideanSplitting.rate lam 1) :
    ∃ P Q : ℕ → Matrix (Fin d) (Fin d) ℝ,
      (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
      (∀ t≤N,‖P t‖≤Real.exp K) ∧ (∀ t≤N,‖Q t‖≤Real.exp K) ∧
      (∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm (A t).toContinuousLinearMap*P t=
        P (t+1)*EuclideanSplitting.rate lam 1) := by
  let P := fun t => frameMatrix (e t)*U t
  let Q := fun t => V t*frameInverse (e t)
  refine ⟨P,Q,fun t => ?_,fun t ht => ?_,fun t ht => ?_,fun t ht => ?_⟩
  · constructor
    · dsimp [P,Q]
      calc
        _=frameMatrix (e t)*(U t*V t)*frameInverse (e t) := by noncomm_ring
        _=1 := by rw [(hUV t).1,mul_one,(frameMatrix_inverse _).1]
    · dsimp [P,Q]
      calc
        _=V t*(frameInverse (e t)*frameMatrix (e t))*U t := by noncomm_ring
        _=1 := by rw [(frameMatrix_inverse _).2,mul_one,(hUV t).2]
  · exact (norm_mul_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul (norm_frameMatrix _) (hU t ht) (norm_nonneg _) zero_le_one)
  · exact (norm_mul_le _ _).trans (by
      simpa only [mul_one] using mul_le_mul (hV t ht) (norm_frameInverse _) (norm_nonneg _) (Real.exp_nonneg _))
  · dsimp [P]
    rw [←mul_assoc,matrix_qr,mul_assoc,hEq t ht,←mul_assoc,he t]
end SmoothObstruction.QR

namespace SmoothObstruction.QR
open MeasureTheory Filter Topology Finset
open scoped Matrix.Norms.L2Operator
variable {d : ℕ} {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Compactness bounds both the actual derivative and every positive QR
log-diagonal. The frame is arbitrary, so no measurable choice is hidden. -/
lemma exists_uniform_qr_bound
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x).toContinuousLinearMap)) :
    ∃ R : ℝ, 0≤R ∧ (∀ x,‖(A x).toContinuousLinearMap‖≤Real.exp R) ∧
      ∀ (x : X) (e : Frame d) j, |Real.log (triangular (A x) e j j)|≤R := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hb : ∀ j : Fin d,∃ B : ℝ,∀ z : X × Frame d,
      |Real.log (triangular (A z.1) z.2 j j)|≤B := by
    intro j
    obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_log_diagonal A hA j).continuousOn
    exact ⟨B,fun z => hB z (Set.mem_univ _)⟩
  choose B hB using hb
  let R := |C|+∑ j,|B j|+1
  have hR : 0≤R := by dsimp [R]; positivity
  have hCR : C≤R := by
    have hs : 0≤∑ j,|B j| := sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [R]; linarith [le_abs_self C]
  refine ⟨R,hR,fun x => (hC x (Set.mem_univ _)).trans (hCR.trans ?_),?_⟩
  · linarith [Real.add_one_le_exp R]
  · intro x e j
    have hj := single_le_sum (f:=fun j : Fin d => |B j|) (fun _ _ => abs_nonneg _) (mem_univ j)
    have hh := (hB j (x,e)).trans (le_abs_self (B j))
    dsimp [R]
    linarith [abs_nonneg C]

omit [MetricSpace X] [CompactSpace X] in
lemma skew_iterate_fst (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (z : X × Frame d) (t : ℕ) : ((skew T A)^[t] z).1=T^[t] z.1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Function.iterate_succ_apply',skew,ih]

omit [MetricSpace X] [CompactSpace X] in
lemma log_error_is_chord (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (z : X × Frame d) (N t : ℕ) (j : Fin d) :
    NormalizedGauge.error
      (fun a => triangular (A ((skew T A)^[a] z).1) ((skew T A)^[a] z).2)
      (fun i => DyadicChord.average
        (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 i i)) z) N) t j=
    DyadicChord.chord
      (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 j j)) z) N t := by
  simp only [NormalizedGauge.error,DyadicChord.chord,DyadicChord.prefixSum,
    DyadicChord.orbit,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]

lemma average_abs_le {f : ℕ → ℝ} {R : ℝ} {N : ℕ} (hN : 0<N)
    (hf : ∀ t<N,|f t|≤R) : |DyadicChord.average f N|≤R := by
  rw [DyadicChord.average,abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  calc
    |DyadicChord.prefixSum f N|≤∑ t∈range N,|f t| := by
      exact abs_sum_le_sum_abs _ _
    _≤∑ t∈range N,R := sum_le_sum (fun t ht => hf t (mem_range.mp ht))
    _=R*N := by simp only [sum_const,card_range,nsmul_eq_mul]; ring

/-- Finite gauges for genuine good QR orbit segments. Positivity and
triangularity come from the actual Gram--Schmidt process, and the chord
errors are identified with the stationary quantities, not assumed anew. -/
theorem compact_good_gauge (T : X → X)
    (A : X → EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hA : Continuous (fun x => (A x).toContinuousLinearMap)) :
    ∃ R C : ℝ,0≤R ∧ 0≤C ∧ ∀ k b (z : X × Frame d),
      z∈GoodStationary.Good (skew T A)
        (fun j w => Real.log (triangular (A w.1) w.2 j j)) k b →
      1≤b*(2:ℝ)^k → Real.log ((2^(k+1):ℕ)+1)≤b*(2:ℝ)^k →
      ∃ (lam : Fin d → ℝ) (P Q : ℕ → Matrix (Fin d) (Fin d) ℝ),
        (∀ j,|lam j|≤R) ∧ (∀ t,P t*Q t=1 ∧ Q t*P t=1) ∧
        (∀ t≤2^(k+1),‖P t‖≤Real.exp (C*(b*2^k))) ∧
        (∀ t≤2^(k+1),‖Q t‖≤Real.exp (C*(b*2^k))) ∧
        (∀ t<2^(k+1),
          (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
            (A (T^[t] z.1)).toContinuousLinearMap*P t=
            P (t+1)*EuclideanSplitting.rate lam 1) := by
  obtain ⟨R,hR,hAR,hlogR⟩ := exists_uniform_qr_bound A hA
  obtain ⟨C,hC,hg⟩ := EuclideanSplitting.exists_operator_gauge d R hR
  refine ⟨R,C,hR,hC,?_⟩
  intro k b z hz hb hn
  let w := fun t => (skew T A)^[t] z
  let L := fun t => A (w t).1
  let e := fun t => (w t).2
  let B := fun t => triangular (L t) (e t)
  let lam := fun j => DyadicChord.average
    (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 j j)) z) (2^(k+1))
  have hlam : ∀ j,|lam j|≤R := by
    intro j
    exact average_abs_le (pow_pos (by omega : 0<2) _) (fun t _ => hlogR _ _ j)
  have he : ∀ t,e (t+1)=step (L t) (e t) := by
    intro t
    simp only [e,L,w,Function.iterate_succ_apply',skew]
  have herr : ∀ t≤2^(k+1),∀ j,|NormalizedGauge.error B lam t j|≤b*2^k := by
    intro t ht j
    rw [show NormalizedGauge.error B lam t j=
      DyadicChord.chord
        (DyadicChord.orbit (skew T A) (fun w => Real.log (triangular (A w.1) w.2 j j)) z)
        (2^(k+1)) t from log_error_is_chord T A z _ _ _]
    exact hz j t ht
  obtain ⟨U,V,hUV,hU,hV,hEq⟩ := hg (2^(k+1)) (b*2^k) B lam hb hn
    (fun t _ => triangular_upper _ _) (fun t _ => diagonal_pos _ _)
    (fun t _ i j => (triangular_bound _ _ i j).trans (hAR _)) hlam herr
  obtain ⟨P,Q,hPQ,hP,hQ,hStep⟩ := transfer_gauge L e he U V lam (2^(k+1)) (C*(b*2^k))
    hUV hU hV hEq
  refine ⟨lam,P,Q,hlam,hPQ,hP,hQ,?_⟩
  intro t ht
  simpa only [L,w,skew_iterate_fst] using hStep t ht
end SmoothObstruction.QR

end

end OAI
